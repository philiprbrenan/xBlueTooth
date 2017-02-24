#!/usr/bin/perl
=pod

Transform a BlueTooth Word document saved in .fodt format to Dita

  Philip R Brenan at gmail dot com, 2017

=cut

use warnings FATAL => qw(all);
use strict;
use Carp;
use Data::Dump qw(dump);
use Data::Edit::Xml;
use Data::Table::Text qw(:all);
use File::Basename;
use Storable;
use Time::HiRes;
use utf8;

# Directories
my $home                = "/home/phil/bt/";                                     # Home directory for this project
my $in                  = $home."in/";                                          # Input directory
my $perl                = $home."perl/";                                        # Perl directory
my $entities            = $home."entities/";                                    # Entities directory
my $tmp                 = $home."tmp/";                                         # Temp directory
my $dtd                 = $home."dtd/";                                         # Dtd directory
my $dtdCatalog          = $dtd."catalog.xml";                                   # DTD catalog
my $out                 = $home."out/";                                         # Transformed output
my $outDita             = $out."dita/";                                         # Generated dita files
my $outImages           = $out."images/";                                       # Flattened output file name space = original outout space minus project folders
my $outErrors           = $out."errors/";                                       # Error messages
my $reportDir           = $out."reports/";                                      # Directory for combined report
my $zipPath             = "$home/zip";                                          # Work folder for zip files

# Settings
my $version             = "2017.02.18 19:08:11";                                # Version for reports

# Reports
my %lintResults;                                                                # Files that passed or failed lint

sub countTagsByType($$)                                                         # Count the tags by tag type
 {my ($x, $folder) = @_;                                                        # Input specification, output sub folder name to contain results
  my $fileName = $x->file;
  my %tags;
  $x->parse->by(sub {my ($o) = @_; $tags{$o->tag}++});
  my $f = $reportDir."tagCounts/$folder/$fileName.data";
  writeFile($f, formatTable(\%tags));
 }

sub Data::Edit::Xml::cutOut($)      :lvalue {$_[0]{cutOut}}                     # Mark a section in the parse tree to be formatted and written out
sub Data::Edit::Xml::transformed($) :lvalue {$_[0]{transformed}}                # Mark a section as already having been transformed

sub unwrapHeadersFromList($)                                                    # The section headers are wrapped in list elements to get section numbering. Dita obviates this so unwrap these entries:
 {my ($x) = @_;                                                                 # Input specification
  say STDERR "Unwrapping headers from header list";

  if (1)                                                                        # Unwrap lists of headers
   {my %unwrap;                                                                 # Headers to unwrap

    $x->parse->by(sub
     {my ($o) = @_;
      if ($o->at(qw(section)))
       {for my $element(@_)
         {next unless $element->at(qw(text:list-item)) ||
                      $element->at(qw(text:list));
          $unwrap{"$element"} = $element;
         }
        $o->wrapContentWith(qw(title));                                         # Preserve the content of the header in a title tag
        $o->change(qw(section));                                                # Change the tag to section to show it has been processed
        $o->cutOut = 1;                                                         # Mark this section for cutting out and formatting
       }
     });
    $_->unwrap for values %unwrap;                                              # Unwrap once the traverse has been completed to avoid changing the parse tree while trying to find the elements to unwrap
   }

  if (1)                                                                        # Attach each outer element to the last seen header
   {my @h;                                                                      # The current header stack
    for my $element($x->body->contents)
     {if ($element->at(qw(section)))
       {if (my $l = $element->attr(qw(text:outline-level)))
         {if ($l > @h + 1)                                                      # Going down more than one level
           {confess "Going down more than one level at: ".$element->string;
           }
          elsif ($l > 1)                                                        # Same level or lower but not outer layer
           {$#h = $l - 2;                                                       # Remove deeper levels completed by this header
            my $p = $h[-1];                                                     # Parent
            $p->putLast($element->cut);
            push @h, $element;                                                  # Add to stack
           }
          else                                                                  # Outermost level
           {@h = ($element);
           }
         }
        else
         {confess "No attr: text:outline-level on tag: test:h";
         }
       }
      elsif (@h) {$h[-1]->putLast($element->cut)}                               # Attach current element which is not a header the to last seen header if there is one
     };
   }
 }

my %uniqueTitles;
sub uniqueFileNameForSection($$)                                                # Create a unique file name for a section
 {my ($x, $section) = @_;                                                       # Input specification, section
  my $title = $section->get(qw(title));
  my $Title = $title->string =~ s /<.*?>//gsr =~ s/\W//gsr;
  my $s = $section->tag. "_". $Title;
  return $s unless $uniqueTitles{$s}++;
  for(1..100)
   {my $t = $s.$_;
    return $t unless $uniqueTitles{$t}++;
   }
  confess "Unable to create a unique file name from $title";
 }

sub filePath(@)                                                                 # Create a file name from components
 {my (@file) = @_;                                                              # File name components
  my $s = '';                                                                   # Construct path for file
  my $t = join '/', map {s/[\/\\]+\Z//r} @_;
  $t
 }

sub saveSection($$$)                                                            # Save a section referenced in a bookmap
 {my ($x, $p, $file) = @_;                                                      # Input specification, position in parse tree at which to cut out the section, output file name

  $p->by(sub                                                                    # Change remaining tags after conversion to improve chances of getting past xmllint
   {my ($o) = @_;
    my %c = (qw(text:list        ol),
             qw(text:list-item   li),
            );
    my $t = $o->tag;
    if (my $c = $c{$t}) {$o->change($c)}
   });

  my $f = filePath $outDita, $x->file, "$file.dita";
  XmlWrite::new()->lint($p, $f);
  $p->cut;                                                                      # Remove this section it does not show up inside other sections
 }

my $taskNumber;                                                                 # Give each task a unique number

sub formatTestSection($$)                                                       # Format a test section
 {my ($x, $s) = @_;                                                             # Input specification, section
  $s->change(qw(task));                                                         # Convert to task
  $s->id = "task".++$taskNumber;                                                # Give each task a unique number
  $s->cutOut = 2;                                                               # Mark this section for cutting out

  my %unwrap;                                                                   # Things to unwrap
  my $testProcedure;                                                            # Special sections
  my $expectedOutcome;
  my $passVerdict;
  $s->by(sub                                                                    # Create sections for the special paragraphs that are acting as section headers
   {my ($o, $p) = @_;
    if ($o->at(qw(CDATA)))
     {if (my $text = $o->text)
       {if ($text =~ /\A(Test\s+Purpose|Test Procedure|Reference|Initial\s+Condition|Expected\s+Outcome|Pass\s+Verdict)\Z/)
         {$p->change(qw(title));
          my $q = $p->wrapWith(qw(section));
          $q->transformed  = 1;                                                 # Show that this is a generated section and so does not need to be further transformed
          $testProcedure   = $q if $text =~ /procedure/i;                       # Special sections
          $expectedOutcome = $q if $text =~ /expected/i;
          $passVerdict     = $q if $text =~ /verdict/i;
          for(my $r = $q->parent; $r; $r = $r->parent)
           {last if $r->at(qw(task));
            $unwrap{"$r"} = $r;
           }
         }
       }
     }
   });
  $_->unwrap for values %unwrap;                                                # Unwrap once the traverse has been completed to avoid changing the parse tree while trying to find the elements to unwrap

  $s->by(sub                                                                    # Merge back into prior sections
   {my ($o) = @_;
    return if $o->at(qw(section));                                              # Except sections
    if (my $s = $o->prev)
     {if ($s->at(qw(section)))
       {$s->putLast($o->cut);
       }
     }
   });

  my $title = $s->get(qw(title));                                               # Wrap everything except the title in a task body
  $s->wrapContentWith(qw(taskbody));
  $s->putFirst($title->cut) if $title;

  if ($testProcedure)                                                           # Format the test procedure section as steps
   {my $numberOfLists;

    $testProcedure->by(sub
     {my ($o) = @_;
      if    ($o->at(qw(p text:list-item text:list))) {$o->change(qw(cmd))}
      elsif ($o->at(qw(  text:list-item text:list))) {$o->change(qw(step))}
      elsif ($o->at(qw(                 text:list))) {$o->change(qw(steps)); ++$numberOfLists}
     });

    if (!$numberOfLists)                                                        # Perhaps they formatted the procedure as a series if paragraphs
     {my $s = $testProcedure->wrapContentWith(qw(steps));
      my $p = $s->c(qw(p));
      my $q = pop @$p;                                                          # The last paragraph
      $_->change(qw(cmd))->wrapWith(qw(step)) for @$p;                          # The preceding paragraphs become commands
      $s->putNext($q->cut) if $q;                                               # The last paragraph becomes an example
      my $t = $s->get(qw(title));                                               # Remove the title before the steps
      $t->cut if $t;
      $q->wrapWith(qw(example));
     }

    else
     {$testProcedure->by(sub                                                    # Wrap paragraphs after steps with example
       {my ($o) = @_;
        if ($o->at(qw(p section)))
         {my $q = $o->wrapWith(qw(example));
         }
       });
      $testProcedure->byReverse(sub                                             # Convert examples that occurred before the steps into step/cmd
       {my ($o) = @_;
        if ($o->at(qw(example)))
         {if (my $n = $o->next)
           {if ($n->at(qw(steps)))
             {$n->putFirst($o->change(qw(step))->cut);
             }
           }
         }
       });
      $testProcedure->by(sub                                                    # Change p to cmd inside what was an example
       {my ($o) = @_;
        $o->change(qw(cmd)) if $o->at(qw(p step));
       });
     }

    $testProcedure->by(sub                                                      # Remove surrounding section
     {my ($o, $p) = @_;
      if ($o->at(qw(steps section)))
       {my $t = $p->get(qw(title));
        $t->cut if $t;                                                          # Remove title of removed section
        $p->unwrap;
       }
     });
   }

  if ($expectedOutcome and $passVerdict)                                        # Create post req by merging these sections
   {$expectedOutcome->change(qw(postreq));
    $expectedOutcome->putLast($passVerdict->cut);
    $passVerdict->unwrap;
    $expectedOutcome->by(sub                                                    # Convert titles to pb
     {my ($o) = @_;
      if ($o->at(qw(title)))
       {$o->change(qw(b));
        $o->wrapWith(qw(p))
       }
     });
   }

  $s->by(sub                                                                    # Change example-section to example-post-req and remove title of section
   {my ($o, $p) = @_;
    if ($o->at(qw(section)))
     {if (!$o->next)
       {if (my $p = $o->prev)
         {if ($p->at(qw(example)))
           {$o->change(qw(postreq));
            if (my $t = $o->get(qw(title)))                                     # Remove title
             {$t->cut;
             }
           }
         }
       }
     }
   });

  $s->by(sub                                                                    # Remove empty steps - we should investigate why they are empty
   {my ($o) = @_;
    if ($o->at(qw(steps)))
     {if (!$o->contents)
       {$o->cut;
       }
     }
   });

  my $debug = $s->id eq "task191";
  if ($debug)
   {say STDERR "AAAA ", $s->string =~ s/></>\n</gsr;
   }

  if (1)                                                                        # Improve tables
   {my $body;

    $s->by(sub                                                                  # Change table:table-header-rows to tgroup-thead
     {my ($o) = @_;
      if ($o->at(qw(table:table-header-rows)))
       {my $g = $o->change(qw(thead))->wrapWith(qw(tgroup));
        $body = $g->create(qw(tbody));
        $g->putLast($body);
say STDERR "BBBB" if $debug;
       }
say STDERR "CCCC body=", !!$body, "  ", $o->context if $debug;

      if ($body && $o->at(qw(row table)))
       {$body->putLast($o->cut);
       }
     });
   }

  if ($debug)
   {say STDERR "EEEE ", $s->string =~ s/></>\n</gsr;
   }
 }

sub transformTestSection($$)                                                    # Classify a test section
 {my ($x, $s) = @_;                                                             # Input specification, section
  my $subSections;
  $s->by(sub
   {my ($o) = @_;
    $subSections++ if $o->at(qw(section));
   });
  return 0 if $subSections > 1;                                                 # Found a section in the section so it cannot be a test section

  eval
   {$s->by(sub
     {my ($p) = @_;
      if ($p->at(qw(p)))
       {if (my $a = $p->attr(qw(text:style-name)))
         {if ($a eq "Test_20_case_20_Verdict")
           {formatTestSection($x, $s);                                          # Found a test section
            die "found";
           }
         }
       }
     });
   };
  return 1 if $@ and $@ =~ /\Afound/;
  $@
 }

my $conceptNumber;                                                              # Give each concept a unique number

sub formatConcept($$)                                                           # Transform a section into a concept
 {my ($x, $section) = @_;                                                       # Input specification, section
  my $subSections;
  $section->change(qw(concept));
  $section->id = "concept".++$conceptNumber;
  my $title = $section->get(qw(title));
  $section->wrapContentWith(qw(conbody));
  $section->putFirst($title->cut) if $title;
 }

sub transformSections($)                                                        # Transform each section into a topic of some type
 {my ($x) = @_;                                                                 # Input specification
  $x->parse->by(sub
   {my ($o) = @_;
    transformTestSection($x, $o) if $o->at(qw(section));
   });
  $x->parse->by(sub                                                             # Remaining sections become concepts
   {my ($o) = @_;
    formatConcept($x, $o) if $o->at(qw(section)) and !$o->transformed;
   });
 }

my @bookMapFileNames;                                                           # Stack of file names referenced in the bookmap
sub createBookMapEntry($$$$)                                                    # Create a bookmap entry
 {my ($x, $beforeNotAfter, $bookMap, $o) = @_;                                  # Input specification, before or after the tag, bookmap array, title, section
  if (my $n = $o->cutOut)
   {my $t = $o->get(qw(title));
#    my $n = $o->attr(qw(text:outline-level));
#    my $s = '  ' x $n;
    my $tag = $n == 1 ? qw(chapter) : qw(topicref);
    if ($beforeNotAfter)
     {my $f = uniqueFileNameForSection($x, $o);
      push @$bookMap, "<$tag href=\"$f.dita\">";
      push @bookMapFileNames, $f;                                               # Stack of file names referenced in the bookmap
     }
    else
     {push @$bookMap, "</$tag>";
      my $f = pop @bookMapFileNames;
      saveSection($x, $o, $f);
     }
   }
 }

sub createBookMap($)                                                            # Convert an input file that has been parsed
 {my ($x) = @_;                                                                 # Input specification
  my @bookMap;
  transformSections($x);
  $x->body->through
   (sub {my ($o, $p) = @_; createBookMapEntry($x, 1, \@bookMap, $o)},
    sub {my ($o, $p) = @_; createBookMapEntry($x, 0, \@bookMap, $o)},
   );

  if (1)                                                                        # Write bookmap
   {my $s = join "\n", @bookMap;
    my $b = Data::Edit::Xml::new(inputString=>
     '<bookmap>'.$s.'</bookmap>');

    $b->by(sub
     {my ($o) = @_;
      if ($o->at(qw(chapter chapter)))
       {$o->change(qw(topicref));
       }
     });

    my $f = filePath $outDita, $x->file, "bm.ditamap";
    XmlWrite::new()->lint($b, $f);
   }
 }

sub convertParsedFile($)                                                        # Convert an input file that has been parsed
 {my ($x) = @_;                                                                 # Input specification

  countTagsByType $x, "begin";                                                  # Count tags at start

  $x->body = $x->parse->get(qw(office:body office:text));                       # The single section that holds the actual text

  unwrapHeadersFromList($x);
  createBookMap($x);

  countTagsByType $x, "end";                                                    # Count tags at end

  XmlWrite::new()->format($x->parse, $reportDir.$x->file.".html", 1);           # Save the converted file as pretty printed html so we can see it in a browser or editor
 }

sub createInputSpecification($@)                                                # Specify where an xml file came from
 {my ($x, @inputFile) = @_;                                                     # Input file to convert
  XmlRead::new(file=>$inputFile[0] =~ s/\.\Z//r,                                # File parse leaves a trailing dot on the file name
               path=>$inputFile[1],
               ext =>$inputFile[2], parse=>$x);
 }

sub changeObviousTagsLikeP($)                                                   # Change obvious tags like P
 {my ($x) = @_;                                                                 # Parse
  say STDERR "Changing obvious tags";

  $x->by(sub
   {my ($o) = @_;
    my %c = (qw(text:h           section),                                      # Obvious tag transformations
             qw(text:p           p),
             qw(table:table      table),
             qw(table:table-row  row),
             qw(table:table-cell entry),
            );
    my $t = $o->tag;
    if (my $c = $c{$t}) {$o->change($c)}
    $o->deleteAttr(qw(office:value-type));                                      # Superfluous attributes
   });
 }

sub convertInputFile($)                                                         # Convert an input file
 {my ($inputFile) = @_;                                                         # Input file to convert
  say STDERR "convertInputFile inputFile=", dump($inputFile);

  $inputFile =~ /\.fodt\Z/i or
    confess "File $inputFile does not have an extension of .fodt";

  my @inputFile = fileparse($inputFile, qw(fodt));                              # Parse file name

  my $i = $inputFile =~ s/\.fodt\Z/.data/ri;                                    # Storable version of file

  my $x = -e $i ? retrieve($i) : undef;

  if (!$x)
   {say STDERR "Start parse and save of $inputFile";
    my $t = time();

    my $s = readFile($inputFile);
    my $S = $s =~ s(<office:binary-data>.*?<\/office:binary-data>)              # Removing the stored images reduces the file size from 250M to 2M, we need to actually save off the cut out sections and insert a reference to them
                   (<image\/>)gsr;
    my $l = length($s); my $ll = length($l);
    my $L = length($S); my $LL = length($L);
    say STDERR "Squashing binary-data o($ll) to o($LL) = $L";

    $x = Data::Edit::Xml::new(inputString=>$S);

    changeObviousTagsLikeP($x);                                                 # This takes some time

    store $x, $i;
    say STDERR "Parsed and saved in ", (time() - $t), " seconds";
   }

  convertParsedFile(createInputSpecification($x, @inputFile));
  $x                                                                            # Return parsed file contents
 }

# XmlRead methods to describe the source of some XML
sub XmlRead::new(@)
 {package XmlRead;
  return bless {@_};                                                            # Document parameters

  sub file  :lvalue {$_[0]->{file}}                                             # File name shorn of extension and path but with a trailing dot
  sub path  :lvalue {$_[0]->{path }}                                            # Path to file
  sub ext   :lvalue {$_[0]->{ext  }}                                            # Extension of file with no preceding dot
  sub parse :lvalue {$_[0]->{parse}}                                            # Parse tree
  sub body  :lvalue {$_[0]->{body }}                                            # Parse tree of the body of the source document
 }

# XmlWrite methods  to write out an xml document
sub XmlWrite::new
 {package XmlWrite;
  use Data::Table::Text qw(:all);
  return bless {catalog=>$dtdCatalog};                                          # Document catalog

  sub catalog  {$_[0]->{catalog}}                                               # Catalog to validate document against

  sub writeXmlWithHeaders($$$;$)                                                # Make xml usable by xmllint
   {my ($xmlDoc, $file, $x, $addStyles) = @_;                                   # Writer, file to write to, parse tree, whether to add styles or not

    if ($addStyles)                                                             # Add these styles to ameliorate raw word xml
     {my @styles = qw(text office field style svg table draw xlink form);       # Declare the command and attribute prefixes used in word
      for(@styles)
       {$x->setAttr("xmlns:$_", "http://www.w3.org/$_");
       }
     }
    else                                                                        # Unwrap these tags if they are still present - eventually they will be dealt with earlier on and so will no longer occur here
     {my %c = map {$_=>1}
      qw(text:span  text:bookmark-ref text:bookmark-start text:bookmark-end),   # From task
      qw(draw:frame draw:object-ole draw:image text:soft-page-break),
      qw(field:fieldmark-start field:fieldmark-end  text:sequence),             # From concept
      qw(text:bookmark text:line-break text:s text:tab),
      qw(table:table-column table:covered-table-cell);
      $x->by(sub
       {my ($o) = @_;
        my $t = $o->tag;
        unwrap $o if $c{$t};                                                    # Unwrap the above tags
        $o->change($t =~ s/:/_/gsr);                                            # Change remaining tags with : to _


        for(keys %{$o->attributes})                                             # Delete attributes with :
         {$o->deleteAttr($_) if m/:/;
         }
       });
     }

    my $n = $x->tag;                                                            # The outermost tag
    my $d = $n;
    my $N = ucfirst($n);
     ($n, $N) = ("generalTask", "General Task") if $n =~ /task/i;
     ($n, $N) = ("bookmap",     "BookMap")      if $n =~ /bookmap/i;

    my $s = $x->string;

    $s =~ s/\s&\s/ and /gs;                                                     # Annoying use of &

    $s =                                                                        # String that can be processed by xmllint
       "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n".
       "<!DOCTYPE $d PUBLIC \"-//OASIS//DTD DITA $N//EN\" \"$n.dtd\">\n".
       $s;

    writeFile($file, $s);                                                       # Save the xml to the specified file
   }

  sub format($$$;$)                                                             # Pretty print a parse tree
   {my ($xmlDoc, $x, $file, $addStyles) = @_;                                   # Document, parse tree, output file
    my $c = $xmlDoc->catalog;
    $xmlDoc->writeXmlWithHeaders($file, $x, $addStyles);
    my $l = "xmllint --format --output \"$file\"  \"$file\"";
    my $s = qx($l 2>&1);
    say STDERR "FFFFFFFFFFFFFFF Format\n$l\n$file\n$s\n" if $s;
   }

  sub lint($$$)                                                                 # Lint a parse tree
   {my ($xmlDoc, $x, $file) = @_;                                               # Document, parse tree, output file
    my $c = $xmlDoc->catalog;
    $xmlDoc->writeXmlWithHeaders($file, $x);
    my $e = "export XML_CATALOG_FILES='$c' && ";
    if  (1)                                                                     # Format the document first so that error message line numbers are meaningful
     {my $l = "xmllint --format --output \"$file\"  \"$file\"";
      my $s = qx($l 2>&1);
      if ($s)
       {say STDERR "LLLLLLLLLLLLLLL Format\n$l\n$file\n$s\n" if $s;
        $lintResults{fail}{$file}++;
       }
      else                                                                      # If no formatting errors occurred, then lint
       {my $l = $e." xmllint --valid --format --output \"$file\"  \"$file\"";
        if (my @s = qx($l 2>&1))
         {my $s = join "\n", @s;
          say STDERR "LLLLLLLLLLLLLLL Lint\n$l\n$file\n$s\n";
          unshift @s, "Generated on: ". dateTimeStamp;
          appendFile($file, join "\n", map {chomp; "<!-- $_ -->"} @s);
          $lintResults{fail}{$file}++;
         }
        else
         {$lintResults{pass}{$file}++;
         }
       }
     }
   }
 }

# Convert the supplied files after they have been converted to .fodt format by some other means

convertInputFile($_) for fileList($in."*.fodt");                                # Convert the input files

if (1)
 {my %pass = %{$lintResults{pass}};
  my %fail = %{$lintResults{fail}};

  writeFile($reportDir."lintPassFail.data", join "\n",                          # Pass fail report
   "Pass/fail on: ".dateTimeStamp,
   '',
   formatTableBasic([["Pass", scalar keys %pass],
                     ["Fail", scalar keys %fail]]),
   '', 'Pass', (sort keys %pass),
   '', 'Fail', (sort keys %fail));
 }
