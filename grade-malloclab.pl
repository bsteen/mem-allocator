#!/usr/bin/perl   
#!/usr/local/bin/perl 
use Getopt::Std;
use config;

#########################################################################
# grade-malloclab.pl - Malloc Lab autograder
#
# Copyright (c) 2002, R. Bryant and D. O'Hallaron, All rights reserved.
# May not be used, modified, or copied without permission.
#########################################################################

# autoflush output on every print statement
$| = 1; 

# Any tmp files created by this script are readable only by the user
umask(0077); 

# What is the name of this Lab?
$LABNAME = "malloclab";

# What is the distribution of points?
$MAXCORR = 20;   # Max correctness points
$MAXPERF = 35;   # Max performance points
$MAXSTYLE = 10;  # Max style points

# Where are the source files for the driver? 
# (override with -s)
$SRCDIR = ".";

# Where is the handin directory? 
# (override with -d)
$HANDINDIR = "./handin";

# Where are the trace files for the driver?
$TRACEDIR = "../../traces/";

#
# These are the src files we need to compile the driver (besides mm.c). 
# Look for them in $SRCDIR,  which is set by default in config.pm 
# and can be altered with -s.
#
$driverfiles = "Makefile,mdriver.c,config.h,memlib.c,memlib.h,mm.h,clock.c,clock.h,fcyc.c,fcyc.h,fsecs.c,fsecs.h,ftimer.c,ftimer.h";

#
# usage - print help message and terminate
#
sub usage {
    printf STDERR "$_[0]\n";
    printf STDERR "Usage: $0 -f <file> [-he] [-s <srcdir>]\n";
    printf STDERR "Options:\n";
    printf STDERR "  -h          Print this message.\n";
    printf STDERR "  -e          Don't include original handin file on the grade sheet\n";
    printf STDERR "  -f <file>   Name of handin file to be graded\n";
    printf STDERR "  -s <srcdir> Directory where malloc driver is located\n";
    die "\n";
}

#
# corr_score - returns correctness score as a function of the
#       number of traces that were handled without any errors.
#
sub corr_score {
    my $numcorrect = $_[0]; # number of traces handled without errors 
    my $numtraces = 11;     # number of traces

    # Score is based on fraction of traces that were correct
    return ($numcorrect / $numtraces) * $MAXCORR;
}

#
# perf_score - returns performance score as a function of the
#      performance index. A solution with a performance index
#      above or equal to $threshhold gets full credit.
#
sub perf_score {
    my $perfindex = $_[0];  # performance index
    my $threshhold = 0.95;  # full credit threshhold
    my $score;

    $score = (($perfindex/100.0) + (1-$threshhold)) * $MAXPERF;
    if ($score > $MAXPERF) {
      $score = $MAXPERF;
    }

    return $score;
}

##############
# Main routine
##############

# 
# Parse the command line arguments
#
getopts('hef:s:');
if ($opt_h) {
    usage();
}
if (!$opt_f) {
    usage("Missing required argument (-f)");
}

# 
# These optional flags override defaults in config.pm
#
if ($opt_s) {         # driver src directory
    $SRCDIR = $opt_s;
}

# 
# Initialize some file and path names
#
$infile = $opt_f;
($infile_basename = $infile) =~ s#.*/##s;     # basename of input file
$tmpdir = "./tmp/$infile_basename.$$";         # scratch directory
print "tmpdir: $tmpdir \n"; 
$0 =~ s#.*/##s;                               # this prog's basename

# absolute pathname of src directory
$srcdir_abs = `cd $SRCDIR; pwd`; 
chomp($srcdir_abs);

# 
# This is a message we use in several places when the program dies
#
$diemsg = "The files are in $tmpdir.";

# 
# Make sure the driver src directory exists
#
(-d $SRCDIR and -e $SRCDIR)
    or  die "$0: ERROR: Can't access source directory $SRCDIR.\n";

# 
# Make sure the input file exists and is readable
#
open(INFILE, $infile) 
    or die "$0: ERROR: could not open file $infile\n";
close(INFILE);

# 
# Set up the contents of the scratch directory
#
system("mkdir $tmpdir") == 0
  or die "ERROR: mkdir $tmpdir failed\n";
system("cp $infile $tmpdir/mm.c") == 0
  or die "ERROR: cp $infile to $tmpdir failed\n";
system("bash -c 'cp $SRCDIR/\{$driverfiles\} $tmpdir'") == 0
  or die "ERROR: cp driver files to $tmpdir failed\n";

# Print header
print "\nCS:APP Malloc Lab: Grading Sheet for $infile_basename\n\n";

#
# Compile the driver
#
print "Part 1: Compiling the driver\n\n";
system("(cd $tmpdir; make mdriver)") == 0 
    or die "$0: ERROR: Unable to compile mdriver. $diemsg\n";

#
# Run the driver
#
print "\n\nPart 2: Running the driver with the -g autograder option\n\n";
print "tempdir: $tmpdir \n";
print "./mdriver -t $TRACEDIR -vg > results.txt \n";
system("(cd $tmpdir; ./mdriver -t $TRACEDIR -vg > results.txt)") == 0 
    or die "$0: ERROR: Unable to run driver program. $diemsg\n";

print "End Parts 1 and 2\n";
#
# Extract the number of correct traces and the performance index
# from the driver output
#
$result = `(cd $tmpdir; cat results.txt)`;
$result =~ /correct:(.*)/;
$numcorrect = $1;
$result =~ /perfidx:(.*)/;
$perfindex = $1;
print $result;

#
# Compute the number of points for each solution
#
$corr_points = corr_score($numcorrect);
$perf_points = perf_score($perfindex);

#
# Print the grade summary
#
$total = $MAXCORR+$MAXPERF+$MAXSTYLE;
print "\n\nPart 3: Grade\n\n";
printf "Correctness: %3.0f  / %3.0f (correct traces = $numcorrect)\n", 
  $corr_points, $MAXCORR;
printf "Performance: %3.0f  / %3.0f (performance index = $perfindex)\n", 
  $perf_points, $MAXPERF;
printf "Style:            / %3.0f\n", $MAXSTYLE;
print "\n";
printf "Total:            / %3.0f\n", $total; 

# 
# Optionally print the original handin file 
#
# if (!$opt_e) {
#    print "\f\nPart 4: Handin file $infile_basename\n\n";
#    system("cat $infile");
# } 

#
# Everything went OK, so remove the scratch directory
#
system("rm -fr $tmpdir");

exit;


