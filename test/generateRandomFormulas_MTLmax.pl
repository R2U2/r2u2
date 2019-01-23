#!/usr/bin/perl
#
#by Kristin Y. Rozier
#
#     This program generates a test set of MTL formulas using methods inspired by those described in "Improved automata generation for linear temporal logic" by Daniele, Guinchiglia, and Vardi.
#
#     The formulas are written in a standard format; it is presumed that they will be converted to any tool-specific format necessary after having been read in by the appropriate program.
#
# Inputs: (all are required; order matters)
#      L : formula length
#      N : number of variables (named a0, a1, ...)
#      P : probability of choosing temporal operators 
#      M : generate bounds <= M (M is maximum delta between i and j in Z[i,j])
#      T : max trace length; mission-time formulas must have end bounds < T (T is max value of j)
#      (--help will produce a usage message)
#      no inputs: just generate all values of L, N, and P for default value of M
#
# Outputs: (INCOMPLETE)
#
# NOTE: Any temporal operator will randomly appear 1 of 3 ways: Z, Z[i], Z[i,j]
#
# Usage: generateRandomFormulas_MTL.pl
#


use FileHandle;      #for open() 

#Set the directory where all of the formulas will be stored
$formula_dir = "./formulasMTL";

#If the formula directory doesn't exist, create it
if (! (-d $formula_dir) ) {
    mkdir("$formula_dir", 0755) or die "Cannot mkdir $formula_dir: $!";
} #end if
elsif (! (-w $formula_dir) ) { #check for write permission
    die "ERROR: formula directory $formula_dir is not writable!";
} #end elseif


#################### Argument Setup ####################

#Check for correct number and type of command line arguments

if ($ARGV[0] =~ /--help/) {
    die "generateRandomFormulas_MTL.pl: \n\tWith no arguments: generate a wide range of formula files containing MTL formulas.\n\tWith 3 arguments: generate files for specified L, N, P, M, T (order matters).\n";
} #end if

# if ($ARGV[0] =~ /-useR/i) {
#     $useR = 1; 
#     print "Creating two directories, with and without 'R'...\n";
#     shift(@ARGV); #remove this flag
# } #end if
# die "ARGV is now @ARGV";

if (@ARGV == 4) {
    print "Reading command-line arguments:\n";
    ($L, $n, $P, $M) = @ARGV;
    print "L = $L; N = $n; P = $P; M = $M\n";
    if (($L !~ /^\d+\.?\d*$/) 
	|| ($n !~ /^\d+\.?\d*$/) 
	|| ($P !~ /^\d+\.?\d*$/)
	|| ($M !~ /^\d+\.?\d*$/)
	|| ($L < 1)
	|| ($n < 1) 
	|| ($P < 0)
	|| ($P > 1) 
	|| ($M < 1)
	|| ($T < 1)
	) {
	die "Require 5 numerical arguments: L, N, P, M, T\n";
    } #end if
} #end if

elsif (@ARGV != 0) {
    die "Usage: generateRandomFormulas_MTL.pl [optional: specify all of L, N, P, M, and T in that order]\n";
} #end elsif

else {print "Generating formulas for ranges of L, N, P, M, and T ...\n";}


#################### Generation of Formulas ####################

### Set up the generation variables

$F = 500; #number of formulas to generate in one test set
print "F is $F\n";
print OUT "F is $F\n";

@N = qw(a0 a1 a2 a3 a4); #array of variables
print "N is @N\n";
print OUT "N is @N\n";

@Llist = (5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100);
print "L = (@Llist)\n";
print OUT "L = (@Llist)\n";

#@Plist = (1/3, 0.5, 0.7, 0.95); #array of probabilities to try
@Plist = (1.0); ##################Pei
print "P = (@Plist)\n";
print OUT "P = (@Plist)\n";

$M = 4; #default value for M

$T = 4; #default value for T


#Note: No R operator in MTL
#@operators = ("G", "F", "U", "!", "&&", "||"); #array of operators: 
@operators = ("G", "F", "U", "!", "&", "|"); #array of operators: 
$num_unary_temporal_ops = 2;
#$num_temporal_ops = 4;
$num_temporal_ops = 3;#Pei################################################
#order is very important here: unary temporal ops, binary temporal ops, then ! then binary ops


#####################################################################
#
# Functions: 
#    
#    generate_bounds: generates the bounds for one temporal operator 
#    generate_formula: generates one formula
#
#####################################################################


### Define a function to use to generate bounds for one temporal operator
### Future option: allow one input (1,2,3) to determine what type of bounds with the default being the current behavior of randomly choosing which type of bounds
sub generate_bounds {

    my $this;

    my $M_num = int(rand(3)); #Choose between the 3 common formula scenarios:
    if ($M_num == 1) { #1) Make the bounds 0 ... num
	my $first_num = int(rand($M));
	$this = "[0,$first_num]"; #M single bound
    } #end if
    elsif ($M_num == 2) { #2) Make the bounds num1 ... num2
	my $first_num = int(rand($M));
	my $bound = $M - $first_num;
	my $second_num = $first_num + int(rand($bound)); #ensure 2nd num is >= 1st
	$this = "[${first_num},${second_num}]"; #M double bound
    } #end if
    else { #3) Make the bounds num1 ... T
	my $first_num = int(rand($M));
	my $first_num = ${T}-${first_num};
	if ($first_num < 0) { $first_num = 0; } #make sure the lower bound is positive
	$this = "[$first_num,$T]"; #max trace bound
    } #end if

    return ($this);
    
} #end generate_bounds


### Define a recursive function to use to generate each formula
sub generate_formula {

    my $L = $_[0];
    my $S;
    my $op;
    my $this;
    my $bound;

    #print STDERR "generate_formula here: L is $L, N is $n, P is $P, M is $M, and T is $T\n";
    
    if ($L == 1) { #randomly choose one variable
	my $var_num = int(rand($n));
	$this = "a${var_num}";
	#print STDERR "this($this) = N[$randn] for n($n)\n";
	return ($this);
    } #end if
    elsif ($L == 2) { #randomly choose one variable and one unary operator
	$r = rand; #r is a random variate [0, 1)
	if ($r < $P) { #temporal operator chosen
	    $op = "$operators[int(rand($num_unary_temporal_ops))]"; #set operator
	    $this = "(${op}";

	    #if ($op ne "X") { #X operators can't have MTL bounds
	    $bound = generate_bounds();
	    $this = $this.$bound;	    
	    #} #end if "X"

	    my $var_num = int(rand($n));
            $this  = $this."(a${var_num}))"; #set variable
	    #print STDERR "returning1 $this\n";
	    return ($this);
	} #end if
	else { #only 1 non-temporal unary operator: !
	    my $var_num = int(rand($n));
	    $this = "(! (a${var_num}))";
	    #print STDERR "returning2 $this\n";
	    return ($this);
	} #end else
    } #end elsif
    else { #$L > 2
	#choose an operator $op
	$r = rand; #r is a random variate [0, 1)

	#choose an operator with certain probabilities...
	if ($r < $P) {
	    #pick which temporal operator
	    $i = int(rand($num_temporal_ops));
	    $op = $operators[$i]; #because temporal operators are all first in the list
	    $op = "U"; #Pei: force generate until####################################################remove this line later
	    $this = $op; #save operator in this
	    if ($op eq "U") { #binary operators
		#choose S such that 1 <= S <= L - 2
		my $Lminus2 = $L - 2;
		my $S = int(1+rand($Lminus2));
		#print STDERR "S is $S\t";
		my $T = $L - $S - 1;
		#print STDERR "T is $T\n";
		#print STDERR "Returning3 formula of length $S + $T + 1 $op = $L\n";
		
		my $Shalf = &generate_formula($S);
		my $Thalf = &generate_formula($T);
		
		#Decide on M-bounds
		$bound = generate_bounds();
		$this = $this.$bound;
		
		$this = "(".$Shalf
			.") $this ("
			.$Thalf.")";
		
		#print STDERR "returning3 $this\n";
		return $this;
	    } #end if
	    else { #unary temporal operators
		my $Lminus1 = $L - 1;
		my $recur = &generate_formula($Lminus1);

		#Decide on M-bounds
		if ($op ne "!"){ ### pei add this line on Mar.15
			$bound = generate_bounds();
			$this = $this.$bound;
		} ### pei add this line on Mar.15
		$this = "($this ("
		    .$recur
		    ."))";
		#print STDERR "returning5 $this\n";
		return $this;
	    } #end else unary operator
	} #end if temporal operator
	else { #choose non-temporal operator

	    #pick which non-temporal operator
	    $j = @operators - $num_temporal_ops;
	    $i = int(rand($j)) + $num_temporal_ops;
	    $op = $operators[$i]; #because temporal operators are all first in the list

	    if ($op eq "!") { #the only non-temporal unary operator
		my $Lminus1 = $L - 1;
		my $recur = &generate_formula($Lminus1);
		$this = "(! ("
		    .$recur
		    ."))";
		#print STDERR "returning6 $this\n";
		return $this;
	    } #end if
	    else { #binary op
		#choose S such that 1 <= S <= L - 2
		my $Lminus2 = $L - 2;
		$S = int(1+rand($Lminus2));
		#print STDERR "S is $S\t";
		my $T = $L - $S - 1;
		#print STDERR "T is $T\n";
		#print STDERR "Returning1 formula of length $S + $T = $L, op = $op\n";

		my $Shalf = &generate_formula($S);
		my $Thalf = &generate_formula($T);
		
		$this = "(".$Shalf
			.") $op ("
			.$Thalf.")";

		#print STDERR "Back1: Got $formula\n";
		#print STDERR "returning7 $this\n";
		return $this;
	    } #end else
	} #end else non-temporal operator
    } #end else $L > 2
	   
} #end generate_formula


##################################################################
#
# Main Program: 
# 
#    Generate output files, each containing a set of formulas with
#       the same L, N, P, M values,.
#
#
##################################################################


if (@ARGV == 4) {

    print "\n\nN = $n, L = $L, P = $P, M = $M; T - $T:\n";

    #Create an output file for each set of formulas data
    $FormFile = "${formula_dir}/P${P}N${n}L${L}M${M}T${T}.form";
    open(FORMULAS, ">$FormFile") or die "Could not open $FormFile";
    
    for ($f = 0; $f < $F; $f++) { #generate $F formulas
	
	$formula = &generate_formula($L);
	print FORMULAS "$formula\n";
	#print STDERR "End: $formula\n";

    } #end for each formula
    
    close(FORMULAS) or die "Could not close $FormFile";
    #return; #exit since we just needed to generate this one set
    die;
} #end if


#################### Generate the sets of formulas ####################

for ($n = 1; $n <= @N; $n++) { #for n variables

    for ($l = 0; $l < @Llist; $l++) { #for each length
	$L = $Llist[$l];
	
	for ($p = 0; $p < @Plist; $p++) { #for each probability
	    $P = $Plist[$p];
	    
	    print "\n\nN = $n, L = $L, P = $P, M = $M, T = $T:\n";
	    
	    #Create an output file for each set of formulas data
	    $FormFile = "${formula_dir}/P${P}N${n}L${L}M${M}T${T}.form";
	    open(FORMULAS, ">$FormFile") or die "Could not open $FormFile";

	    for ($f = 0; $f < $F; $f++) { #generate $F formulas
		
		$formula = &generate_formula($L);
		print FORMULAS "$formula\n";
		
	    } #end for each formula

	    close(FORMULAS) or die "Could not close $FormFile";
	    
	} #end for each temporal probability

    } #end for each length

} #end for n variables

