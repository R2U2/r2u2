
#	Simple code generator for AT code
#	format:
#	* % or # starts in-line comment
#	* comma-separated
# 	atomic_name	name of Boolean (in atomic vector)
#	float_name	name of (double) intermediate variable
#	source1		name for first input
#	source2		name for second input
#	units		units (string) -- not used
#	filter		name of filter
# 	filter_par1	filter parameter 1
# 	filter_par2	filter parameter 2
#	access_par	parameter for GET function
#	compare		name of comparer
#	compare_par1	parameter 1 of comparer
#	compare_par2	parameter 2 of comparer
#
#	N/A value is '-'
#
#
#	TODO:
#	check of definedness
#	hardcoded source for r2u2->  must be mod'd for
#	matlab interface
#	test for signal comparison
#	code for:   FILTER_ABS_...
#	code for arbitrary external functions
#	how:   x^2 + y^2 > 5 ???
#	FFT: has 3 args for GET
#	MOVAVG: has 1 args for GET
#

if [ "$1$EMPTY" = "$EMPTY" ] ; then
	echo "usage $0 <SPEC>.txt"
	exit 1
fi

if [ ! -f $1 ] ; then
	echo "$0: could not open file $1"
	exit 1
fi

FN=`basename $1 .txt`

gawk -F, -v FN=$FN '
function extract(idx){
	atomic_name[idx] = $1;
	atomic_names[$1] = $1;
	float_name[idx] = $2;
	float_names[$2] = $2;
	source1[idx] = $3;
	source2[idx] = $4;
	units[idx] = $5;
	filter[idx] = $6;
	filter_par1[idx] = $7;
	filter_par2[idx] = $8;
	access_par[idx] = $9
	compare[idx] = $10;
	compare_par1[idx] = $11;
	compare_par2[idx] = $12;
	}
function print_filter_decls(FN_AT){
	print "\n\n" >>FN_AT
	print "//*****************************************************" >>FN_AT
	print "// declaration of filters" >>FN_AT
 	print "//*****************************************************" >>FN_AT
	for(i=0;i<idx;i++){
	    if (filter[i] != "-"){
		if (atomic_idx[i] >=0){
			fname = atomic_name[i];
			}
		else {
			fname = float_name[i];
			}

		if (filters[filter[i]] == ""){
			print "ILLEGAL FILTER NAME" filter[i] >>FN_AT
			print "ILLEGAL FILTER NAME" filter[i] 
			}
		else {
			print "FILTER_" filter[i] "_DECL(" fname "," filter_par1[i] ")" >> FN_AT;
			}
		}
	    }

	}
function print_filter_init(FN_AT){
	print "\n\n" >>FN_AT
	print "//*****************************************************" >>FN_AT
	print "// initialization of filters" >>FN_AT
 	print "//*****************************************************" >>FN_AT
	print "void at_checkers_init(){" >>FN_AT
	for(i=0;i<idx;i++){
	    if (filter[i] != "-"){
		if (atomic_idx[i] >=0){
			fname = atomic_name[i];
			}
		else {
			fname = float_name[i];
			}

		if (filters[filter[i]] == ""){
			print "ILLEGAL FILTER NAME: " filter[i] >>FN_AT
			print "ILLEGAL FILTER NAME: " filter[i] 
			}
		else {
			print "\tFILTER_" filter[i] "_INIT(" fname "," filter_par1[i] ");" >> FN_AT;
			}
		}
	    }
	print "}\n" >>FN_AT

	}

function print_filter_free(FN_AT){
	print "\n\n" >>FN_AT
	print "//*****************************************************" >>FN_AT
	print "// clean up filters" >>FN_AT
 	print "//*****************************************************" >>FN_AT
	print "void at_checkers_free(){" >>FN_AT
	for(i=0;i<idx;i++){
	    if (filter[i] != "-"){
		if (atomic_idx[i] >=0){
			fname = atomic_name[i];
			}
		else {
			fname = float_name[i];
			}

		if (filters[filter[i]] == ""){
			print "ILLEGAL FILTER NAME" filter[i] >>FN_AT
			print "ILLEGAL FILTER NAME" filter[i] 
			}
		else {
			print "\tFILTER_" filter[i] "_FREE(" fname ");" >> FN_AT;
			}
		}
	    }
	print "}\n" >>FN_AT

	}

function print_filter_update(FN_AT){
	print "\n\n" >>FN_AT
	print "//*****************************************************" >>FN_AT
	print "// update filters and set atomics" >>FN_AT
 	print "//*****************************************************" >>FN_AT
	print "void at_checkers_update(const r2u2_input_data_t *r2u2_input_data){" >>FN_AT
	print "\n" >>FN_AT
	for (i in float_names){
	  if (float_names[i] != "-"){
	    print "double " float_names[i] ";" >>FN_AT
	    }
          }

	for(i=0;i<idx;i++){
	  print "\n" >>FN_AT
	  if (float_names[source1[i]] != ""){
		s=source1[i];
		}
	  else {
		s="r2u2_input_data->"source1[i];
		}

	  s2="";
	  if (source2[i] != "-"){
	    if (float_names[source2[i]] != ""){
		s2=source2[i];
		}
	    else {
		s2="r2u2_input_data->"source2[i];
		}
	    }


		#
		# filter updates
		#
	  if (filter[i] != "-"){
	    if (atomic_idx[i] >=0){
		fname = atomic_name[i];
		}
	    else {
		fname = float_name[i];
		}
	    print "\tFILTER_" filter[i] "_UPDATE(" fname "," filter_par1[i] "," >>FN_AT
	    if (s2 == ""){
	    	print "\t\t" s ");" >>FN_AT
		}
	    else {
	    	print "\t\t" s ", " s2 ");" >>FN_AT
		}
		
		#
		# get filter values
		#
	    if (atomic_name[i] == "-"){
		print "\t" float_name[i] " = FILTER_" filter[i] "_GET(" fname ");" >> FN_AT
		}
	    }
	    
	    if (atomic_name[i] != "-"){
	      if (float_names[source1[i]] != ""){
		      s=source1[i];
		      }
	      else {
		      s="r2u2_input_data->"source1[i];
		      }
	      if (filter[i] != "-"){
		      s="FILTER_" filter[i] "_GET(" fname ")";
		      }

		if (compare[i] == "RANGE_INCL"){
		  print "\tatomics_vector[" atomic_idx[i] "] = AT_RANGE_INCL(" s "," compare_par1[i] "," compare_par2[i] ");" >>FN_AT
		  }
		else if (compare[i] == "MATCH"){
		  print "\tatomics_vector[" atomic_idx[i] "] = AT_MATCH(" s ");" >>FN_AT
		  }
		else {
		  print "\tatomics_vector[" atomic_idx[i] "] = AT_COMP(" s "," compare[i] "," compare_par1[i] ");" >>FN_AT
		  }
		}
	}
	print "}\n" >>FN_AT

	}
	
BEGIN{
	FN_AT="at_checker_" FN ".c";
	idx=0;
	at_idx = 0;
	filters["FILT"] = "FILT";
	filters["FFT"] = "FFT";
	filters["RATE"] = "RATE";
	filters["MOVAVG"] = "MOVAVG";
	filters["PROG"] = "PROG";
	filters["RATE_ANGLE"] = "RATE_ANGLE";
	filters["RATE_ANGLE"] = "RATE_ANGLE";
	filters["ABS_DIFF_ANGLE"] = "ABS_DIFF_ANGLE";
	filters["REGEX"] = "REGEX";
	filters["REGEX_PLEXIL"] = "REGEX_PLEXIL";
	filters["PROGNOSTICS"] = "PROGNOSTICS";
	print "% auto-generated do not modify " > FN"_header.txt"
	print "% from specification file " FN ".txt" >> FN"_header.txt"
	print "// auto-generated do not modify " > FN_AT;
	print "// from specification file " FN ".txt\n" >> FN_AT
	print "#include <math.h>" >>FN_AT
	print "#ifdef R2U2_STANDALONE" >>FN_AT
	print "#    include \"r2u2_input_types.h\"" >>FN_AT
	print "#else" >>FN_AT
	print "#    include \"r2u2_private_types.h\"" >>FN_AT
	print "#endif" >>FN_AT
	print "#include \"at_checkers.h\"" >>FN_AT
	print "#include \"filter_fft.h\"" >>FN_AT
	print "#include \"filter_filt.h\"" >>FN_AT
	print "#include \"filter_rate.h\"" >>FN_AT
	print "#include \"filter_regex.h\"" >>FN_AT
	print "#include \"filter_prognostics.h\"" >>FN_AT
	print "#include \"TL_observers.h\"\n" >>FN_AT

   }
/^%/{ next; }
/^-/{
	extract(idx);
	atomic_idx[idx] = -1;
	idx++;
	}
/^[a-zA-Z]/{
	extract(idx);
	atomic_idx[idx] = at_idx;
	at_idx++;
	idx++;
	}
END {
	for(i=0;i<idx;i++){
		if (atomic_idx[i] >= 0){
			print "map " atomic_name[i] "\t= " atomic_idx[i] "." >> FN"_header.txt"
			}
		}

	print_filter_decls(FN_AT);
	print_filter_init(FN_AT);
	print_filter_free(FN_AT);
	print_filter_update(FN_AT);

	print "generated " idx-1 " at definitions"
}
' $1
# atomic_name,float_name,source,units,filter,par1,par2,CMP,par1,par2
exit 0
