
echo "testing binary assembler..."
echo "usage: $0 FORMULA.txt"
FN=$1
BFN=`basename $FN .txt`

BINDIR=../../bin

FT=$BINDIR/FT
TMP=xxx
FASM=$BINDIR/ftas.py

$FT $FN

if [ ! -f $BFN.fts ] ; then
	echo "cannot open assembly file"
	exit 1
fi

sed -e 's/^[0-9]*:[	 ]*//' \
	-e 's/		/	/g' \
	-e 's/ /	/g' \
		$BFN.fts >$TMP.fasm

echo "calling Assembler..."
$FASM $TMP <$TMP.fasm

echo "comparing files...: ftm"
diff $TMP.ftm $BFN.ftm
echo "comparing files...: fti"
diff $TMP.fti $BFN.fti


#------------- past time part
PTASM=$BINDIR/ptas.py


if [ ! -f $BFN.pts ] ; then
	echo "cannot open assembly file"
	exit 1
fi

sed -e 's/^[0-9]*:[	 ]*//' \
	-e 's/		/	/g' \
	-e 's/ /	/g' \
		$BFN.pts >$TMP.pasm

echo "calling Assembler..."
$PTASM $TMP 44 <$TMP.pasm

echo "comparing files...: ptm"
diff $TMP.ptm $BFN.ptm
echo "comparing files...: pti"
diff $TMP.pti $BFN.pti

rm -f $TMP.pasm $TMP.pti $TMP.ptm

