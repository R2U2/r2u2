
AOS=$HOME/AOS/aos/tools/r2u2prepare

echo $AOS

for i in *.h *.cpp *.y ; do
	if [ ! -f $AOS/$i ] ; then
		echo "can't find AOS version of $i..."
	else
		echo ">>>>>>>>>>>> $i"
		diff $i $AOS/$i
	fi
done
