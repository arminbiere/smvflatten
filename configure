#!/bin/sh

cd `dirname $0`

#--------------------------------------------------------------------------#

printf "version ..."
version="`cat VERSION`"
echo " $version"

#--------------------------------------------------------------------------#

printf "searching for test cases ..."
if [ -d test ]
then
  echo " found"
  cmu_smv=""
  printf "searching for CMU smv ..."
  #
  # you may need to add more file-names here
  #
  for p in `printenv PATH | sed -e 's,:, ,g'`
  do
    for b in cmu-smv smv
    do
      f=$p/$b
      if [ -f $f ]
      then
	cmu_smv=$f
	break;
      fi
    done
  done

  if [ "$cmu_smv" ]
  then
    echo " $cmu_smv"
  else
    echo " not found (some black box tests are disabled)"
  fi
else
  echo " not found"
fi

#--------------------------------------------------------------------------#

printf "generating config.sh ..."
rm -f config.sh
echo "version=\"$version\"" >> config.sh
[ "$cmu_smv" ] && echo "cmu_smv=$cmu_smv" >> config.sh
echo " done"

#--------------------------------------------------------------------------#

printf "generating Makefile ..."
rm -f Makefile
sed -e "s,@VERSION@,$version," Makefile.in > Makefile
echo " done"
