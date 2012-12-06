#!/bin/sh
version=`cat VERSION`
base=smvflatten-$version
dir=/tmp/$base/
tar=/tmp/${base}.tar.gz
[ -d $dir ] || mkdir $dir
rm -rf $dir/*
for d in bin obj src; do mkdir $dir/$d; done
cp -p \
configure.sh \
COPYRIGHT \
INSTALL \
LICENSE \
Makefile.in \
NEWS \
README \
VERSION \
$dir
cp -p src/*.[chly] $dir/src/
cd /tmp
rm -f $tar
tar zcf $tar $base
ls -l $tar
