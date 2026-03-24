#!/bin/bash

NAME=agdarya-`git show -s --format=%h`-`date +'%Y%m%d'`
mkdir -p $NAME
cp ../proofgeneral/*.el $NAME
cp ../ctags/agdarya.ctags $NAME
cp ../result/bin/agdarya $NAME
cp INSTALL.txt install-pg.sh proof-site.patch $NAME
tar -czf agdarya-master-static.tar.gz $NAME
mkdir -p build/releases
mv agdarya-master-static.tar.gz build/releases
