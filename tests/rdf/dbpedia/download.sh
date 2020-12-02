#!/bin/bash

# strip comments
sed 's/#.*$//g' urllist > urllist.stripped

# download data
wget -N --content-disposition --trust-server-names -i urllist.stripped

# clean temporary file
rm urllist.stripped

# decompress data
gunzip *.gz 2>/dev/null
bzip2 -d *.bz2 2>/dev/null

# add .nt extension to *.ttl files because they are ntriples really
for F in *.ttl; do
    mv $F $F.nt
done
