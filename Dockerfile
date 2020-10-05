# start from a known base ubuntu image
from ubuntu:focal

# update the apt repo
run apt-get -qy update

#install agda
run apt-get -qy install agda=2.6.0.1-1build4

# copy over everything in the current directory
copy . .

# remove any agdai files that might be local to the host
cmd ["rm" , "*.agdai"]

# run agda on all.agda very verbosely
cmd ["agda" , "-v", "3", "all.agda"]
