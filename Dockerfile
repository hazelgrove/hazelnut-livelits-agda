# start from a known base ubuntu image
from ubuntu:groovy

# update the apt repo
run apt-get -qy update

#install agda
run apt-get -qy install agda=2.6.1-1build1

# copy over everything in the current directory
copy . .

# remove any agdai files that might be local to the host
run ["rm", "-f", "*.agdai"]

# run agda on all.agda, noting that unicode ought to be allowed
cmd ["agda" , "-v", "1", "all.agda"]
