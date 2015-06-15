#!/bin/sh

#
# Script to writing btor from verilog design
#

if [ "$#" -ne 3 ]; then
  echo "Usage: $0 input.v output.smv top-module-name" >&2
  exit 1
fi
if ! [ -e "$1" ]; then
  echo "$1 not found" >&2
  exit 1
fi

FULL_PATH=$(readlink -f $1)
DIR=$(dirname $FULL_PATH)

./yosys -q -p "
read_verilog -sv $1; 
hierarchy -top $3; 
hierarchy -libdir $DIR; 
hierarchy -check; 
proc; 
opt;
# [-mux_undef] [-undriven] [-fine] [-full] [-keepdc]; 
#rename -hide;;;
#techmap -map +/pmux2mux.v;;
splice;;; 
memory_dff -wr_only;
memory_collect;;
flatten;;
memory_unpack; 
splitnets -driver;
setundef -zero -undriven;;
wreduce;;;
write_smv $2;"

