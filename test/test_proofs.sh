#!/bin/bash

cd ..
make debug
#g++ -o roundingsat_debug roundingsat.cc -g -O3
cd test

declare -a arr_dec=(
"stein9"
"stein15"
"p0040"
"pipex"
"bm23"
"p0291"
"sentoy"
"air01"
#"lp4l"
#"cracpb1"
#"air02"
#"air06"
)

declare -a arr_opt_cg=(
"diamond"
"stein9"
"stein15"
"p0033"
"stein27"
"p0040"
#"pipex"
"bm23"
"enigma"
#"stein45"
#"lseu"
#"p0201"
"sentoy"
#"p0282"
#"p0291"
#"mod008"
#"p0548"
"air01"
#"cracpb1"
#"lp4l"
#"l152lav"
#"mod010"
#"air02"
)

declare -a arr_opt_cg_lazy=(
"diamond"
"stein9"
"stein15"
"p0033"
"stein27"
"p0040"
"pipex"
"bm23"
"enigma"
#"stein45"
#"lseu"
#"p0201"
"sentoy"
#"p0282"
#"p0291"
#"mod008"
#"p0548"
"air01"
#"cracpb1"
#"lp4l"
#"l152lav"
#"mod010"
#"air02"
)

declare -a arr_opt_lin=(
"diamond"
"stein9"
"stein15"
"p0033"
"stein27"
"p0040"
"pipex"
"bm23"
"enigma"
#"stein45"
"lseu"
#"p0201"
"sentoy"
#"p0282"
"p0291"
#"mod008"
#"p0548"
"air01"
#"cracpb1"
#"lp4l"
#"l152lav"
#"mod010"
#"air02"
)

i="cnf"
echo "running $i"
rm $i.proof
rm $i.formula
bzcat /home/jodv/workspace/instances/dec/CNF/even_colouring/ec_rand4regsplit-v030-n1.cnf.bz2 | ../roundingsat_debug --proof-log=$i > /dev/null
echo "verifying $i"
wc -l $i.proof
veripb $i.formula $i.proof -d $1
echo ""

i="maxsat"
echo "running $i"
rm $i.proof
rm $i.formula
bzcat /home/jodv/workspace/instances/maxsat/mse19-complete-weighted-benchmarks/planning/driverlog01c.wcsp.dir.wcnf.bz2 | ../roundingsat_debug --proof-log=$i > /dev/null
echo "verifying $i"
wc -l $i.proof
veripb $i.formula $i.proof -d $1
echo ""

echo "*** HYBRID COREGUIDED OPTIMIZATION ***"
for i in "${arr_opt_cg[@]}"
do
    echo "running $i"
    rm $i.proof
    rm $i.formula
    bzcat /home/jodv/workspace/instances/opt/MIPLIB/miplib2/$i.opb.bz2 | ../roundingsat_debug --proof-log=$i --opt-mode=3 > /dev/null
    echo "verifying $i"
    wc -l $i.proof
    veripb $i.formula $i.proof -d $1
    echo ""
done

echo "*** HYBRID LAZY COREGUIDED OPTIMIZATION ***"
for i in "${arr_opt_cg_lazy[@]}"
do
    echo "running $i"
    rm $i.proof
    rm $i.formula
    bzcat /home/jodv/workspace/instances/opt/MIPLIB/miplib2/$i.opb.bz2 | ../roundingsat_debug --proof-log=$i --opt-mode=4 > /dev/null
    echo "verifying $i"
    wc -l $i.proof
    veripb $i.formula $i.proof -d $1
    echo ""
done

echo "*** LINEAR OPTIMIZATION ***"
for i in "${arr_opt_lin[@]}"
do
    echo "running $i"
    rm $i.proof
    rm $i.formula
    bzcat /home/jodv/workspace/instances/opt/MIPLIB/miplib2/$i.opb.bz2 | ../roundingsat_debug --proof-log=$i --opt-mode=0 > /dev/null
    echo "verifying $i"
    wc -l $i.proof
    veripb $i.formula $i.proof -d $1
    echo ""
done

echo "*** DECISION ***"
for i in "${arr_dec[@]}"
do
    echo "running $i"
    rm $i.proof
    rm $i.formula
    bzcat /home/jodv/workspace/instances/dec/MIPLIB/miplib2/$i.0.u.opb.bz2 | ../roundingsat_debug --proof-log=$i > /dev/null
    echo "verifying $i"
    wc -l $i.proof
    veripb $i.formula $i.proof -d $1
    echo ""
done


