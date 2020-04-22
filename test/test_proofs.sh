#!/bin/bash

cd ..
make debug
#g++ -o roundingsat_debug roundingsat.cc -g -O3
cd test

time=1

errors=0

i="maxsat"
echo "running $i"
rm $i.proof
rm $i.formula
bzcat /home/jod/workspace/instances/maxsat/mse19-complete-weighted-benchmarks/planning/driverlog01c.wcsp.dir.wcnf.bz2 | ../roundingsat_debug --proof-log=$i > /dev/null
echo "verifying $i"
wc -l $i.proof
veripb $i.formula $i.proof -d --arbitraryPrecision $1
errors=`expr $? + $errors`
echo $errors
echo ""

i="cnf"
echo "running $i"
rm $i.proof
rm $i.formula
bzcat /home/jod/workspace/instances/dec/CNF/even_colouring/ec_rand4regsplit-v030-n1.cnf.bz2 | ../roundingsat_debug --proof-log=$i > /dev/null
echo "verifying $i"
wc -l $i.proof
veripb $i.formula $i.proof -d --arbitraryPrecision $1
errors=`expr $? + $errors`
echo $errors
echo ""

declare -a arr_dec=(
"diamond"
"stein9"
"stein15"
"stein27"
"stein29"
"p0040"
"pipex"
"bm23"
"p0291"
"sentoy"
"lp4l"
"cracpb1"
"air01"
"air02"
"air03"
"air06"
)

echo "*** decision ***"
echo ""
for i in "${arr_dec[@]}"
do
    echo "running $i"
    rm $i.proof
    rm $i.formula
    bzcat /home/jod/workspace/instances/dec/MIPLIB/miplib2/$i.0.u.opb.bz2 > $i.opb
    timeout $time ../roundingsat_debug $i.opb --proof-log=$i > /dev/null
    echo "verifying $i"
    wc -l $i.proof
    veripb $i.formula $i.proof -d --arbitraryPrecision $1
    errors=`expr $? + $errors`
    echo $errors
    echo ""
done

declare -a arr_opt=(
"enigma_0"
"stein9_5"
"stein15_9"
"stein27_18"
"stein45_30"
"p0033_3089"
"p0040_62027"
"p0201_7615"
"p0282_254811"
"p0291_7609041"
"p0548_8691"
"mod008_307"
"mod010_6548"
"air01_6796"
"air02_7810"
"air03_340160"
"air06_49649"
"pipex_788263"
"sentoy_-7772"
"bm23_34"
"l152lav_4722"
"lp4l_2967"
"lseu_1120"
"cracpb1_22199"
)

declare -a arr_modes=(
"linear"
"hybrid"
"lazy-hybrid"
)

for mode in "${arr_modes[@]}"; do
    echo "*****  $mode  *****"
    echo ""
    for j in "${arr_opt[@]}"; do
        i="$(cut -d'_' -f1 <<<$j)"
        obj="$(cut -d'_' -f2 <<<$j)"
        echo "running $i"
        rm $i.proof
        rm $i.formula
        bzcat /home/jod/workspace/instances/opt/MIPLIB/miplib2/$i.opb.bz2 > $i.opb
        output=`timeout $time ../roundingsat_debug $i.opb --proof-log=$i --opt-mode=$mode | awk '/^o/ {print $2}'`
        if [ "$output" != "" ] && [ "$output" != "$obj" ]; then
            errors=`expr 100 + $errors`
            echo "wrong output: $output vs $obj"
        fi
        echo "verifying $i"
        wc -l $i.proof
        veripb $i.formula $i.proof -d --arbitraryPrecision $1
        errors=`expr $? + $errors`
        echo $errors
        echo ""
    done
done

