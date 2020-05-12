#!/bin/bash

cd ..
make debug
cd test

time=$1

errors=0
tested=0
completed=0

echo "###########################"
echo "########## START ##########"
echo "###########################"
echo ""

declare -a arr_default=(
"maxsat"
"cnf"
"opb/dec"
)

echo "########## simple #########"
echo ""
for folder in "${arr_default[@]}"; do
    echo $folder
    for formula in instances/$folder/*; do
        echo "running $formula"
        logfile=${formula/instances/logs}
        mkdir -p `dirname $logfile`
        echo -n "" > $logfile.proof
        echo -n "" > $logfile.formula
        timeout $time roundingsat_debug $formula --proof-log=$logfile > /dev/null
        echo "verifying $logfile"
        wc -l $logfile.proof
        veripb $logfile.formula $logfile.proof -d --arbitraryPrecision
        errors=`expr $? + $errors`
        echo $errors
        tested=`expr 1 + $tested`
        echo $tested
        echo ""
    done
done

declare -a arr_modes=(
"linear"
"core-guided"
"lazy-core-guided"
"hybrid"
"lazy-hybrid"
)

declare -a arr_opt=(
"enigma_0"
"stein9_5"
"stein15_9"
"stein27_18"
"stein45_30"
"p0033_3089"
"p0040_62027"
"p0201_7615"
"p0282_258411"
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
    
for mode in "${arr_modes[@]}"; do
    echo "########## $mode ##########"
    echo ""
    for j in "${arr_opt[@]}"; do
        formula="$(cut -d'_' -f1 <<<$j)"
        formula="instances/opb/opt/$formula.opb"
        obj="$(cut -d'_' -f2 <<<$j)"
        echo "running $formula"
        logfile=${formula/instances/logs}
        mkdir -p `dirname $logfile`
        echo -n "" > $logfile.proof
        echo -n "" > $logfile.formula
        output=`timeout $time roundingsat_debug $formula --proof-log=$logfile --opt-mode=$mode | awk '/^o/ {print $2}'`
        if [ "$output" != "" ] && [ "$output" != "$obj" ]; then
            errors=`expr 1000 + $errors`
            echo "wrong output: $output vs $obj"
        fi
        echo "verifying $logfile"
        wc -l $logfile.proof
        veripb $logfile.formula $logfile.proof -d --arbitraryPrecision
        errors=`expr $? + $errors`
        echo $errors
        tested=`expr 1 + $tested`
        echo $tested
        echo ""
    done
done

echo "tested: $tested"
echo "errors: $errors"
