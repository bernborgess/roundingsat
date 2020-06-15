#!/bin/bash

time=$1
binary=$2

SCRIPTPATH="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"

errors=0
tested=0
completed=0

echo "###########################"
echo "########## START ##########"
echo "###########################"
echo ""
echo "timeout: $1"
echo "binary: $2"
echo ""

declare -a arr_default=(
"maxsat"
"cnf"
"opb/dec"
)

declare -a arr_dec=(
"cnf/ec_rand4regsplit-v030-n1.cnf_UNSATISFIABLE"
"opb/dec/air01.0.s.opb_SATISFIABLE"
"opb/dec/air01.0.u.opb_UNSATISFIABLE"
"opb/dec/air02.0.s.opb_SATISFIABLE"
"opb/dec/air02.0.u.opb_UNSATISFIABLE"
"opb/dec/air06.0.s.opb_SATISFIABLE"
"opb/dec/air06.0.u.opb_UNSATISFIABLE"
"opb/dec/bm23.0.s.opb_SATISFIABLE"
"opb/dec/bm23.0.u.opb_UNSATISFIABLE"
"opb/dec/cracpb1.0.s.opb_SATISFIABLE"
"opb/dec/cracpb1.0.u.opb_UNSATISFIABLE"
"opb/dec/diamond.0.d.opb_UNSATISFIABLE"
"opb/dec/lp4l.0.s.opb_SATISFIABLE"
"opb/dec/lp4l.0.u.opb_UNSATISFIABLE"
"opb/dec/p0040.0.s.opb_SATISFIABLE"
"opb/dec/p0040.0.u.opb_UNSATISFIABLE"
"opb/dec/p0291.0.s.opb_SATISFIABLE"
"opb/dec/p0291.0.u.opb_UNSATISFIABLE"
"opb/dec/pipex.0.s.opb_SATISFIABLE"
"opb/dec/pipex.0.u.opb_UNSATISFIABLE"
"opb/dec/sentoy.0.s.opb_SATISFIABLE"
"opb/dec/sentoy.0.u.opb_UNSATISFIABLE"
"opb/dec/stein9.0.s.opb_SATISFIABLE"
"opb/dec/stein9.0.u.opb_UNSATISFIABLE"
"opb/dec/stein15.0.s.opb_SATISFIABLE"
"opb/dec/stein15.0.u.opb_UNSATISFIABLE"
)

echo "########## simple #########"
echo ""

for j in "${arr_dec[@]}"; do
    formula="$(cut -d'_' -f1 <<<$j)"
    formula="$SCRIPTPATH/instances/$formula"
    obj="$(cut -d'_' -f2 <<<$j)"
    echo "running $formula"
    logfile=${formula/instances/logs}
    mkdir -p `dirname $logfile`
    echo -n "" > $logfile.proof
    echo -n "" > $logfile.formula
    output=`timeout $time $binary $formula --proof-log=$logfile 2>&1 | awk '/^o|SATISFIABLE|.*Assertion.*/ {print $2}'`
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

declare -a arr_modes=(
"linear"
"core-guided"
"lazy-core-guided"
"hybrid"
"lazy-hybrid"
)

declare -a arr_opt=(
"maxsat/driverlog01bc.wcsp.dir.wcnf_2245"
"opb/opt/enigma.opb.opb_0"
"opb/opt/stein9.opb_5"
"opb/opt/stein15.opb_9"
"opb/opt/stein27.opb_18"
"opb/opt/stein45.opb_30"
"opb/opt/p0033.opb_3089"
"opb/opt/p0040.opb_62027"
"opb/opt/p0201.opb_7615"
"opb/opt/p0282.opb_258411"
"opb/opt/p0291.opb_7609041"
"opb/opt/p0548.opb_8691"
"opb/opt/mod008.opb_307"
"opb/opt/mod010.opb_6548"
"opb/opt/air01.opb_6796"
"opb/opt/air02.opb_7810"
"opb/opt/air03.opb_340160"
"opb/opt/air06.opb_49649"
"opb/opt/pipex.opb_788263"
"opb/opt/sentoy.opb_-7772"
"opb/opt/bm23.opb_34"
"opb/opt/l152lav.opb_4722"
"opb/opt/lp4l.opb_2967"
"opb/opt/lseu.opb_1120"
"opb/opt/cracpb1.opb_22199"
)

for mode in "${arr_modes[@]}"; do
    echo "########## $mode ##########"
    echo ""
    for j in "${arr_opt[@]}"; do
        formula="$(cut -d'_' -f1 <<<$j)"
        formula="$SCRIPTPATH/instances/$formula"
        obj="$(cut -d'_' -f2 <<<$j)"
        echo "running $formula"
        logfile=${formula/instances/logs}
        mkdir -p `dirname $logfile`
        echo -n "" > $logfile.proof
        echo -n "" > $logfile.formula
        output=`timeout $time $binary $formula --opt-mode=$mode --proof-log=$logfile 2>&1 | awk '/^o|UNSATISFIABLE|.*Assertion.*/ {print $2}'`
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

echo "########## no proofs ##########"
echo ""
for j in "${arr_opt[@]}"; do
    formula="$(cut -d'_' -f1 <<<$j)"
    formula="$SCRIPTPATH/instances/opb/opt/$formula.opb"
    obj="$(cut -d'_' -f2 <<<$j)"
    echo "running $formula"
    logfile=${formula/instances/logs}
    mkdir -p `dirname $logfile`
    echo -n "" > $logfile.proof
    echo -n "" > $logfile.formula
    output=`timeout $time $binary $formula --opt-mode="lazy-hybrid" 2>&1 | awk '/^o|UNSATISFIABLE|.*Assertion.*/ {print $2}'`
    if [ "$output" != "" ] && [ "$output" != "$obj" ]; then
        errors=`expr 1000 + $errors`
        echo "wrong output: $output vs $obj"
    fi
    echo $errors
    tested=`expr 1 + $tested`
    echo $tested
    echo ""
done

echo "tested: $tested"
echo "errors: $errors"
