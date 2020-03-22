#!/bin/bash

FILES1="ccm flows inset_flows linkset_flows keyset_ra"
FILES2="give_up"
FILES3="link"
FILES4="coupling_inv"

timesfile=/tmp/times-iris
timestotalfile=/tmp/times-total-iris
locfile=/tmp/loc-iris
loctotalfile=/tmp/loc-total-iris
outputfile=/tmp/templates-table

run()
{
    name="${1}"
    tabs=$((2 - ${#name} / 8))
    echo -n "$name" >> $outputfile
    perl -E "print \"\t\" x $tabs" >> $outputfile
    shift
    rm -f $timesfile $locfile
    for f in $@ ; do
        # ignore comments and blank lines for line counting
        grep -v -e '^[[:space:]]*$' $f.v | grep -v -e "^[[:space:]]*(\*" | wc -l >> $locfile
        { TIMEFORMAT=%3R; time make $f.vo 2>&1 ; } 2>> $timesfile
        echo 1 >> $timesfile
    done
    awk '{sum+=$1;} END{printf("\t& ?\t& ?\t& %d", sum);}' $locfile >> $outputfile
    awk '{sum+=$1;} END{print sum;}' $locfile >> $loctotalfile
    awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timesfile >> $outputfile
    awk '{sum+=$1;} END{printf("%d\n", int(sum+0.5));}' $timesfile >> $timestotalfile
}

coq_makefile -f _CoqProject -o Makefile
make clean
rm -f $loctotalfile $timestotalfile $outputfile

echo -e "; Module\t\t& Code\t& Proof\t& Total\t& Time" >> $outputfile
run "Flow library" $FILES1
run "Link template" $FILES3
run "Give-up template" $FILES2
run "Lock-coupling template" $FILES4

echo -n -e "Total\t\t" >> $outputfile
awk '{sum+=$1;} END{printf("\t& ?\t& ?\t& %d", sum);}' $loctotalfile >> $outputfile
awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timestotalfile >> $outputfile

echo ""
cat $outputfile
