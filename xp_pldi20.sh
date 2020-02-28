#!/bin/bash

FILES1="ccm flows inset_flows linkset_flows keyset_ra"
FILES2="give_up"
FILES3="link"

timesfile=/tmp/times-iris
locfile=/tmp/loc-iris

run()
{
    name="${1}"
    shift
    echo -n "$name"
    rm -f $timesfile $locfile
    for f in $@ ; do
        # ignore comments and blank lines for line counting
        grep -v -e '^[[:space:]]*$' $f.v | grep -v -e "^[[:space:]]*(\*" | wc -l >> $locfile
        { TIMEFORMAT=%3R; time make $f.vo > /dev/null ; } 2>> $timesfile
    done
    awk '{sum+=$1;} END{printf("\t& ?\t& ?\t& %d", sum);}' $locfile
    awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timesfile
}

make clean

echo -e "; Module\t& Code\t& Proof\t& Total\t& Time"
run "Flow library" $FILES1
run "Link template" $FILES3
run "Give-up tpl" $FILES2
