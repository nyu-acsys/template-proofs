#!/bin/bash

timesfile=/tmp/times-iris
timestotalfile=/tmp/times-total-iris
locfile=/tmp/loc-iris
loctotalfile=/tmp/loc-total-iris
outputfile=/tmp/templates-table

fail=0

run()
{
    name="${1}"
    tabs=$((2 - ${#name} / 8))
    echo "\\hline" >> $outputfile
    echo -n "$name" >> $outputfile
    perl -E "print \"\t\" x $tabs" >> $outputfile
    shift
    rm -f $timesfile $locfile
    for f in $@ ; do
        # ignore comments and blank lines for line counting
        grep -v -e '^[[:space:]]*$' $f.v | grep -v -e "^[[:space:]]*(\*" | wc -l >> $locfile
        { TIMEFORMAT=%3R; time make $f.vo 2>&1 ; } 2>> $timesfile
        retcode=$?
        if [ $retcode -ne 0 ]; then
            fail=1
            echo -e "\nCoq exited with errors in file $f.v.\n"
        fi
        echo 1 >> $timesfile
    done
    awk '{sum+=$1;} END{printf("\t& ?\t& ?\t& %d", sum);}' $locfile >> $outputfile
    awk '{sum+=$1;} END{print sum;}' $locfile >> $loctotalfile
    awk '{sum+=$1;} END{printf("\t& %d\\\\\n", int(sum+0.5));}' $timesfile >> $outputfile
    awk '{sum+=$1;} END{printf("%d\n", int(sum+0.5));}' $timesfile >> $timestotalfile
}

eval $(opam env)
coq_makefile -f _CoqProject -o Makefile
make clean
rm -f $loctotalfile $timestotalfile $outputfile

echo -e "% Module\t\t& Code\t& Proof\t& Total\t& Time" >> $outputfile
run "Flow Library" "flows/gmap_more flows/ccm flows/ccm_big_op flows/flows flows/flows_big_op flows/multiset_flows flows/list_flow_upd"
run "Hindsight" "util/misc_ra util/one_shot_proph util/typed_proph util/gset_seq hindsight/hindsight"
run "Client-level Spec" "hindsight/hindsight_proof"
run "Skiplist" "util/keyset_ra lockfree/node_module lockfree/traverse_module lockfree/traverse_spec_module lockfree/skiplist lockfree/skiplist_util"
run "Skiplist Search" "lockfree/skiplist_search"
run "Skiplist Insert" "lockfree/skiplist_insert_maintenance flows/list_flow_upd_insert lockfree/skiplist_insert"
run "Skiplist Delete" "lockfree/skiplist_delete_maintenance flows/list_flow_upd_marking lockfree/skiplist_delete"
run "Skiplist Init" "lockfree/skiplist_spec"
run "Node-Impl1" "lockfree/node_impl1"
run "Node-Impl2" "lockfree/node_impl2"
run "Eager-traverse" "lockfree/eager"
run "Lazy-traverse" "flows/list_flow_upd_unlink lockfree/lazy"
#run "Multicopy Template" "multicopy_hindsight/lsm_node_module multicopy_hindsight/lsm multicopy_hindsight/lsm_util multicopy_hindsight/lsm_search multicopy_hindsight/lsm_upsert"


echo -e "\\hline" >> $outputfile
echo -n -e "Total\t\t" >> $outputfile
awk '{sum+=$1;} END{printf("\t& ?\t& ?\t& %d", sum);}' $loctotalfile >> $outputfile
awk '{sum+=$1;} END{printf("\t& %d\\\\\n", int(sum+0.5));}' $timestotalfile >> $outputfile

echo ""
cat $outputfile

if [ $fail -ne 0 ]; then
    exit 1
fi
