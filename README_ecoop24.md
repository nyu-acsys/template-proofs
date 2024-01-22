## Artifact for ECOOP'24 paper: Verifying Lock-free Search Structure Templates

### Getting Started Guide

This artifact relies on Iris (a high-order concurrent separation logic built on top of Coq). The artifact comes pre-installed with Coq/Iris and CoqIDE for evaluating the Coq proofs.

Navigate to the directory `ecoop24_artifact/templates`. Run the script `./xp_ecoop24.sh` to generate the data from Table 1 (Sec. 6) from the paper. The script is expected to run for ~10 minutes. Note that the line count for the code of the template algorithms is obtained manually from the Coq proof scripts. Hence, the relevant entries are filled with `?` in the generated rows.

### Setup Guide

For sake of completeness, we provide instructions on how to setup Coq/Iris for Debian/Ubuntu system. The following are the packages to be installed :

- OCaml, version 4.14.0 (or newer)

- OCaml Findlib, version 1.9.6 (or newer)

- ocamlbuild, version 0.14.2 (or newer)

- Coq, version 8.18.0

- Coq stdpp, version coq-stdpp.1.9.0

- Iris, version coq-iris.3.4.1

- Iris heap lang library, version coq-iris-heap-lang.3.4.1

The easiest way to satisfy all OCaml and Coq-related requirements is through the OCaml package manager OPAM.

#### Installing OPAM

```bash
sudo apt install opam
```

#### Setting up OPAM dependencies 

```bash
opam switch create 4.14.1
eval $(opam env)
opam install -y ocamlfind
opam install -y ocamlbuild
```

#### Installing Coq/CoqIDE

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y coq.8.18.0
opam install -y coqide.8.18.0
```

#### Installing Iris

```bash
opam install -y coq-iris.3.4.1
opam install -y coq-iris-heap-lang.3.4.1
eval $(opam config env)
```

### Contents

The Iris proofs are contained in `~/ecoop24_artifact/templates` directory. Its contents are described below:
    
+ util/ :
  - keyset_ra : Keyset camera definitions
  - gset_seq : Lemmas about converting a sequence of nats to gset
  - typed_proph.v : Typed prophecies
  - one_shot_proph.v: One-shot prophecies
  - misc_ra : Defining Booleans and Locations as Unital Discrete RAs
  - array_util : Lemmas about HeapLang array manipulations 
    
+ flows/ : Formalization of the flow framework
  - ccm.v : Commutative Cancelative Monoids, the basis for flow domains
  - ccm_big_op.v : Lemmas about iterated composition over CCM 
  - gmap_more.v : Lemmas about merge operation on finite maps.
  - flows.v : The flow framework and flow interfaces camera definitions
  - flows_big_op.v : Lemmas about iterated composition of flow interfaces
  - multiset_flows.v : Flow interface cameras of multisets over some arbitrary set
  - list_flow_upd.v : Flow update over unbounded list segments
  - list_flow_upd_marking.v : Flow update caused by marking a node
  - list_flow_upd_insert.v : Flow update caused by insert
  - list_flow_upd_unlink.v : Flow update caused by unlinking an unbounded marked segment

+ hindsight/ : Formalization of the hindsight reasoning in Iris (Sec. 4)
  - hindsight.v : Defines the shared state invariant offered by our proof method (Sec. 4.2)
  - hindsight_proof.v : Defines the Hindsight Spec and proves the client-level spec assuming the hindsight spec (Sec. 4.1)

+ lockfree/ : The skiplist template case study 
  - node_module.v : The node interface and helper function specs (Sec. 5.1)
  - traverse_module.v : The traverse interface (Sec. 2)
  - skiplist.v : The skiplist template (Sec. 2)
  - skiplist_util.v : Util for skiplist template proofs
  - traverse_spec_module : Specification of traverse assumed by the template (Sec 3, Sec. 5.2)
  - skiplist_delete_maintenance.v : Proof of maintenance operation of delete 
  - skiplist_delete.v : Proof of delete (Sec 3, Sec 5.2)
  - skiplist_insert_maintenance.v : Proof of maintenance operation of insert
  - skiplist_insert.v : Proof of insert (Sec 3, Sec 5.2)
  - skiplist_search.v : Proof of search (Sec 3, Sec 5.2)
  - skiplist_spec : Proof that skiplist template satisfied the hindsight spec; and initialization of the skiplist template (Sec 4.1, Sec 5.2)
  - eager : Eager traversal implementation and proof (Sec. 2, Sec 3.4)
  - lazy : Lazy traversal implementation and proof
  - node_impl1 : Node implementation that stores mark bit and the next pointer as a pair via indirection (Sec. 6)
  - node_impl2 : Node implementation that uses HeapLang data types to encode the mark bit (Sec. 6)

+ multicopy_hindsight/ : The multicopy template case study
  - lsm_node_module.v : The node interface and helper function specs
  - lsm.v : The LSM DAG template
  - lsm_util.v : Util for the multicopy template proofs
  - lsm_search.v : Proof of search
  - lsm_upsert.v : Proof of upsert
  - lsm_spec.v : Proof that multicopy template satisfies the hindsight spec
          
### Step-by-Step Evaluation Instructions

The proofs are verified by Iris/Coq. From the `templates/` directory, one can check individual files by running, for example:

```bash
coq_makefile -f _CoqProject -o Makefile
make lockfree/skiplist.vo
```

You can prefix the make command with e.g. `TIMED=true` in order to time each check, or `VERBOSE=true` in order to see the exact command being used. We suppress certain Coq warnings, but these are the same as the ones suppressed by Iris (see https://gitlab.mpi-sws.org/iris/iris/blob/master/_CoqProject).

You can verify that our Coq proof scripts have no "holes" in them by checking that they do not contain any `admit` or `Admitted` commands (except one admit in file `templates/multicopy_hindsight/lsm_spec`, see comment below).
 	
The artifact comes preinstalled with CoqIDE, a graphical tool to step through the coq proofs in a user-friendly manner. CoqIDE can be started by executing in terminal the command:

```bash
coqide
```
 	
### Paper-to-Artifact Correspondence Guide (and additional comments):

Below we list points that will make it easier to make the connection between the definitions in the paper and the artifact. We also list out the differences between the two.

* Success and Failure values returned by helper functions (Sec. 2) are encoded as return values of a CAS operation ((_, true), _) for Success and vice-versa).

* Upd(-) functions in Sec 4. is named process_proph in the proofs (hindsight.v). In the proofs, process_proph checks for result of successful resolution of CAS operation. Thus, it checks for values of the form ((_, b), _), where b is a boolean.

* The proofs assumes that the list of prophesied values comes with an end marker indicating the end of the operation. (We use the thread identifier as the end marker, a value of the form (_, tid)). The process_proph function checks for Success or Failure only before the end markers. As a result, the hindsight spec has to deal with an additional case where the list of prophesied values do not have an end marked. This end marker is the cause of difference between the hindsight spec in the paper versus the proof.

* Due to the complicated module structures, some predicates have long parameter lists. We are working towards finding a better approach.

* We do not verify the initialization of the multicopy template because [2] does not offer an initialization procedure for the multicopy template.

## Code Acknowledgement

* From [1], we borrow the formalization of flow interfaces and the keyset as Iris camera.

* From [2], we borrow the development on multiset flows.

* From `iris/examples` repository, we borrow code for array_util.v, typed_proph.v and one_shot.v

### References

[1] Siddharth Krishna, Alexander J. Summers, and Thomas Wies. 2020b.  Local Reasoning for Global Graph Properties. InProgramming Languages and Systems - 29th European Symposium on Programming, ESOP 2020, Held as Part of the EuropeanJoint Conferences on Theory and Practice of Software, ETAPS 2020, Dublin, Ireland, April 25-30, 2020, Proceedings (LectureNotes in Computer Science, Vol. 12075), Peter Müller (Ed.). Springer, 308–335.  https://doi.org/10.1007/978-3-030-44914-8_12

[2] Nisarg Patel, Siddharth Krishna, Dennis E. Shasha, and Thomas Wies. Verifying concurrent multicopy search structures. Proc. ACM Program. Lang., 5(OOPSLA):1–32, 2021.
