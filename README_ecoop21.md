## Artifact for ECOOP'21 paper: Verifying Concurrent Search Structure Templates

### Getting Started Guide

The artifact has the following external dependencies

- OCaml, version 4.07.1

- OCaml Findlib, version 1.8.1

- ocamlbuild, version 0.14.0

- Coq, version 8.11

- Coq stdpp, version coq-stdpp.dev.2020-03-18.1.846deb08

- Iris, version coq-iris.dev.2020-03-21.0.ed3b52f9

- GRASShopper, version pldi_2020.

- Z3, version >= 4.5

The easiest way to satisfy all OCaml and Coq-related requirements is to install the OCaml package manager OPAM and then execute the following commands

```bash
opam switch 4.07.1
opam install -y ocamlfind
opam install -y ocamlbuild
opam install -y coq
opam install -y coq-stdpp
opam install -y coq-iris
eval $(opam config env)
```

For your convenience, you can download and install the correct GRASShopper version by executing the script

```bash
./setup.sh
```

Use the following script to generate the rows for Table 1 (Section 4 of the paper):

```bash
./run_experiments.sh
```

Please make sure that the Z3 executable is in your PATH. Also note that the line counts for the code of the templates are obtained manually from the Coq proof scripts. Hence the relevant entries are filled with `?` in the generated rows.

### Contents

+ templates/:
     The Iris proofs of template algorithms
  - ccm.v:
        Commutative Cancelative Monoids, the basis for flow domains
  - gmap_more.v:
        Extension of gmaps in stdpp (Coq standard library used by Iris)
  - flows.v:
        The flow framework and flow interfaces camera definitions
  - auth_ext.v:
        Assorted auxiliary lemmas for authoritative RAs used by the template proofs
  - inset_flows.v:
        Instantiation of flows used by give-up and lock-coupling templates
  - linkset_flows.v:
        Instantiation of flows used by link template
  - keyset_ra.v:
        The Keyset RA from Sec 4.2 of the paper
  - lock.v:
        The implementation and proofs for node locking operations.
  - link.v:
        The link template algorithm and proof
  - give_up.v:
        The give-up template algorithm and proof
  - coupling_inv.v:
        The lock coupling template algorithm and proof
+ implementations/:
     The GRASShopper proofs of implementations
  - ccm.spl, multiset-ccm.spl:
        CCM definition, and CCM instances used in implementations
  - flows.spl, inset-flows.spl:
        Flow framework and flow interfaces definitions
  - ordered_type.spl:
        An ordered type, used for the type of keys
  - array_util.spl:
        Library of basic manipulations of arrays
  - b-link-core.spl:
        The B-link tree implementation of the link template
  - b-link-half.spl:
        The half split operation on B-link trees
  - b-link-full.spl:
        The full split operation on B-link trees
  - b+-tree.spl:
        The B+ tree implementation of the give-up template
  - hashtbl-give-up.spl:
        The hash table implementation of the give-up template
  - hashtbl-link.spl:
        The hash table implementation of the link template
  - lock-coupling.spl:
        Common definitions for lock coupling template implementations
  - list-coupling.spl:
        The list-based implementation of the lock coupling template
  
+ setup.sh:
     A script to download and compile the correct GRASShopper version.
+ run_experiments.sh:
     The script to re-run the experiments reported in our paper


### Step-by-Step Evaluation Instructions

Our artifact consists of two parts: the proofs of template algorithms, to be verified by Iris/Coq, and the proofs of implementations, to be verified by GRASShopper.


#### Template Proofs

These proofs live in the `templates/` directory and are verified by Iris/Coq.
From the `templates/` directory, one can check individual files by running, for example:

```bash
coq_makefile -f _CoqProject -o Makefile
make give_up.vo
```

You can prefix the make command with e.g. `TIMED=true` in order to time each check, or `VERBOSE=true` in order to see the exact command being used. We suppress certain Coq warnings, but these are the same as the ones suppressed by Iris (see https://gitlab.mpi-sws.org/iris/iris/blob/master/_CoqProject).

You can verify that our Coq proof scripts have no "holes" in them by checking that they do not contain any `admit` or `Admitted` commands. Our proofs make some assumptions about the implementation proofs checked by GRASShopper, but each of these are tagged as either `Parameter` (for the helper function implementations) or `Hypothesis` (for an implementation-dependent lemma of the same name checked by GRASShopper). See below for a complete list of such assumptions.

Apart from these, we make the following assumptions in our Iris proofs:
`lockLoc`, `getLockLoc`, `getLockLoc_spec`, and `node_timeless_proof`. The first three assumptions are a way to talk about the lock field of each node that all GRASShopper implementations have. These assumptions are declared in the file `lock.v`. The assumption `node_timeless_proof` is justified because GRASShopper uses a first-order separation logic.


#### Implementation Proofs

These proofs live in the `implementations/` directory and are verified by GRASShopper.

From the `implementations/` directory, one can check individual implementation files by running, for example:

```bash
../grasshopper/grasshopper.native hashtbl-link.spl -module hashtbl-link
```

You can prefix the command with `time` in order to time each check, or append `-v` in order to see more verbose outputs.

You can verify that our GRASShopper proof scripts have no "holes" in them by checking that they contain no `assume` commands. Note that there are some procedures/lemmas without bodies in ccm.spl. These should be interpreted as forward declarations that serve as axioms of the theory of CCMs.  The bodies (i.e. proofs) of these lemmas are then provided in `multiset_ccm.spl` and `multipair_ccm.spl` for the specific instantiations of the CCM theory.

#### Linking Templates and Implementations

The link template proof (`templates/link.v`) makes the following assumptions on its implementation proof (`implementations/{hashtbl-link,b-link}.spl`):

* Parameter `node`:
  This is a predicate that is defined in each implementation by a macro of the same name.
* Parameters `findNext` and `decisiveOp`:
  These are GRASShopper procedures in the implementation files. Note that `decisiveOp` is a placeholder for each of the three search structure operations: search, insert, and delete.
* Parameters `findNext_spec` and `decisiveOp_spec`:
  These are the specifications (pre and post-conditions, denoted by requires and ensures keywords) of the procedures mentioned above. These are checked manually to ensure that they match (modulo the different syntax for each tool).
* Hypotheses `node_sep_star` and `node_implies_nodeinv`:
  These have GRASShopper lemmas of the same names, with proofs in each implementation file.

The give-up template proof (`templates/give_up.v`) makes the following assumptions on its implementation proof (`implementations/{hashtbl-give-up,b+-tree}.spl`):

* Parameter `node`:
  This is a predicate that is defined in each implementation by a macro of the same name.
* Parameters `findNext`, `inRange`, and `decisiveOp`:
  These are GRASShopper procedures in the implementation files. Note that `decisiveOp` is a placeholder for each of the three search structure operations: search, insert, and delete.
* Parameters `findNext_spec`, `inRange_spec`, and `decisiveOp_spec`:
  These are the specifications (pre and post-conditions, denoted by requires and ensures keywords) of the procedures mentioned above. These are checked manually to ensure that they match (modulo the different syntax for each tool).
* Hypothesis `node_sep_star` and `node_implies_nodeinv`:
  These have GRASShopper lemmas of the same name, with proofs in each implementation file.
