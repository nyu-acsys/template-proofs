## Artifact for ECOOP'21 submission: Verifying Concurrent Multicopy Structures

### Getting Started Guide

The artifact has the following external dependencies

- OCaml, version 4.07.1 (or newer)

- OCaml Findlib, version 1.8.1 (or newer)

- ocamlbuild, version 0.14.0 (or newer)

- Coq, version 8.12.2

- Coq stdpp, version coq-stdpp.dev.2020-12-11.0.881f2f38

- Iris, version coq-iris.dev.2020-12-19.0.58c1caae

- Iris heap lang library, version coq-iris-heap-lang.dev.2020-12-19.0.58c1caae

- GRASShopper, version pldi_2020.

- Z3, version >= 4.5

The easiest way to satisfy all OCaml and Coq-related requirements is to install the OCaml package manager OPAM and then execute the following commands

```bash
opam switch 4.07.1
opam install -y ocamlfind
opam install -y ocamlbuild
opam install -y coq
opam install -y coq-iris-heap-lang.dev.2020-12-19.0.58c1caae
eval $(opam config env)
```

For your convenience, you can download and install the correct GRASShopper version by executing the script

```bash
./setup.sh
```

Use the following script to generate the rows for Table 1 (Section 8 of the paper):

```bash
./run_experiments.sh
```

Please make sure that the Z3 executable is in your PATH. Also note that the line counts for the code of the templates are obtained manually from the Coq proof scripts. Hence the relevant entries are filled with `?` in the generated rows.

### Contents

+ templates/:
    The Iris proofs
    
  + util/:
    - lock.v:
        The implementation and proofs for node locking operations
    - auth_ext.v:
        Assorted auxiliary lemmas for authoritative cameras
    - typed_proph.v:
        Typed prophecies
    - one_shot_proph.v:
        One-shot prophecies
        
  + flows/:
    Formalization of the flow framework
    - ccm.v:
        Commutative Cancelative Monoids, the basis for flow domains
    - gmap_more.v:
        Extension of gmaps in stdpp (Coq standard library used by Iris)
    - flows.v:
        The flow framework and flow interfaces camera definitions
    - multiset_flows.v:
        Flow interface cameras of multisets over some arbitrary set
        
  + multicopy/:
    Multicopy structure proofs
    - multicopy.v:
        Shared definitions for multicopy proofs
    - multicopy_util.v:
        Auxiliary utility lemmas for multicopy proofs
    - multicopy_client_level.v:
        Proofs relating client-level and template-level specs (Sec. 4)
    - multicopy_lsm.v:
        Shared definitions for LSM DAG template proofs
    - multicopy_lsm_util.v:
        Auxiliary utility lemmas for template proofs
    - multicopy_lsm_search.v:
        Proof of search template
    - multicopy_lsm_upsert.v:
        Proof of upsert template
    - multicopy_lsm_compact.v
        Proof of compact template
        
+ implementations/:
  The GRASShopper proofs of the LSM tree implementation
  - ordered_type.spl:
      An ordered type, used for the type of keys
  - array_util.spl:
      Library of basic manipulations of arrays
  - multicopy-lsm.spl:
      The LSM tree implementation of the LSM DAG template 
  
- README.md:
     This file.
- setup.sh:
     A script to download and compile the correct GRASShopper version.
- run_experiments.sh:
     The script to re-run the experiments reported in our paper

### Step-by-Step Evaluation Instructions

Our artifact consists of two parts: the proofs of the Iris formalization, to be verified by Coq, and the proofs of the template implementation, to be verified by GRASShopper.


#### Iris Proofs

These proofs live in the `templates/multicopy` directory and are verified by Iris/Coq.
From the `templates/` directory, one can check individual files by running, for example:

```bash
coq_makefile -f _CoqProject -o Makefile
make multicopy/multicopy.vo
```

You can prefix the make command with e.g. `TIMED=true` in order to time each check, or `VERBOSE=true` in order to see the exact command being used. We suppress certain Coq warnings, but these are the same as the ones suppressed by Iris (see https://gitlab.mpi-sws.org/iris/iris/blob/master/_CoqProject).

You can verify that our Coq proof scripts have no "holes" in them by checking that they do not contain any `admit` or `Admitted` commands. Our proofs make some assumptions about the implementation proofs checked by GRASShopper, but each of these are tagged as either `Parameter` (for the helper function implementations) or `Hypothesis` (for an implementation-dependent lemma of the same name checked by GRASShopper). See below for a complete list of such assumptions.

Apart from these, we make the following assumptions in our Iris proofs:
`lockLoc`, `getLockLoc`, `getLockLoc_spec`, and `node_timeless_proof`. The first three assumptions are a way to talk about the lock field of each node that all GRASShopper implementations have. These assumptions are declared in the file `lock.v`. The assumption `node_timeless_proof` is justified because GRASShopper uses a first-order separation logic.


#### Implementation Proofs

These proofs live in the `implementations/` directory and are verified by GRASShopper.

From the `implementations/` directory, one can check individual implementation files by running, for example:

```bash
../grasshopper/grasshopper.native multicopy-lsm.spl -module multicopy-lsm
```

You can prefix the command with `time` in order to time each check, or append `-v` in order to see more verbose outputs.

You can verify that our GRASShopper proof scripts have no "holes" in them by checking that they contain no `assume` commands. 

