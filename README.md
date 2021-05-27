## Automated Verification of Concurrent Search Structures

This artifact contains the mechanized proofs described in the book 

Krishna, S., Patel, N., Shasha, D., & Wies, T. (2021). *Automated Verification of Concurrent Search Structures*. Synthesis Lectures on Computer Science. Morgan & Claypool.

For the most recent version of this artifact, please visit:

https://github.com/nyu-acsys/template-proofs/

### Getting Started Guide

The artifact has the following external dependencies

- OCaml, version 4.07.1 (or newer)

- OCaml Findlib, version 1.8.1 (or newer)

- ocamlbuild, version 0.14.0 (or newer)

- Coq, version 8.13.1

- Coq stdpp, version coq-stdpp.1.5.0

- Iris, version coq-iris.3.4.0

- Iris heap lang library, version coq-iris-heap-lang.3.4.0

- GRASShopper, commit 5828de4d9a995e5b33197b837246929926fe4c5f.

- Z3, version >= 4.5

The easiest way to satisfy all OCaml and Coq-related requirements is to install the OCaml package manager OPAM and then execute the following commands

```bash
opam switch 4.07.1
opam install -y ocamlfind
opam install -y ocamlbuild
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y coq.8.13.1
opam install -y coq-iris.3.4.0
opam install -y coq-iris-heap-lang.3.4.0
eval $(opam config env)
```

For your convenience, you can download and install the correct GRASShopper version by executing the script

```bash
./setup.sh
```

Use the following script to generate the rows for Table 13.1 of the book:

```bash
./run_experiments_book.sh
```

Please make sure that the Z3 executable is in your PATH. Also note that the line counts for the code of the templates are obtained manually from the Coq proof scripts. Hence the relevant entries are filled with `?` in the generated rows.

### Contents

+ templates/:
    The Iris proofs
    
  + util/:
    - lock.v:
        The implementation and proofs for node locking operations (Chp 2)
    - auth_ext.v:
        Assorted auxiliary lemmas for authoritative cameras
    - typed_proph.v:
        Typed prophecies
    - one_shot_proph.v:
        One-shot prophecies
        
  + flows/:
    Formalization of the flow framework (Chp 7)
    - ccm.v:
        Commutative Cancelative Monoids, the basis for flow domains
    - gmap_more.v:
        Extension of gmaps in stdpp (Coq standard library used by Iris)
    - flows.v:
        The flow framework and flow interfaces camera definitions
    - multiset_flows.v:
        Flow interface cameras of multisets over some arbitrary set

  + single_copy/:
    Single-copy structure proofs
	  - inset_flows.v:
        Instantiation of flows to encode keysets (Chp 7) 
	  - keyset_ra.v:
        The Keyset RA (from Chp 5)
    - search_str.v:
        Abstract specification of search structure operations (Chp 3)
	  - single_node.v:
        The single-node template algorithm and proof (Chp 2)
	  - two_node.v:
        The two-node template algorithm and proof (Chp 5)
	  - link.v:
        The link template algorithm and proof (Chp 8)
	  - give_up.v:
        The give-up template algorithm and proof (Chp 8)
	  - coupling_inv.v:
        The lock coupling template algorithm and proof (Chp 8)
        
  + multicopy/:
    Multicopy structure proofs
    - multicopy.v:
        Shared definitions for multicopy proofs (Chp 9)
    - multicopy_util.v:
        Auxiliary utility lemmas for multicopy proofs
    - multicopy_client_level.v:
        Proofs relating client-level and template-level specs (Chp 11)
    - multicopy_lsm.v:
        Shared definitions for LSM DAG template proofs (Chp 12)
    - multicopy_lsm_util.v:
        Auxiliary utility lemmas for template proofs
    - multicopy_lsm_search.v:
        Proof of LSM DAG search template (Chp 12)
    - multicopy_lsm_upsert.v:
        Proof of LSM DAG upsert template (Chp 12)
    - multicopy_lsm_compact.v
        Proof of LSM DAG compact template (Chp 12)
    - multicopy_df.v:
    		Shared definitions for Differential Files(DF) template proofs (Chp 9)
    - multicopy_df_search.v:
        Proof of DF search template
    - multicopy_df_upsert.v:
        Proof of DF upsert template

+ implementations/:
     The GRASShopper proofs of implementations
  - ccm.spl, multiset-ccm.spl:
        CCM definition, and CCM instances used in implementations (Chp 7)
  - flows.spl, inset-flows.spl:
        Flow framework and flow interfaces definitions (Chp 7)
  - ordered_type.spl:
        An ordered type, used for the type of keys
  - array_util.spl:
        Library of basic manipulations of arrays
  - b-link-core.spl:
        The B-link tree implementation of the link template (Chp 8)
  - b-link-half.spl:
        The half split operation on B-link trees (Chp 8)
  - b-link-full.spl:
        The full split operation on B-link trees (Chp 8)
  - b+-tree.spl:
        The B+ tree implementation of the give-up template (Chp 8)
  - hashtbl-give-up.spl:
        The hash table implementation of the give-up template (Chp 8)
  - hashtbl-link.spl:
        The hash table implementation of the link template (Chp 8)
  - lock-coupling.spl:
        Common definitions for lock coupling template implementations (Chp 8)
  - list-coupling.spl:
        The list-based implementation of the lock coupling template (Chp 8)
  - multicopy-lsm.spl:
      The LSM tree implementation of the LSM DAG template (Chp 12)

- README.md:
     This file.
+ setup.sh:
     A script to download and compile the correct GRASShopper version.
+ run_experiments_book.sh:
     The script to re-run the experiments reported in the book.


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

You can verify that our GRASShopper proof scripts have no "holes" in them by checking that they contain no `assume` commands. Note that there are some procedures/lemmas without bodies in ccm.spl. These should be interpreted as forward declarations that serve as axioms of the theory of CCMs.  The bodies (i.e. proofs) of these lemmas are then provided in `multiset_ccm.spl` for the specific instantiations of the CCM theory.

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

The lock-coupling template proof (`templates/coupling.v`) makes the following assumptions on its implementation proof (`implementations/{list-coupling}.spl`):

* Parameter `node`:
  This is a predicate that is defined in each implementation by a macro of the same name.
* Parameters `allocRoot`, `findNext`, `inRange`, and `decisiveOp`:
  These are GRASShopper procedures in the implementation files. Note that `decisiveOp` is a placeholder for each of the three search structure operations: search, insert, and delete.
* Parameters `allocRoot_spec`, `findNext_spec`, `inRange_spec`, and `decisiveOp_spec`:
  These are the specifications (pre and post-conditions, denoted by requires and ensures keywords) of the procedures mentioned above. These are checked manually to ensure that they match (modulo the different syntax for each tool).
* Hypothesis `node_sep_star` and `node_implies_nodeinv`:
  These have GRASShopper lemmas of the same name, with proofs in each implementation file.

  
The LSM DAG template proof (`templates/multicopy/multicopy_lsm*.v`) makes the following assumptions on its implementation proof (`implementations/multicopy-lsm.spl`):

* Parameters `node`, `nodeSpatial` and `needsNewNode`:
  These are predicates that are defined in the implementation by macros of the same name.
* Parameters `findNext`, `inContent`, and `addContents`:
  These are GRASShopper procedures in the implementation file. These procedure are used by the `search` and `upsert` operations.
* Parameters `atCapacity`, `chooseNext`, `mergeContents`, `allocNode` and `insertNode` :
  These are GRASShopper procedures in the implementation file, except for `mergeContents` and `allocNode`. These procedures are used by the `compact` operation. We do not anticipate any difficulty in extending the implementation proof to also support `mergeContents` and `allocNode`.
* Parameters `findNext_spec`, `inContent_spec`, `addContents_spec`:
  These are the specifications (pre and post-conditions, denoted by requires and ensures keywords) of the procedures used by `search` and `upsert`. These are checked manually to ensure that they match (modulo the different syntax for each tool).
* Parameters `atCapacity_spec`, `chooseNext_spec`, `mergeContents_spec`, `allocNode_spec` and `insertNode_spec` :
  These are the specifications of procedures used by the compact operation, manually checked to ensure that they match. 
* Parameters `node_sep_star`, `node_es_disjoint` and `node_es_empty`:
  These have GRASShopper lemmas of the same names, with proofs in the implementation file.

The Differential File template proof (`templates/multicopy/multicopy_df*.v`) makes the following assumptions:

* Parameters `findNext`, `inContent`, and `addContents`:
  These are helper functions used by the DF `search` and `upsert` operations.
* Parameters `node` and `nodeSpatial`:
  These are predicates that capture resources needed to implement nodes in a Differential File data structure. 
* Parameter `node_sep_star`:
	This predicate is an assumption on the implementation made by the template algorithm.
