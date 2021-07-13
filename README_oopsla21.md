## Artifact for OOPSLA'21 submission: Verifying Concurrent Multicopy Structures

The artifact is packaged as a VirtualBox Image based on Ubuntu 20.04.2. The login is `templates:templates`.

### Getting Started Guide

This artifact relies on two tools: Iris (a high-order concurrent separation logic built on top of Coq) and GRASShopper (a program verification tool). The artifact is packaged with these software preinstalled and the necessary files precompiled. 

Navigate to the folder `~/oopsla21_artifact`. Run the script `./run_experiments.sh` to generate the data from Table 1 (Section 8) from the paper. The script is expected to run for ~9 minutes. Note that the line counts for the code of the templates are obtained manually from the Coq proof scripts. Hence the relevant entries are filled with `?` in the generated rows.

### Step-by-step Setup Guide

Before diving into details about how to use the tools packaged with the artifact, we first provide details below about how to reproduce the setup of the VirtualBox Image. The proofs contained in this artifact are available publicly at `https://github.com/nyu-acsys/template-proofs/tree/book`. Instructions below to generate the `oopsla21_artifact` directory:

```bash
sudo apt install git 			# ignore if git already installed
git clone https://github.com/nyu-acsys/template-proofs.git
cd template-proof
git checkout book
./create_oopsla_artifact.sh
``` 

Now let's set up the tools required by the artifact. The artifact has the following external dependencies:

- OCaml, version 4.07.1 (or newer)

- OCaml Findlib, version 1.8.1 (or newer)

- ocamlbuild, version 0.14.0 (or newer)

- Coq, version 8.13.1

- Coq stdpp, version coq-stdpp.1.5.0

- Iris, version coq-iris.3.4.0

- Iris heap lang library, version coq-iris-heap-lang.3.4.0

- GRASShopper, commit 5828de4d9a995e5b33197b837246929926fe4c5f.

- Z3, version >= 4.5

The easiest way to satisfy all OCaml and Coq-related requirements is through the OCaml package manager OPAM. We provide instructions for Linux below:

#### Installing OPAM

```bash
sudo apt install opam
```

#### Setting up OPAM dependencies 

```bash
opam switch create 4.07.1
eval $(opam env)
opam install -y ocamlfind
opam install -y ocamlbuild
```

#### Installing Coq/CoqIDE

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y coq.8.13.1
opam install -y coqide.8.13.1
```

#### Installing Iris

```bash
opam install -y coq-iris.3.4.0
opam install -y coq-iris-heap-lang.3.4.0
eval $(opam config env)
```

Note that OPAM might run into errors due to missing dependencies depending on your system. In that case, try again after installing the missing dependencies.

#### Installing GRASShopper

The easiest way to install GRASShopper is to navigate to the `oopsla21_artifact` directory, and execute the command

```bash
./setup.sh
```

The script will download and install the correct version of GRASShopper. Please make sure that Z3 is installed and the Z3 executable is in your PATH before running the script. 

Now your system has all the tools required to use the artifact.   

### Contents

The contents of `oopsla21_artifact` directory is described below:

+ templates/:
    The Iris proofs
    
  + util/:
    - lock.v:
        The implementation and proofs for node locking operations (Appx. A.6 - Fig 12) 
    - auth_ext.v:
        Assorted auxiliary lemmas for authoritative cameras
    - typed_proph.v:
        Typed prophecies
    - one_shot_proph.v:
        One-shot prophecies
        
  + flows/: (Sec. 6.2)
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
        Shared definitions for multicopy proofs (Sec. 4 - Fig. 5, Appx. A.4 - Fig 10) 
    - multicopy_util.v:
        Auxiliary utility lemmas for multicopy proofs
    - multicopy_client_level.v:
        Proofs relating client-level and template-level specs (Sec. 4, Appx. A.4)
    - multicopy_lsm.v:
        Shared definitions for LSM DAG template proofs (Appx. A.5)
    - multicopy_lsm_util.v:
        Auxiliary utility lemmas for template proofs
    - multicopy_lsm_search.v:
        Proof of LSM DAG search template (Sec. 6.1, Appx. A.6.1)
    - multicopy_lsm_upsert.v:
        Proof of LSM DAG upsert template (Sec. 6.1, Appx. A.6.2)
    - multicopy_lsm_compact.v
        Proof of LSM DAG compact template (Sec. 7, Appx. A.6.3)
    - multicopy_df.v:
    		Shared definitions for Differential Files(DF) template proofs
    - multicopy_df_search.v:
        Proof of DF search template
    - multicopy_df_upsert.v:
        Proof of DF upsert template
        
+ implementations/ (Sec. 8):
  The GRASShopper proofs of the LSM tree implementation
  - ordered_type.spl:
      An ordered type, used for the type of keys
  - array_basic.spl:
      Library of basic functions manipulating arrays
  - array_map.spl:
      Library of partial maps represented as arrays
  - multicopy_lsm.spl:
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

The artifact comes preinstalled with CoqIDE, a graphical tool to step through the coq proofs in a user-friendly manner. CoqIDE can be started by executing in terminal the command:

```bash
coqide
```

You can verify that our Coq proof scripts have no "holes" in them by checking that they do not contain any `admit` or `Admitted` commands. Our proofs make some assumptions about the implementation proofs checked by GRASShopper, but each of these are tagged as a `Parameter`. The assumption is either a helper function implementation or an implementation-dependent lemma of the same name checked by GRASShopper. See below for a complete list of such assumptions.

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

#### LSM DAG Template and Implementation

The LSM DAG template proof (`templates/multicopy/multicopy_lsm*.v`) makes the following assumptions on its implementation proof (`implementations/multicopy_lsm.spl`):

* Parameters `findNext`, `inContent`, and `addContents`:
  These are GRASShopper procedures in the implementation file. These procedure are used by the `search` and `upsert` operations.
* Parameters `atCapacity`, `chooseNext`, `mergeContents`, `allocNode` and `insertNode` :
  These are GRASShopper procedures in the implementation file, except for `mergeContents` and `allocNode`. These procedures are used by the `compact` operation. We do not anticipate any difficulty in extending the implementation proof to also support `mergeContents` and `allocNode`.
* Parameters `node`, `nodeSpatial` and `needsNewNode`:
  These are predicates that are defined in the implementation by macros of the same name.
* Parameters `node_sep_star`, `node_es_disjoint` and `node_es_empty`:
  These have GRASShopper lemmas of the same names, with proofs in the implementation file.
* Parameters `findNext_spec`, `inContent_spec`, `addContents_spec`:
  These are the specifications (pre and post-conditions, denoted by requires and ensures keywords) of the procedures used by `search` and `upsert`. These are checked manually to ensure that they match (modulo the different syntax for each tool).
* Parameters `atCapacity_spec`, `chooseNext_spec`, `mergeContents_spec`, `allocNode_spec` and `insertNode_spec` :
  These are the specifications of procedures used by the compact operation, manually checked to ensure that they match. 
 
#### Differential File Template

The Differential File template proof (`templates/multicopy/multicopy_df*.v`) makes the following assumptions:

* Parameters `findNext`, `inContent`, and `addContents`:
  These are helper functions used by the DF `search` and `upsert` operations.
* Parameters `node` and `nodeSpatial`:
  These are predicates that capture resources needed to implement nodes in a Differential File data structure. 
* Parameter `node_sep_star`:
	This predicate is an assumption on the implementation made by the template algorithm.
	
### Paper-to-Artifact Correspondence Guide:

Below we list points that will make it easier to make the connection between the definitions in the paper and the artifact.

* The artifact uses (and includes) the Coq formalization of the Flow Framework [1]. This files are contained in the directory templates/flows. 

* In Section 3.1, we define the contents of a node as finite map from KS to Timestamps, but we also alternately view contents as a set over KS x Timestamps. We also express the invariants with the notion of contents as a set (e.g., Invariant 3 in Sec. 6.1). In the artifact, the conversion between a set over KS x Timestamps and a map from KS to Timestamps is performed by the functions set_of_map and map_of_set in file multicopy.v in the directory templates/multicopy.

* The invariants presented as Iris formulae in the paper use ghost locations of the form γ(n) for a node n (e.g. γ_e(n) in predicate N_L in Fig. 11). This suggests that γ is a map from nodes to ghost locations. This map also needs to be explicitly stored in the invariant, however we do not present how exactly in the paper. As a result, the definition of an invariant in the artifact might contain an additional variable of type authoritative finite maps (gmaps in Iris standard library terms) to track this information. These variables are usually named hγ, hγt, etc in the artifact.

* The table below lists the discrepancies between the names used in the paper versus the artifact (also listed in the code appropriately).

    | Paper |  Artifact |
    | :---- | ---------: |
    | \overline{MCS} | MCS_high |
    | Inv | mcs |
    | \overline{search} | search' |
    | G | global_state |
    | N_L | nodePred |
    | N_S | nodeShared |

### References

[1] Siddharth Krishna, Alexander J. Summers, and Thomas Wies. 2020b.  Local Reasoning for Global Graph Properties. InProgramming Languages and Systems - 29th European Symposium on Programming, ESOP 2020, Held as Part of the EuropeanJoint Conferences on Theory and Practice of Software, ETAPS 2020, Dublin, Ireland, April 25-30, 2020, Proceedings (LectureNotes in Computer Science, Vol. 12075), Peter Müller (Ed.). Springer, 308–335.  https://doi.org/10.1007/978-3-030-44914-8_12
 


 	

