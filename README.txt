
Artifact for paper #756: Verifying Concurrent Search Structure Templates.


Getting Started Guide
=====================

Our artifact is a VirtualBox VM distributed as a zip file (756.zip). To get started, unzip the file and import the enclosed ova file into VirtualBox. Boot up the VM, and use the following credentials to log in:

username: templates
password: templates

Once in the home directory, you can run all the experiments and reproduce the results of the paper by running the following scripts:

./update_files.sh  # optional; this updates proof scripts from our repository

./run_experiments.sh

The script will generate the rows for Table 1 (Section 4 of the paper).

Warning: line counts and times may differ from the original submission because we've updated the proofs since submission, in order to reduce the unverified interface between the Coq and GRASShopper proofs. We have transferred the mechanization of the flow framework from GRASShopper to Coq. This also enables others to use flow-based reasoning in Iris proofs without having to rely on external proofs. We have also transferred many flow-domain-specific proofs to Coq. Also note that the line counts for the code of the templates are obtained manually from the Coq proof scripts. Hence the relevant entries are filled with ? in the generated rows.

Contents of the VM
------------------

+ templates/:
     The Iris proofs of template algorithms
  - ccm.v:
        Commutative Cancelative Monoids, the basis for flow domains
  - gmap_more.v:
        Extension of gmaps in stdpp (Coq standard library used by Iris)
  - flows.v:
        The flow framework and flow interfaces camera definitions
  - inset_flows.v:
        Instantiation of flows used by give-up template
  - linkset_flows.v:
        Instantiation of flows used by link template
  - keyset_ra.v:
        The Keyset RA from Sec 4.2 of the paper
  - link.v:
        The link template algorithm and proof
  - give_up.v:
        The give-up template algorithm and proof
+ implementations/: (this is a symlink)
     The GRASShopper proofs of implementations
  - ccm.spl, multiset-ccm.spl, multipair-ccm.spl:
        CCM definition, and CCM instances used in implementations
  - flows.spl:
        Flow framework and flow interfaces definitions
  - ordered_type.spl:
        An ordered type, used for the type of keys
  - array_util.spl:
        Library of basic manipulations of arrays
  - give-up.spl:
        Common definitions across all give-up template implementations
  - link.spl:
        Common definitions across all link template implementations
  - b-link.spl:
        The B-link tree implementation of the link template
  - b+-tree.spl:
        The B+ tree implementation of the give-up template
  - hashtbl-give-up.spl:
        The hash table implementation of the give-up template
  - hashtbl-link.spl:
        The hash table implementation of the link template
+ update_files.sh:
     A script to update the above proof scripts from our repository
+ run_experiments.sh:
     The script to re-run the experiments reported in our paper
+ grasshopper/:
     GRASShopper source files and proof scripts


Step-by-Step Evaluation Instructions
====================================

Our artifact consists of two parts: the proofs of template algorithms, to be verified by Iris/Coq, and the proofs of implementations, to be verified by GRASShopper.


Template Proofs
---------------

These proofs live in the templates/ directory and were checked with Coq version 8.11 and Iris version dev.2020-02-28-0.a2f75cd0. These dependencies are already satisfied by the VM.

From the templates/ directory, one can check individual files by running, for example:

coq_makefile -f _CoqProject -o Makefile
make give_up.vo

You can prefix the make command with e.g. `TIMED=true` in order to time each check, or `VERBOSE=true` in order to see the exact command being used. We suppress certain Coq warnings, but these are the same as the ones suppressed by Iris (see https://gitlab.mpi-sws.org/iris/iris/blob/master/_CoqProject).

You can verify that our Coq proof scripts have no "holes" in them by checking that they do not contain any `admit` or `Admitted` commands. Our proofs make some assumptions about the implementation proofs checked by GRASShopper, but each of these are tagged as either `Parameter` (for the helper function implementations) or `Hypothesis` (for an implementation-dependent lemma of the same name checked by GRASShopper). See below for a complete list of such assumptions.

Apart from these, we make the following assumptions in our Iris proofs:
lockLoc, getLockLoc, getLockLoc_spec, and node_timeless_proof. The first three assumptions are a way to talk about the lock field of each node that all GRASShopper implementations have, and the final one is justified because GRASShopper uses a first-order separation logic.


Implementation Proofs
---------------------

These proofs live in the implementations/ directory and require GRASShopper compiled from source (branch pldi20). Again, the VM has a built version of GRASShopper but see ~/grasshopper/README.md for build instructions.

From the implementations/ directory, one can check individual implementation files by running, for example:

grasshopper hashtbl-link.spl -module hashtbl-link

You can prefix the command with `time` in order to time each check, or append `-v` in order to see more verbose outputs.

You can verify that our GRASShopper proof scripts have no "holes" in them by checking that they contain no `assume` commands. Note that there are some procedures/lemmas without bodies in ccm.spl. These should be interpreted as forward declarations that serve as axioms of the theory of CCMs.  The bodies (i.e. proofs) of these lemmas are then provided in multiset_ccm.spl and multipair_ccm.spl for the specific instantiations of the CCM theory.

Linking Templates and Implementations
-------------------------------------

The link template proof (templates/link.v) makes the following assumptions on its implementation proof (implementations/{hashtbl-link,b-link}.spl):

  - Parameter node:
    This is a predicate that is defined in each implementation by a macro of the same name.
  - Parameters findNext and decisiveOp:
    These are GRASShopper procedures in the implementation files. Note that decisiveOp is a placeholder for each of the three search structure operations: search, insert, and delete.
  - Parameters findNext_spec and decisiveOp_spec:
    These are the specifications (pre and post-conditions, denoted by requries and ensures keywords) of the procedures mentioned above. These are checked manually to ensure that they match (modulo the different syntax for each tool).
  - Hypotheses node_sep_star and node_implies_nodeinv:
    These have GRASShopper lemmas of the same names, with proofs in each implementation file.


The give-up template proof (templates/give_up.v) makes the following assumptions on its implementation proof (implementations/{hashtbl-give-up,b+-tree}.spl):

  - Parameter node:
    This is a predicate that is defined in each implementation by a macro of the same name.
  - Parameters findNext, inRange, and decisiveOp:
    These are GRASShopper procedures in the implementation files. Note that decisiveOp is a placeholder for each of the three search structure operations: search, insert, and delete.
  - Parameters findNext_spec, inRange_spec, and decisiveOp_spec:
    These are the specifications (pre and post-conditions, denoted by requries and ensures keywords) of the procedures mentioned above. These are checked manually to ensure that they match (modulo the different syntax for each tool).
  - Hypothesis node_sep_star:
    This has a GRASShopper lemmas of the same name, with a proof in each implementation file.

