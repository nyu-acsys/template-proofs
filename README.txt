
Artifact for paper #756: Verifying Concurrent Search Structure Templates.


Getting Started Guide
=====================

TODO: how to run experiments. This will depend on VM.


Warning: line counts and times may differ because we've updated the proofs since submission, in order to reduce the unverified interface between the Coq and GRASShopper proofs. We have transferred the mechanization of the flow framework from GRASShopper to Coq. This also enables others to use flow-based reasoning in Iris proofs without having to rely on external proofs. We have also transferred many flow-domain-specific proofs to Coq.


Step-by-Step Evaluation Instructions
====================================

Our artifact consists of two parts: the proofs of template algorithms, to be verified by Iris/Coq, and the proofs of implementations, to be verified by GRASShopper.

TODO directory/file structure with what's where

Template Proofs
---------------

These proofs live in the templates/ directory and require Coq version >= TODO and Iris version >= TODO. The dependencies are already satisfied by this VM, but see file TODO for detailed installation instructions.

From the templates/ directory, one can check individual files by running, for example:

coq_makefile -f _CoqProject -o Makefile
make give_up.vo

You can prefix the make command with e.g. `TIMED=true` in order to time each check, or `VERBOSE=true` in order to see the exact command being used. We suppress certain Coq warnings, but these are the same as the ones suppressed by Iris (see https://gitlab.mpi-sws.org/iris/iris/blob/master/_CoqProject).

You can verify that our Coq proof scripts have no "holes" in them by checking that they do not contain any `admit` or `Admitted` commands. Our proofs make some assumptions about the implementation proofs checked by GRASShopper, but each of these are tagged as either `Parameter` (for the helper function implementations) or `Hypothesis` (for an implementation-dependent lemma of the same name checked by GRASShopper). See below for a complete list of such assumptions.

Apart from these, we make the following assumptions in our Iris proofs:
lockLoc, getLockLoc, getLockLoc_spec
node_timeless_proof, 


Implementation Proofs
---------------------

These proofs live in the implementations/ directory and require GRASShopper compiled from source (commit hash TODO). Again, this VM has a built version of GRASShopper but see TODO for build instructions.

From the implementations/ directory, one can check individual implementation files by running, for example:

grasshopper hashtbl-link.spl

You can prefix the command with `time` in order to time each check, or append `-v` in order to see more verbose outputs.

You can verify that our GRASShopper proof scripts have no "holes" in them by checking that they contain no `assume` commands, or procedures/lemmas with no bodies.


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

