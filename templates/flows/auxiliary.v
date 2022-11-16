(** Theory of Commutative Cancelative Monoids (CCMs) *)

Require Import Coq.Logic.Decidable.

From iris Require Export base.
From stdpp Require Export decidable.
From stdpp Require Export gmap.
From stdpp Require Import mapset.
From stdpp Require Import finite.

Fixpoint k_combinations (k: nat) `{Countable A} (X: list A) : list (list A) :=
  match k with 
  | 0 => [[]]
  | S k' => 
    let fix inner l := 
      match l with
    | [] => []
    | x :: xs => map (λ z, x :: z) (k_combinations k' xs) :: inner xs end in 
    concat (inner X) end.
    
Compute k_combinations 2 [1;7;3;5].

(*
Fixpoint perm `{Countable A} (X: list A) : list (list A) :=
  match X with
  | [] => [[]]
  | x :: xs => 
    let fix insert a l :=
      match l with
      | [] => [[a]]
      | h :: t => (a::l) :: (map (λ el, h :: el) (insert a t)) end in
    concat (map (insert x) (perm xs)) end.
*)

Definition k_lists (k: nat) `{Countable A} (X: list A) : list (list A) := 
  let k_combs := k_combinations k X in
  concat (map (permutations) k_combs).
  
Compute k_lists 3 [1;4;7;2].   

(*
Definition k_enum (k: nat) : list nat :=
  let fix helper k acc :=
    match k with
    | 0 => acc
    | S k' => helper k' (k :: acc) end in
  helper k [].
*)

Definition k_enum (k: nat) := seq 1 k.

Compute k_enum 5.

Fixpoint alternating `{Countable A} (P Q: A → bool) (xs: list A) : bool :=
  match xs with
  | [] => true
  | x :: xs => P x && alternating Q P xs end.  
  

      
