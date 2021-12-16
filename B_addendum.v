(*
Additional material
===================
*)

From local Require Import A_completeness.
From stdpp Require Import list.

(*
This is a variant of f_big that produces a pretty formula: the default formula
is only used when ps is empty, and the formula associates to the left.
*)
Definition f_big_pretty {X} c (d : form X) ps :=
  match ps with
  | [] => d
  | [p] => p
  | p :: qs => foldl (f_Conn c) p qs
  end.

Notation "`⋀` fs" := (f_big_pretty Conj ⊤ fs) (at level 57).
  
(*
As an exercise, I wanted to develop more advanced tactics that can select a
hypothesis clause using its index to revert or apply it. The first step is to
extract clauses as a list, 
*)
Section Clause_extraction.

Fixpoint extract_clauses (f : form term) : list (form term) :=
  match f with
  | p `∧` q => extract_clauses p ++ extract_clauses q
  | p => [p]
  end.

Lemma d_normalize_clauses f :
  f ⊣⊢ `⋀` extract_clauses f.
Proof.
Admitted.

Lemma d_big_pretty_conj_subseteq ps qs :
  qs ⊆ ps -> `⋀` ps ⊢ `⋀` qs.
Proof.
Admitted.

Lemma d_select_clause n ps :
  `⋀` ps ⊢ `⋀` (take n ps ++ drop (S n) ps ++ take 1 (drop n ps)).
Proof.
apply d_big_pretty_conj_subseteq; intros p.
rewrite ?elem_of_app, <-Nat.add_1_r, <-drop_drop.
rewrite (or_comm (p ∈ drop _ _) _).
rewrite <-?elem_of_app, ?take_drop; done.
Qed.

End Clause_extraction.
