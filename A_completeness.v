(*
A Complete Proof System for the Later Modality
==============================================
*)

Require Import Nat Compare_dec.
From stdpp Require Import gmap list.

Section Generic_utilities.

Fixpoint adj {X} (xs : list X) :=
  match xs with
  | [] => []
  | [_] => []
  | x :: (y :: _) as xs' => (x, y) :: adj xs'
  end.

Lemma adj_cons {X} (x0 x1 : X) xs :
  adj (x0 :: x1 :: xs) = (x0, x1) :: adj (x1 :: xs).
Proof.
done.
Qed.

Lemma adj_fmap {X Y} (f : X -> Y) xs :
  adj (f <$> xs) = (λ p, (f (fst p), f (snd p))) <$> adj xs.
Proof.
induction xs; simpl. done.
destruct xs; simpl in *. done.
rewrite IHxs; done.
Qed.

Lemma in_seq_iff start n len :
  n ∈ seq start len <-> start ≤ n < start + len.
Proof.
rewrite elem_of_list_In; apply in_seq.
Qed.

Lemma subseteq_mbind {X Y} (f : X -> list Y) x (xs : list X) :
  x ∈ xs -> f x ⊆ xs ≫= f.
Proof.
intros H y Hy; apply elem_of_list_bind; exists x; done.
Qed.

Lemma subseteq_fmap {X Y} (f : X -> Y) (l l' : list X) :
  l ⊆ l' -> f <$> l ⊆ f <$> l'.
Proof.
intros H y Hy. apply elem_of_list_fmap in Hy as (x & -> & Hx).
apply elem_of_list_fmap; exists x; auto.
Qed.

Lemma elem_of_list_mapM {X Y} xs ys (f : X -> list Y) :
  ys ∈ mapM f xs <-> Forall2 (λ y x, y ∈ f x) ys xs.
Proof.
revert ys; induction xs; simpl; intro ys; split; intro H.
- apply elem_of_list_ret in H as ->; apply Forall2_nil; done.
- apply Forall2_nil_inv_r in H as ->; apply elem_of_list_ret; done.
- apply elem_of_list_bind in H as (y & H1 & H2).
  apply elem_of_list_bind in H1 as (ys' & H3 & H4).
  apply elem_of_list_ret in H3 as ->.
  apply Forall2_cons; split. done.
  apply IHxs, H4.
- inversion H; subst; clear H.
  apply elem_of_list_bind; exists x; split; [|done].
  apply elem_of_list_bind; exists l; split.
  apply elem_of_list_ret; done. apply IHxs, H4.
Qed.

End Generic_utilities.

Inductive term := t_Const (b : bool) | t_Var (i : nat).
Inductive connective := Conj | Disj | Impl.
Inductive form (X : Type) :=
  | f_Term (x : X)
  | f_Later (p : form X)
  | f_Conn (c : connective) (p q : form X).

Arguments f_Term {_}.
Arguments f_Later {_}.
Arguments f_Conn {_}.

Definition f_later {X} n (f : form X) := Nat.iter n f_Later f.
Definition f_big {X} c (d : form X) fs := foldr (f_Conn c) d fs.

Fixpoint FV (f : form term) : gset nat :=
  match f with
  | f_Term (t_Var i) => {[ i ]}
  | f_Term _ => ∅
  | f_Later p => FV p
  | f_Conn _ p q => FV p ∪ FV q
  end.

Fixpoint MD (f : form term) :=
  match f with
  | f_Term _ => 0
  | f_Later p => S (MD p)
  | f_Conn _ p q => max (MD p) (MD q)
  end.

Global Instance fmap_form : FMap form :=
  λ X Y f, fix rec (r : form X) :=
    match r with
    | f_Term x => f_Term (f x)
    | f_Later p => f_Later (rec p)
    | f_Conn c p q => f_Conn c (rec p) (rec q)
    end.

Notation "⊤" := (f_Term (t_Const true)).
Notation "⊥" := (f_Term (t_Const false)).
Notation "$ x" := (f_Term x) (at level 40, format "$ x").
Notation "# i" := (f_Term (t_Var i)) (at level 40, format "# i").
Notation "▷ p" := (f_Later p) (at level 49, right associativity, format "▷ p").
Notation "n *▷ p" := (f_later n p) (at level 50).
Notation "p `∧` q" := (f_Conn Conj p q) (at level 56, left associativity).
Notation "p `∨` q" := (f_Conn Disj p q) (at level 56, left associativity).
Notation "p ⟹ q" := (f_Conn Impl p q) (at level 54, right associativity).
Notation "p ⟺ q" := (p ⟹ q `∧` q ⟹ p) (at level 54).
Notation "⋀ fs" := (f_big Conj ⊤ fs) (at level 57).
Notation "⋁ fs" := (f_big Disj ⊥ fs) (at level 57).

(*
The sequent could be replaced with an implication, e.g. we could write something
like ⊢ p ⟹ q instead of p ⊢ q. But there are some advantages of using a sequent
relation: (1) Automation: this gives setoid rewriting and a pre-order instance.
(2) Readability: the sequent avoids parentheses in some cases, and creates a
clear separation between hypothesis and goal.

This treatment of natural deduction is not completely rigorous. We do not use
lists to store the context, but a single formula (this started as an experiment,
but at this point going back requires too much work). We do not prove a
deduction theorem, but include transitivity as an axiom.
*)

Reserved Notation "p ⊢ q" (at level 70).
Reserved Notation "⊢ q" (at level 70).

Inductive deduction : form term -> form term -> Prop :=
  | d_refl p             : p ⊢ p
  | d_trans p q r        : p ⊢ q -> q ⊢ r -> p ⊢ r
  | d_true_intro p       : p ⊢ ⊤
  | d_false_elim p       : ⊥ ⊢ p
  | d_conj_intro c p q   : c ⊢ p -> c ⊢ q -> c ⊢ p `∧` q
  | d_conj_elim_l p q    : p `∧` q ⊢ p
  | d_conj_elim_r p q    : p `∧` q ⊢ q
  | d_disj_intro_l p q   : p ⊢ p `∨` q
  | d_disj_intro_r p q   : q ⊢ p `∨` q
  | d_disj_elim c p q r  : c ⊢ p `∨` q -> c `∧` p ⊢ r -> c `∧` q ⊢ r -> c ⊢ r
  | d_impl_intro c p q   : c `∧` p ⊢ q -> c ⊢ p ⟹ q
  | d_impl_elim c p q    : c ⊢ p ⟹ q -> c ⊢ p -> c ⊢ q
  | d_later_intro p      : p ⊢ ▷p
  | d_later_elim p       : ⊢ ▷p -> ⊢ p
  | d_later_fix p        : ▷p ⊢ p -> ⊢ p
  | d_later_mono p q     : p ⊢ q -> ▷p ⊢ ▷q
  | d_later_conj p q     : ▷p `∧` ▷q ⊢ ▷(p `∧` q)
  | d_compare p q        : ⊢ p ⟹ q `∨` ▷q ⟹ p
where "p ⊢ q" := (deduction p q) and "⊢ q" := (⊤ ⊢ q).
Notation "p ⊣⊢ q" := (p ⊢ q /\ q ⊢ p) (at level 71).

Ltac inv H := inversion H; subst; clear H.
Ltac cut x := transitivity x.
Ltac ecut := etransitivity.
Ltac refl := reflexivity.
Ltac d_split := apply d_conj_intro.
Ltac d_intro := apply d_impl_intro.
Ltac d_mp := eapply d_impl_elim.
Ltac d_apply_l H := ecut; [eapply H|].
Ltac d_apply_r H := ecut; [|eapply H].
Ltac d_left := d_apply_r d_disj_intro_l.
Ltac d_right := d_apply_r d_disj_intro_r.

Global Instance d_pre_order :
  PreOrder deduction.
Proof.
split. intros p; apply d_refl.
intros p q r; apply d_trans.
Defined.

Lemma d_clr p q : ⊢ q -> p ⊢ q.
Proof. d_apply_l d_true_intro; done. Qed.

Lemma d_clr_l c p q : c ⊢ q -> p `∧` c ⊢ q.
Proof. d_apply_l d_conj_elim_r; done. Qed.

Lemma d_clr_r c p q : c ⊢ q -> c `∧` p ⊢ q.
Proof. d_apply_l d_conj_elim_l; done. Qed.

Ltac clr := apply d_clr.
Ltac clr_l := apply d_clr_l.
Ltac clr_r := apply d_clr_r.
Ltac d_hyp := refl || (clr_l; d_hyp) || (clr_r; d_hyp).

Lemma d_conj_comm p q : p `∧` q ⊢ q `∧` p.
Proof. d_split; d_hyp. Qed.

Lemma d_conj_assoc p q r : (p `∧` q) `∧` r ⊣⊢ p `∧` (q `∧` r).
Proof. split; repeat d_split; d_hyp. Qed.

Lemma d_impl_revert c p q : c ⊢ p ⟹ q -> c `∧` p ⊢ q.
Proof. intros; d_mp; [clr_r; done|clr_l; done]. Qed.

Lemma d_impl_revert_top p q : ⊢ p ⟹ q -> p ⊢ q.
Proof. intros; d_mp; [clr; done|refl]. Qed.

Ltac d_comm := d_apply_l d_conj_comm.
Ltac d_assoc := d_apply_l d_conj_assoc.
Ltac d_revert := apply d_impl_revert || apply d_impl_revert_top.

Section Deductions.

Implicit Types p q : form term.

Lemma d_strong_fix p :
  ▷p ⟹ p ⊢ p.
Proof.
d_mp; [clr|refl].
eapply d_later_fix.
d_intro; d_mp; [d_hyp|].
d_comm; d_revert.
d_apply_l d_later_intro.
d_intro; d_apply_l d_later_conj.
apply d_later_mono; d_mp; d_hyp.
Qed.

Lemma d_later_impl p q :
  ▷p ⟹ ▷q ⊢ ▷(p ⟹ q).
Proof.
eapply d_disj_elim.
clr; apply d_compare with (p:=p)(q:=q).
d_apply_r d_later_intro; d_hyp. cut (▷q). d_mp. d_hyp.
d_apply_r d_later_intro; d_apply_r d_strong_fix.
d_intro; d_mp; [d_hyp|]; d_mp; d_hyp.
apply d_later_mono; d_intro; d_hyp.
Qed.

Lemma d_later_inj p q :
  ▷p ⊢ ▷q -> p ⊢ q.
Proof.
intros; d_mp; [clr|refl]. apply d_later_elim.
d_apply_r d_later_impl. d_intro; clr_l; done.
Qed.

Lemma d_compare_weak p q :
  ⊢ p ⟹ q `∨` q ⟹ p.
Proof.
eapply d_disj_elim.
clr; apply d_compare with (p:=p)(q:=q).
d_left; d_hyp. d_right; d_intro; d_mp.
d_hyp. d_apply_r d_later_intro; d_hyp.
Qed.

Lemma d_disj_elim_inline p q r :
  p ⊢ r -> q ⊢ r -> p `∨` q ⊢ r.
Proof.
intros; eapply d_disj_elim. done.
all: clr_l; done.
Qed.

Lemma d_big_conj_intro c ps :
  (∀ p, p ∈ ps -> c ⊢ p) -> c ⊢ ⋀ ps.
Proof.
induction ps; simpl; intros. clr; done.
apply d_conj_intro. apply H, elem_of_list_here.
apply IHps; intros; apply H, elem_of_list_further, H0.
Qed.

Lemma d_big_conj_elim p ps :
  p ∈ ps -> ⋀ ps ⊢ p.
Proof.
induction ps; simpl; intros.
apply elem_of_nil in H; done.
inv H. d_hyp. clr_l; apply IHps, H2.
Qed.

Lemma d_big_disj_intro p ps :
  p ∈ ps -> p ⊢ ⋁ ps.
Proof.
induction ps; simpl; intros.
apply not_elem_of_nil in H; done.
inv H; [d_left|d_right]. done. auto.
Qed.

Lemma d_big_disj_elim ps q :
  (∀ p, p ∈ ps -> p ⊢ q) -> ⋁ ps ⊢ q.
Proof.
induction ps; simpl; intros. constructor.
eapply d_disj_elim. done. all: clr_l.
apply H; left; done.
apply IHps; intros.
apply H; right; done.
Qed.

Lemma d_big_disj_subseteq ps qs :
  ps ⊆ qs -> ⋁ ps ⊢ ⋁ qs.
Proof.
intros; apply d_big_disj_elim; intros.
d_apply_r d_big_disj_intro. done. auto.
Qed.

Lemma d_big_disj_conj_swap {X} (f : X -> list (form term)) (xs : list X) :
  ⋀ ((λ x, ⋁ f x) <$> xs) ⊢ ⋁ ((λ c, ⋀ c) <$> mapM f xs).
Proof.
induction xs. simpl; d_left; done.
ecut. apply d_conj_intro.
clr_r; done. clr_l; apply IHxs.
d_revert; apply d_big_disj_elim; intros p Hp; d_intro.
d_comm; d_revert; apply d_big_disj_elim; intros q Hq; d_intro.
apply elem_of_list_fmap in Hq as (qs & -> & Hqs).
d_apply_r d_big_disj_intro. d_comm; done.
apply elem_of_list_fmap; exists (p :: qs); simpl; split. done. 
apply elem_of_list_bind; exists p; split; [|done].
apply elem_of_list_bind; exists qs; split; [|done].
apply elem_of_list_ret; done.
Qed.

Lemma d_iff_refl p :
  ⊢ p ⟺ p.
Proof.
d_split; d_intro; d_hyp.
Qed.

Lemma d_iff_symm p q :
  p ⟺ q ⊢ q ⟺ p.
Proof.
d_split; d_hyp.
Qed.

Lemma d_iff_trans p q r :
  p ⟺ q `∧` q ⟺ r ⊢ p ⟺ r.
Proof.
d_split; d_intro; d_mp; try d_hyp; d_mp.
clr_r; clr_r; d_hyp. d_hyp.
clr_r; clr_l; d_hyp. d_hyp.
Qed.

Lemma d_impl_later p q :
  p ⟹ q ⊢ ▷p ⟹ ▷q.
Proof.
d_apply_l d_later_intro; d_intro.
d_apply_l d_later_conj; apply d_later_mono.
d_revert; done.
Qed.

Lemma d_impl_laters m n p q :
  m ≤ n -> p ⟹ q ⊢ m *▷ p ⟹ n *▷ q.
Proof.
intro H; induction H.
induction m; simpl; intros. done. d_apply_r d_impl_later; done.
d_intro; simpl; d_apply_r d_later_intro; d_revert; done.
Qed.

Lemma d_iff_laters n p q :
  p ⟺ q ⊢ n *▷ p ⟺ n *▷ q.
Proof.
d_split; d_apply_r d_impl_laters; d_hyp.
Qed.

Lemma d_laters_le m n p :
  m ≤ n -> m *▷ p ⊢ n *▷ p.
Proof.
intro H; induction H; simpl. done.
d_apply_r d_later_intro; apply IHle.
Qed.

Lemma d_laters_intro n p :
  p ⊢ n *▷ p.
Proof.
induction n; simpl. done.
d_apply_r d_later_intro; done.
Qed.

Lemma laters_S n p :
  ▷(n *▷ p) = S n *▷ p.
Proof.
done.
Qed.

Lemma laters_add m n p :
  (m + n) *▷ p = m *▷ (n *▷ p).
Proof.
induction m; simpl; congruence.
Qed.

End Deductions.

Section Reference_model.

Inductive Sω :=
  | Finite (n : nat)
  | Infinite.

Definition Sω_succ (p : Sω) :=
  match p with
  | Finite n => Finite (S n)
  | Infinite => Infinite
  end.

Definition Sω_min (p0 p1 : Sω) :=
  match p0, p1 with
  | Finite n0, Finite n1 => Finite (min n0 n1)
  | _, Infinite => p0
  | Infinite, _ => p1
  end.

Definition Sω_max (p0 p1 : Sω) :=
  match p0, p1 with
  | Finite n0, Finite n1 => Finite (max n0 n1)
  | _, Infinite => Infinite
  | Infinite, _ => Infinite
  end.

Definition Sω_leb (p0 p1 : Sω) :=
  match p0, p1 with
  | Finite n0, Finite n1 => n0 <=? n1
  | _, Infinite => true
  | _, _ => false
  end.

Definition Sω_le (p0 p1 : Sω) :=
  match p0, p1 with
  | Finite n0, Finite n1 => n0 ≤ n1
  | _, Infinite => True
  | _, _ => False
  end.

Definition interp (Γ : nat -> Sω) (x : term) :=
  match x with
  | t_Const false => Finite 0
  | t_Const true => Infinite
  | t_Var i => Γ i
  end.

Fixpoint eval (f : form Sω) :=
  match f with
  | f_Term x => x
  | f_Later p => Sω_succ (eval p)
  | f_Conn Conj p q => Sω_min (eval p) (eval q)
  | f_Conn Disj p q => Sω_max (eval p) (eval q)
  | f_Conn Impl p q =>
    if Sω_leb (eval p) (eval q)
    then Infinite else eval q
  end.

Definition realizes Γ p q :=
  (Sω_le (eval (interp Γ <$> p)) (eval (interp Γ <$> q))).

Global Instance Sω_le_pre_order :
  PreOrder Sω_le.
Proof.
split. intros []; simpl; done.
intros [] [] []; simpl; try done; lia.
Qed.

Global Instance realizes_pre_order Γ :
  PreOrder (realizes Γ).
Proof.
split; unfold realizes. intros p; done.
intros p q r; intros; etrans; done.
Qed.

Lemma Sω_le_leb p q :
  Sω_le p q <-> Sω_leb p q = true.
Proof.
destruct p, q; simpl; try done.
split; apply Nat.leb_le.
Qed.

Lemma Sω_le_cases p q :
  Sω_le p q \/ Sω_le (Sω_succ q) p.
Proof.
destruct p, q; simpl; auto; lia.
Qed.

Lemma Sω_compare p q :
  Sω_le Infinite (eval (p ⟹ q `∨` ▷q ⟹ p)).
Proof.
simpl; edestruct Sω_le_cases; apply Sω_le_leb in H; rewrite H; simpl.
all: destruct (if Sω_leb _ _ then _ else _); done.
Qed.

Lemma realizes_conj_intro Γ c p q :
  realizes Γ c p -> realizes Γ c q -> realizes Γ c (p `∧` q).
Proof.
unfold realizes; simpl; repeat destruct (eval _); simpl; try done; lia.
Qed.

Lemma realizes_impl_intro_top p q Γ :
  realizes Γ p q -> realizes Γ ⊤ (p ⟹ q).
Proof.
unfold realizes; simpl; repeat destruct (eval _); simpl; try done.
intros; apply Nat.leb_le in H; rewrite H; done.
Qed.

Theorem deduction_sound Γ p q :
  p ⊢ q -> realizes Γ p q.
Proof.
unfold realizes; intros H; induction H.
18: apply Sω_compare.
all: simpl in *; repeat destruct (eval _); simpl in *; try done; try lia.
all: destruct (_ <=? _) eqn:E; try done.
all: try apply Nat.leb_le in E; try apply Nat.leb_gt in E; lia.
Qed.

End Reference_model.

(*
We replace formulas with a term of the form `n *▷ $x`.
*)
Section Symbolic_evaluation.

Definition bounded_term `{ElemOf nat X} (range : X) x :=
  match x with
  | t_Const _ => True
  | t_Var i => i ∈ range
  end.

Implicit Types fv : gset nat.

Definition atom fv md a := ∃ x n,
  bounded_term fv x /\ n ≤ md /\ a = n *▷ $x.

Lemma atom_const fv md b :
  atom fv md ($t_Const b).
Proof.
exists (t_Const b), 0; repeat split; lia.
Qed.

Lemma atom_later fv md a :
  atom fv md a -> atom fv (S md) (▷a).
Proof.
intros (x & d & H1 & H2 & ->); exists x, (S d);
simpl; repeat split. done. lia.
Qed.

Lemma atom_weaken fv fv' md md' a :
  atom fv md a -> fv ⊆ fv' -> md ≤ md' -> atom fv' md' a.
Proof.
intros (x & d & H1 & H2 & ->); exists x, d; repeat split.
destruct x; simpl in *. done. apply H, H1. lia.
Qed.

Variable ctx : form term.
Variable fv : gset nat.
Variable md : nat.

Hypothesis exhaustive : ∀ a b,
  atom fv md a -> atom fv md b ->
  ctx ⊢ a ⟹ b \/ ctx ⊢ ▷b ⟹ a.

Ltac d_apply_r_lift_iff H :=
  (d_apply_r d_conj_elim_l; d_apply_r H) ||
  (d_apply_r d_conj_elim_r; d_apply_r H).

Ltac d_subst_r H := d_mp; [(d_apply_r H || d_apply_r_lift_iff H); d_hyp|].

Local Lemma exhaustive_weak a b :
  atom fv md a -> atom fv md b ->
  ctx ⊢ a ⟹ b \/ ctx ⊢ b ⟹ a.
Proof.
intros; destruct (exhaustive a b); try done. left; done.
right; d_intro; d_subst_r H1; d_apply_r d_later_intro; d_hyp.
Qed.

Theorem d_reduce_to_atom f :
  FV f ⊆ fv -> MD f ≤ md ->
  ∃ a, atom (FV f) (MD f) a /\ ctx ⊢ f ⟺ a.
Proof.
induction f as [[]|p|[] p IHp q IHq]; simpl; intros Hfv Hmd.
3-6: destruct IHp as (a & Aa & Ha); try lia. 3,5,7,9: set_solver.
4-6: destruct IHq as (b & Ab & Hb); try lia. 4,6,8: set_solver.
4-5: destruct (exhaustive_weak a b).
12: destruct (exhaustive a b).
4,5,8,9,12,13: eapply atom_weaken; [eassumption|set_solver|lia].
1: exists ($t_Const b).
2: exists (#i). 3: exists (▷a).
4: exists a. 5: exists b.
6: exists b. 7: exists a.
8: exists ⊤. 9: exists b.
1,2: split; [|clr; apply d_iff_refl].
apply atom_const. exists (t_Var i), 0; simpl; split; [set_solver|done]. split.
apply atom_later, Aa. d_apply_l Ha; d_split; d_apply_r d_impl_later; d_hyp.
all: split. 1,3,5,7,11: eapply atom_weaken; [eassumption|set_solver|lia].
5: apply atom_const. all: d_split; d_intro.
2,4: d_split; [d_subst_r Ha|d_subst_r Hb]; try d_hyp; d_subst_r H; d_hyp.
d_subst_r Ha; d_hyp. d_subst_r Hb; d_hyp.
1,3: eapply d_disj_elim; [d_hyp|idtac|idtac].
d_subst_r H; d_subst_r Ha; d_hyp. d_subst_r Hb; d_hyp.
d_subst_r Ha; d_hyp. d_subst_r H; d_subst_r Hb; d_hyp. 
d_right; d_subst_r Hb; d_hyp. d_left; d_subst_r Ha; d_hyp.
constructor. d_intro; d_subst_r Hb; d_subst_r H; d_subst_r Ha; d_hyp.
d_apply_r d_strong_fix; d_intro; d_subst_r Hb; d_mp; [d_hyp|].
d_subst_r Ha; d_subst_r H; d_hyp. d_intro; d_subst_r Hb; d_hyp.
Qed.

End Symbolic_evaluation.

(*
We obtain a disjunction of all possible implication orderings.
*)
Section Permutation_deduction.

Implicit Types xs : list nat.

Definition perm_form xs :=
  ⋀ ((λ p, #p.1 ⟹ #p.2) <$> adj xs).

Lemma perm_form_unfold x y zs :
  perm_form (x :: y :: zs) = #x ⟹ #y `∧` perm_form (y :: zs).
Proof.
done.
Qed.

Lemma d_perm_form_tl x ys :
  perm_form (x :: ys) ⊢ perm_form ys.
Proof.
destruct ys. unfold perm_form; simpl; done.
rewrite perm_form_unfold; clr_l; done.
Qed.

Lemma d_interleave x xs :
  perm_form xs ⊢ ⋁ (perm_form <$> interleave x xs).
Proof.
induction xs as [|y zs].
unfold perm_form; simpl. d_left; constructor.
simpl interleave; rewrite fmap_cons; simpl.
eapply d_disj_elim; [|d_left; clear IHzs|d_right].
clr; apply d_compare_weak with (p:=#x)(q:=#y).
rewrite perm_form_unfold; apply d_conj_comm.
(* interleave x into the tail. *)
d_revert; d_apply_l d_conj_intro.
apply d_perm_form_tl. done. d_revert.
d_apply_l IHzs. apply d_big_disj_elim; intros; d_intro; d_intro.
apply elem_of_list_fmap in H as (zs' & -> & H).
d_apply_r d_big_disj_intro.
2: { apply elem_of_list_fmap; eexists; split; [done|].
apply elem_of_list_fmap; exists zs'; done. }
(* y comes before zs' ∈ interleave x zs. *)
destruct zs as [|z zs]; simpl in *.
- apply elem_of_list_singleton in H; subst.
  unfold perm_form; simpl. d_split; d_hyp.
- inv H; rewrite ?perm_form_unfold.
  repeat d_split; d_hyp.
  apply elem_of_list_fmap in H2 as (zs'' & -> & H).
  rewrite perm_form_unfold; d_split; d_hyp.
Qed.

Lemma d_bind_interleave x xss :
  ⋁ (perm_form <$> xss) ⊢ ⋁ (perm_form <$> xss ≫= interleave x).
Proof.
apply d_big_disj_elim; intros.
apply elem_of_list_fmap in H as (xs & -> & H).
d_apply_r d_big_disj_subseteq. apply d_interleave with (x:=x).
apply subseteq_fmap, subseteq_mbind, H.
Qed.

Theorem d_permutations xs :
  ⊢ ⋁ (perm_form <$> permutations xs).
Proof.
induction xs as [|x xs]; simpl. d_left; constructor.
d_apply_l IHxs; apply d_bind_interleave.
Qed.

End Permutation_deduction.

(*
We obtain a disjunction with some different offsets between propositions.
*)
Section Offset_deduction.

Definition offset_clause md (p q : form term) n :=
  if n <=? md then n *▷ p ⟺ q else n *▷ p ⟹ q.

Definition offset_clauses p q md :=
  offset_clause md p q <$> seq 0 (2 + md).

Definition clause_terms xs :=
  t_Const false :: (t_Var <$> xs).

Lemma in_fmap_seq {X} (f : nat -> X) m n :
  m ≤ n -> f m ∈ f <$> seq 0 (S n).
Proof.
intros; apply elem_of_list_fmap; exists m; split.
done. apply in_seq_iff; lia.
Qed.

Lemma d_later_offsets c p q k :
  c ⊢ p ⟹ q -> c ⊢ k *▷ p ⟹ q `∨`
    ⋁ ((λ n, n *▷ p ⟺ q) <$> seq 0 k).
Proof.
intros; induction k. d_left; done.
eapply d_disj_elim. apply IHk.
eapply d_disj_elim. clr; apply (d_compare q (k *▷ p)).
- d_right; d_apply_r d_big_disj_intro.
  2: apply in_fmap_seq; done. d_split; d_hyp.
- d_left; d_hyp.
- d_right; clr_l.
  apply d_big_disj_subseteq.
  apply subseteq_fmap; intros i.
  rewrite ?in_seq_iff; lia.
Qed.

Lemma d_offset_clauses c p q md :
  c ⊢ p ⟹ q -> c ⊢ ⋁ offset_clauses p q md.
Proof.
unfold offset_clauses; intros.
ecut. apply d_later_offsets with (k:=S md), H.
apply d_disj_elim_inline.
- d_apply_r d_big_disj_intro.
  2: apply in_fmap_seq; done. unfold offset_clause.
  replace (S md <=? md) with false. done.
  symmetry; apply Nat.leb_gt; lia.
- eapply d_big_disj_elim; intros r Hr.
  apply elem_of_list_fmap in Hr as (d & -> & Hd).
  apply in_seq_iff in Hd. d_apply_r d_big_disj_intro.
  2: apply in_fmap_seq with (m:=d); lia. unfold offset_clause.
  replace (d <=? md) with true. done.
  symmetry; apply Nat.leb_le; lia.
Qed.

Lemma d_offset_clauses_perm md (xs : list nat) :
  perm_form xs ⊢ ⋀ ((λ p, ⋁ (offset_clauses ($p.1) ($p.2) md))
    <$> adj (clause_terms xs)).
Proof.
unfold perm_form; apply d_big_conj_intro; intros.
apply elem_of_list_fmap in H as (p' & -> & H).
unfold clause_terms in H; destruct xs. apply elem_of_nil in H; done.
rewrite fmap_cons, adj_cons, <-fmap_cons in H.
apply elem_of_cons in H as [->|].
- clr; apply d_offset_clauses; simpl.
  d_intro; d_apply_r d_false_elim; d_hyp.
- rewrite adj_fmap in H; apply elem_of_list_fmap in H as (ij & -> & H).
  apply d_offset_clauses, d_big_conj_elim, elem_of_list_fmap; exists ij; done.
Qed.

End Offset_deduction.

(*
We implement a decision procedure that looks for counterexamples.
*)
Section Counterexample_search.

Implicit Types fv : gset nat.

Fixpoint case_clauses (case : list (nat * nat)) (md : nat) (bot : form term) :=
  match case with
  | [] => []
  | (i, n) :: case' =>
    offset_clause md bot (#i) n ::
    case_clauses case' md (#i)
  end.

Fixpoint case_context (case : list (nat * nat)) (i : nat) : nat :=
  match case with
  | [] => 0
  | (j, n) :: case' => n + if i =? j then 0 else case_context case' i
  end.

Definition case_form md bot case :=
  ⋀ case_clauses case md bot.

Definition list_cases (fv : gset nat) (md : nat) :=
  let skips := seq 0 (2 + md) in
  let perms := permutations (elements fv) in
  xs ← perms; mapM (λ i, pair i <$> skips) xs.

Definition eval_case (f : form term) (case : list (nat * nat)) :=
  Sω_leb Infinite (eval (interp (Finite ∘ case_context case) <$> f)).

Definition counterexample (f : form term) :=
  find (negb ∘ eval_case f) (list_cases (FV f) (MD f)).

Example not_strong_later_inj :
  counterexample ((▷#0 ⟹ ▷#1) ⟹ #0 ⟹ #1) = Some [(1, 0); (0, 1)].
Proof. done. Qed.

Example not_excluded_middle :
  counterexample (#0 `∨` (#0 ⟹ ⊥)) = Some [(0, 1)].
Proof. done. Qed.

Section Case_form_exhaustive.

Lemma offset_clause_weaken md p q n :
  offset_clause md p q n ⊢ n *▷ p ⟹ q.
Proof.
unfold offset_clause; destruct (_ <=? _); d_hyp.
Qed.

Lemma case_form_exhaustive_bot_var case md bot p :
  p ∈ case.*1 ->
  case_form md bot case ⊢ S md *▷ bot ⟹ #p \/ ∃ n,
  case_form md bot case ⊢ n *▷ bot ⟺ #p.
Proof.
unfold case_form; intros Hp; revert bot.
induction case as [|[r k] case]; simpl; intros.
apply elem_of_nil in Hp; done.
rewrite fmap_cons in Hp; inv Hp.
- (* p = r *)
  unfold offset_clause; destruct (k <=? md) eqn:E.
  + right; exists k; d_hyp.
  + left; clr_r; d_intro; d_mp. d_hyp. clr_l.
    rewrite laters_S; apply d_laters_le.
    apply Nat.leb_gt in E; lia.
- (* p ∈ case.*1 *)
  destruct IHcase with (bot:=#r) as [IH|(n & IH)]. done.
  + left; d_intro; d_mp. d_apply_r IH; d_hyp.
    d_comm; d_assoc; clr_r. rewrite laters_S.
    d_comm; d_revert; d_apply_l offset_clause_weaken.
    d_apply_r d_impl_laters; [|done]. d_intro; d_mp.
    d_hyp. clr_l; apply d_laters_intro.
  + unfold offset_clause; destruct (k <=? md) eqn:E.
    * right; exists (n + k). d_comm; d_revert; d_apply_l IH; d_intro.
      d_apply_r d_iff_trans; d_split; [|d_hyp].
      rewrite laters_add; d_apply_r d_iff_laters. d_hyp.
    * left. d_comm; d_revert; d_apply_l IH; d_intro; d_intro.
      d_mp. d_hyp. d_assoc; clr_l. d_mp.
      d_apply_r d_impl_laters. d_hyp. done.
      clr_l; rewrite laters_S, <-laters_add.
      apply d_laters_le; apply Nat.leb_gt in E; lia.
Qed.

Lemma case_form_exhaustive_var_var case md bot p q :
  p ∈ case.*1 -> q ∈ case.*1 ->
  case_form md bot case ⊢ S md *▷ #p ⟹ #q \/
  case_form md bot case ⊢ S md *▷ #q ⟹ #p \/
  (∃ n, case_form md bot case ⊢ n *▷ #p ⟺ #q) \/
  (∃ n, case_form md bot case ⊢ n *▷ #q ⟺ #p).
Proof.
unfold case_form; intros Hp Hq; revert bot.
induction case as [|[r k] case]; simpl; intros. apply elem_of_nil in Hp; done.
replace (_ :: _).*1 with (r :: case.*1) in Hp, Hq by done; inv Hp; inv Hq.
- (* p = q = r *)
  right; right; right; exists 0; clr; apply d_iff_refl.
- (* p = r, q ∈ case.*1 *)
  eapply case_form_exhaustive_bot_var in H1 as [].
  left. clr_l; apply H. destruct H as (n & H).
  right; right; left; exists n; clr_l; apply H.
- (* p ∈ case.*1, q = r *)
  eapply case_form_exhaustive_bot_var in H1 as [].
  right; left. clr_l; apply H. destruct H as (n & H).
  right; right; right; exists n; clr_l; apply H.
- (* p, q ∈ case.*1 *)
  destruct IHcase with (bot:=#r) as [IH|[IH|[(n & IH)|(n & IH)]]]; try done.
  left; clr_l; done. right; left; clr_l; done.
  right; right; left; exists n; clr_l; done.
  right; right; right; exists n; clr_l; done.
Qed.

Lemma case_form_exhaustive_const_term case md b x :
  bounded_term case.*1 x ->
  case_form md ⊥ case ⊢ S md *▷ $x ⟹ $t_Const b \/
  case_form md ⊥ case ⊢ S md *▷ $t_Const b ⟹ $x \/
  (∃ n, case_form md ⊥ case ⊢ n *▷ $t_Const b ⟺ $x).
Proof.
intros; destruct b. left; d_intro; clr; done.
destruct x. destruct b. right; left; d_intro; clr; done.
right; right; exists 0; clr; apply d_iff_refl.
edestruct case_form_exhaustive_bot_var. apply H.
right; left; apply H0. right; right; apply H0.
Qed.

Lemma case_form_exhaustive_term_term case md x y :
  bounded_term case.*1 x ->
  bounded_term case.*1 y ->
  case_form md ⊥ case ⊢ S md *▷ $x ⟹ $y \/
  case_form md ⊥ case ⊢ S md *▷ $y ⟹ $x \/
  (∃ n, case_form md ⊥ case ⊢ n *▷ $x ⟺ $y) \/
  (∃ n, case_form md ⊥ case ⊢ n *▷ $y ⟺ $x).
Proof.
intros; destruct x.
edestruct case_form_exhaustive_const_term.
apply H0. right; left; apply H1. destruct H1; auto.
destruct y. edestruct case_form_exhaustive_const_term.
apply H. left; apply H1. destruct H1; auto.
apply case_form_exhaustive_var_var; done.
Qed.

Lemma convert_bounded_term fv xs x :
  xs ≡ₚ elements fv -> bounded_term fv x -> bounded_term xs x.
Proof.
destruct x; simpl; intros.
done. rewrite H; set_solver.
Qed.

Lemma case_form_exhaustive fv md case a b :
  case.*1 ≡ₚ elements fv ->
  atom fv md a -> atom fv md b ->
  case_form md ⊥ case ⊢ a ⟹ b \/ case_form md ⊥ case ⊢ ▷b ⟹ a.
Proof.
intros Hrange (x & m & Hx & Hm & ->) (y & n & Hy & Hn & ->).
rewrite laters_S; edestruct case_form_exhaustive_term_term
with (case:=case)(x:=x)(y:=y) as [H|[H|[(i & H)|(i & H)]]].
1,2: eapply convert_bounded_term; [apply Hrange|done].
- left; d_apply_l H; d_intro. d_apply_r d_laters_intro.
  d_mp. d_hyp. clr_l; apply d_laters_le; lia.
- right; d_apply_l H; d_intro. d_apply_r d_laters_intro.
  d_mp. d_hyp. clr_l; apply d_laters_le; lia.
- destruct (le_le_S_dec m (i + n)).
  + left; d_apply_l H; d_apply_l d_iff_laters.
    d_intro; d_mp. d_hyp. clr_l; rewrite <-laters_add.
    apply d_laters_le; lia.
  + right; d_apply_l H; d_apply_l d_iff_laters.
    d_intro; ecut. d_mp; [|clr_l; done]; d_hyp.
    rewrite <-laters_add; apply d_laters_le; lia.
- destruct (le_le_S_dec (i + m) n).
  + left; d_apply_l H; d_apply_l d_iff_laters.
    d_intro; ecut. d_mp; [|clr_l; done]; d_hyp.
    rewrite <-laters_add; apply d_laters_le; lia.
  + right; d_apply_l H; d_apply_l d_iff_laters.
    d_intro; d_mp. d_hyp. clr_l; rewrite <-laters_add.
    apply d_laters_le; lia.
Qed.

End Case_form_exhaustive.

Section List_cases.

Lemma list_cases_in case fv md :
  case ∈ list_cases fv md -> case.*1 ≡ₚ elements fv.
Proof.
unfold list_cases; intros.
eapply elem_of_list_bind in H as (xs & H1 & H2).
apply permutations_Permutation in H2; rewrite H2; clear H2.
replace case.*1 with xs; [done|].
apply elem_of_list_mapM in H1; induction H1. done.
apply elem_of_list_fmap in H as (n & -> & H).
rewrite fmap_cons, IHForall2; done.
Qed.

Lemma convert_to_case_form md bot cs xs :
  Forall2 (λ c p, c ∈ offset_clauses ($p.1) ($p.2) md)
    cs (adj (bot :: (t_Var <$> xs))) ->
  ∃ case, Forall2 (λ c i, c.1 = i /\ c.2 ≤ S md) case xs /\
    ⋀ cs ⊢ case_form md ($bot) case.
Proof.
unfold case_form; revert bot cs; induction xs as [|i xs]; intros.
- apply Forall2_nil_inv_r in H as ->.
  exists []; split. apply Forall2_nil; done. done.
- rewrite fmap_cons, adj_cons in H.
  apply Forall2_cons_inv_r in H as (c & cs' & H1 & H2 & ->).
  apply IHxs in H2 as (case & IH1 & IH2). unfold offset_clauses in H1.
  apply elem_of_list_fmap in H1 as (n & -> & Hn); simpl.
  apply in_seq_iff in Hn; exists ((i, n) :: case); split.
  apply Forall2_cons; simpl; split. lia. apply IH1.
  simpl. d_split. d_hyp. clr_l; apply IH2.
Qed.

Lemma d_list_cases fv md :
  ⊢ ⋁ (case_form md ⊥ <$> list_cases fv md).
Proof.
unfold list_cases.
ecut. apply d_permutations.
apply d_big_disj_elim; intros.
apply elem_of_list_fmap in H as (xs & -> & H).
ecut. apply d_offset_clauses_perm with (md:=md).
ecut. apply d_big_disj_conj_swap.
eapply d_big_disj_elim; intros.
apply elem_of_list_fmap in H0 as (cs & -> & Hcs).
apply elem_of_list_mapM in Hcs.
apply convert_to_case_form in Hcs as (case & H1 & H2).
d_apply_l H2; apply d_big_disj_intro.
apply elem_of_list_fmap; exists case; split. done.
apply elem_of_list_bind; exists xs; split; [|done].
eapply elem_of_list_mapM, Forall2_impl. apply H1.
intros [i n] i'; intros (<- & Hn); simpl in Hn.
apply elem_of_list_fmap; eexists; split. done.
apply in_seq_iff; lia.
Qed.

End List_cases.

Section Soundness.

Lemma eval_case_spec f case :
  eval_case f case = true <-> realizes (Finite ∘ case_context case) ⊤ f.
Proof.
unfold eval_case, realizes;
rewrite Sω_le_leb; done.
Qed.

Theorem counterexample_sound f case :
  counterexample f = Some case ->
  ¬realizes (Finite ∘ case_context case) ⊤ f.
Proof. 
intros; rewrite <-eval_case_spec.
apply find_some in H as [_ <-]; simpl; destruct (eval_case _); done.
Qed.

End Soundness.

Section Completeness.

Lemma fmap_later {X Y} (t : X -> Y) n (f : form X) :
  t <$> (n *▷ f) = n *▷ (t <$> f).
Proof.
induction n; simpl. done.
rewrite <-IHn; done.
Qed.

Lemma eval_later n f i :
  eval f = Finite i -> eval (n *▷ f) = Finite (n + i).
Proof.
induction n; simpl; intros.
done. rewrite IHn; done.
Qed.

Lemma realizes_later_iff Γ p q i n :
  eval (interp Γ <$> p) = Finite i ->
  eval (interp Γ <$> q) = Finite (n + i) ->
  realizes Γ ⊤ (n *▷ p ⟹ q) /\ realizes Γ ⊤ (q ⟹ n *▷ p).
Proof.
intros Hp Hq; split; apply realizes_impl_intro_top;
unfold realizes; erewrite fmap_later, eval_later, Hq; done.
Qed.

Lemma realizes_finite_atom Γ fv md a :
  atom fv md a -> realizes (Finite ∘ Γ) ⊤ a -> ∃ n, a = n *▷ ⊤.
Proof.
unfold realizes; intros ([[]|] & n & Hx & Hn & ->) H; simpl in *.
exists n; done. all: exfalso; erewrite fmap_later, eval_later in H; done.
Qed.

Lemma case_context_realizes_case_form md bot bot_n case Γ :
  (∀ i, i ∈ case.*1 -> Γ i = Finite (bot_n + case_context case i)) ->
  NoDup case.*1 -> eval (interp Γ <$> bot) = Finite bot_n ->
  realizes Γ ⊤ (case_form md bot case).
Proof.
unfold case_form; revert bot bot_n.
induction case as [|[i n] case]; rewrite ?fmap_cons; simpl; intros. done.
assert (Hi : eval (interp Γ <$> #i) = Finite (n + bot_n)).
simpl; rewrite H, Nat.eqb_refl, Nat.add_0_r, Nat.add_comm.
done. apply elem_of_list_here. apply realizes_conj_intro.
- edestruct realizes_later_iff. apply H1. apply Hi.
  unfold offset_clause; destruct (n <=? md).
  apply realizes_conj_intro; done. done.
- inv H0; apply IHcase with (bot_n:=n + bot_n).
  intros j Hj; rewrite H. 2: apply elem_of_list_further, Hj.
  destruct (j =? i) eqn:E. apply Nat.eqb_eq in E as ->; done.
  rewrite Nat.add_assoc, Nat.add_comm with (m:=n); done. done. done.
Qed.

Lemma case_form_reduce f  case :
  case.*1 ≡ₚ elements (FV f) ->
  ∃ a, atom (FV f) (MD f) a /\
  case_form (MD f) ⊥ case ⊢ f ⟺ a.
Proof.
intros; eapply d_reduce_to_atom.
intros; eapply case_form_exhaustive.
all: done.
Qed.

Lemma eval_case_complete f case :
  case.*1 ≡ₚ elements (FV f) ->
  eval_case f case = true ->
  case_form (MD f) ⊥ case ⊢ f.
Proof.
intros Hfv Heval; edestruct case_form_reduce as (a & Ha & Hf).
apply Hfv. eapply realizes_finite_atom in Ha as [d ->].
d_apply_l Hf; d_mp. d_hyp. clr; apply d_laters_intro.
etrans. apply realizes_conj_intro.
eapply case_context_realizes_case_form with (bot:=⊥)(case:=case).
intros i Hi; rewrite Nat.add_0_l; done.
rewrite Hfv; apply NoDup_elements. done.
apply eval_case_spec, Heval. apply deduction_sound.
d_revert; d_apply_l Hf; d_hyp.
Qed.

Theorem counterexample_complete f :
  counterexample f = None -> ⊢ f.
Proof.
unfold counterexample; intros. ecut.
apply d_list_cases with (fv:=FV f)(md:=MD f).
eapply d_big_disj_elim; intros p Hp.
apply elem_of_list_fmap in Hp as (case & -> & Hcase).
apply eval_case_complete. eapply list_cases_in, Hcase.
eapply find_none, negb_false_iff in H.
apply H. apply elem_of_list_In, Hcase.
Qed.

End Completeness.

End Counterexample_search.

(*
The final result.
*)
Corollary deduction_complete p q :
  (∀ Γ, realizes Γ p q) -> p ⊢ q.
Proof.
intros; apply d_impl_revert_top.
apply counterexample_complete.
destruct (counterexample _) eqn:E; [exfalso|done].
apply counterexample_sound in E; apply E.
apply realizes_impl_intro_top, H.
Qed.
