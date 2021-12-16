(*
A constructive completeness proof for the later modality
========================================================
*)

Require Import Nat.
From stdpp Require Import list.

Inductive term :=
  | t_Const (b : bool)
  | t_Prop (i : nat).

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

Fixpoint FV (f : form term) :=
  match f with
  | f_Term (t_Prop i) => S i
  | f_Term _ => 0
  | f_Later p => FV p
  | f_Conn _ p q => max (FV p) (FV q)
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

Global Instance form_top : Top (form term) := f_Term (t_Const true).
Global Instance form_bot : Bottom (form term) := f_Term (t_Const false).

Notation "# i" := (f_Term (t_Prop i)) (at level 40, format "# i").
Notation "▷ p" := (f_Later p) (at level 49, right associativity, format "▷ p").
Notation "p `∧` q" := (f_Conn Conj p q) (at level 56, left associativity).
Notation "p `∨` q" := (f_Conn Disj p q) (at level 56, left associativity).
Notation "p ⟹ q" := (f_Conn Impl p q) (at level 54, right associativity).
Notation "p ⟺ q" := (p ⟹ q `∧` q ⟹ p) (at level 54).
Notation "⋀ fs" := (f_big Conj ⊤ fs) (at level 57).
Notation "⋁ fs" := (f_big Disj ⊥ fs) (at level 57).

(*
Why use a binary sequent?
-------------------------
The sequent could be replaced with an implication, e.g. we could write something
like ⊢ p ⟹ q instead of p ⊢ q. But there are a few advantages of using a binary
sequent relation: (1) Using tactics: a binary relation allows setoid rewriting
and pre-order based tactics. (2) Readability: the sequent avoids parentheses in
some cases, and creates a clear separation between hypothesis and goal.
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
  | d_later_fixp p       : ▷p ⊢ p -> ⊢ p
  | d_later_mono p q     : p ⊢ q -> ▷p ⊢ ▷q
  | d_later_conj p q     : ▷p `∧` ▷q ⊢ ▷(p `∧` q)
  | d_compare p q        : ⊢ p ⟹ q `∨` ▷q ⟹ p
where "p ⊢ q" := (deduction p q) and "⊢ q" := (⊤ ⊢ q).
Notation "p ⊣⊢ q" := (p ⊢ q /\ q ⊢ p) (at level 71).

Ltac inv H := inversion H; subst.
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

Lemma d_conj_assoc p q r : (p `∧` q) `∧` r ⊢ p `∧` (q `∧` r).
Proof. repeat d_split; d_hyp. Qed.

Lemma d_impl_revert c p q : c ⊢ p ⟹ q -> c `∧` p ⊢ q.
Proof. intros; d_mp; [clr_r; done|clr_l; done]. Qed.

Lemma d_impl_revert_top p q : ⊢ p ⟹ q -> p ⊢ q.
Proof. intros; d_mp; [clr; done|refl]. Qed.

Ltac d_comm := d_apply_l d_conj_comm.
Ltac d_assoc := d_apply_l d_conj_assoc.
Ltac d_revert := apply d_impl_revert || apply d_impl_revert_top.

(*
We list all basic deductions that are needed later in the proof.
*)
Section Deductions.

Lemma d_strong_fixp p :
  ▷p ⟹ p ⊢ p.
Proof.
d_mp; [clr|refl].
eapply d_later_fixp.
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
d_apply_r d_later_intro; d_apply_r d_strong_fixp.
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

Lemma d_big_disj_intro p q qs :
  q ∈ qs -> p ⊢ q -> p ⊢ ⋁ qs.
Proof.
induction qs; simpl; intros.
apply not_elem_of_nil in H; done.
inv H; [d_left|d_right]. done.
apply IHqs; done.
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
apply d_big_disj_intro with (q:=p).
auto. done.
Qed.

Lemma d_iff_refl p :
  ⊢ p ⟺ p.
Proof.
d_split; d_intro; d_hyp.
Qed.

Lemma d_iff_later c p q :
  c ⊢ p ⟺ q -> c ⊢ ▷p ⟺ ▷q.
Proof.
intros; d_split.
all: d_apply_l d_later_intro; d_intro.
all: d_apply_l d_later_conj; apply d_later_mono.
all: d_revert; d_apply_l H; constructor.
Qed.

End Deductions.

(*
But what does it mean for a formula to hold? We define this using a reference
model that is classically equivalent to the more intuitive model of infinite
sequences. We show that this model realizes every deduction.
*)
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
  | Finite n0, Finite n1 => n0 <= n1
  | _, Infinite => True
  | _, _ => False
  end.

Definition interp (Γ : nat -> Sω) (x : term) :=
  match x with
  | t_Const false => Finite 0
  | t_Const true => Infinite
  | t_Prop i => Γ i
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
  Sω_le (eval (interp Γ <$> p)) (eval (interp Γ <$> q)).

Instance Sω_le_pre_order :
  PreOrder Sω_le.
Proof.
split. intros []; simpl; done.
intros [] [] []; simpl; try done; lia.
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

Lemma realizes_impl p q Γ :
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
We can evaluate formulas semantically, if we are given a context with enough
information about the proposition variables. We will need this later on to prove
completeness.
*)
Section Semantic_evaluation.

Definition atom_term fv x :=
  match x with
  | t_Const _ => True
  | t_Prop i => i < fv
  end.

Definition atom fv md a :=
  ∃ x d, atom_term fv x /\ d <= md /\ a = f_later d (f_Term x).

Lemma atom_const fv md b :
  atom fv md (f_Term (t_Const b)).
Proof.
exists (t_Const b), 0; repeat split; lia.
Qed.

Lemma atom_later fv md a :
  atom fv md a -> atom fv (S md) (▷a).
Proof.
intros (x & d & H1 & H2 & ->); exists x, (S d);
simpl; repeat split. done. lia.
Qed.

Lemma atom_weaken fv md fv' md' a :
  atom fv md a -> fv ≤ fv' -> md ≤ md' -> atom fv' md' a.
Proof.
intros (x & d & H1 & H2 & ->); exists x, d; repeat split.
destruct x; simpl in *; [done|lia]. lia.
Qed.

Variable c : form term.
Variable fv md : nat.

Hypothesis exhaustive : ∀ a b,
  atom fv md a -> atom fv md b ->
  c ⊢ a ⟹ b \/ c ⊢ ▷b ⟹ a.

Ltac d_apply_r_lift_iff H :=
  (d_apply_r d_conj_elim_l; d_apply_r H) ||
  (d_apply_r d_conj_elim_r; d_apply_r H).

Ltac d_subst_r H := d_mp; [(d_apply_r H || d_apply_r_lift_iff H); d_hyp|].

Local Lemma exhaustive_weak a b :
  atom fv md a -> atom fv md b ->
  c ⊢ a ⟹ b \/ c ⊢ b ⟹ a.
Proof.
intros; destruct (exhaustive a b); try done. left; done.
right; d_intro; d_subst_r H1; d_apply_r d_later_intro; d_hyp.
Qed.

Theorem d_reduce_to_atom f :
  FV f <= fv -> MD f <= md ->
  ∃ a, atom (FV f) (MD f) a /\ c ⊢ f ⟺ a.
Proof.
induction f as [[]|p|[] p IHp q IHq]; simpl; intros Hfv Hmd.
3-6: destruct IHp as (a & Aa & Ha); try lia.
4-6: destruct IHq as (b & Ab & Hb); try lia.
4-5: destruct (exhaustive_weak a b).
12: destruct (exhaustive a b).
4,5,8,9,12,13: eapply atom_weaken; [eassumption|lia|lia].
1: exists (f_Term (t_Const b)).
2: exists (#i). 3: exists (▷a).
4: exists a. 5: exists b.
6: exists b. 7: exists a.
8: exists ⊤. 9: exists b.
1,2: split; [|clr; apply d_iff_refl].
apply atom_const. exists (t_Prop i), 0; simpl; split; [lia|done].
split; [apply atom_later, Aa|apply d_iff_later, Ha]. all: split.
1,3,5,7,11: eapply atom_weaken; [eassumption|lia|lia]. 5: apply atom_const.
all: d_split; d_intro.
2,4: d_split; [d_subst_r Ha|d_subst_r Hb]; try d_hyp; d_subst_r H; d_hyp.
d_subst_r Ha; d_hyp. d_subst_r Hb; d_hyp.
1,3: eapply d_disj_elim; [d_hyp|idtac|idtac].
d_subst_r H; d_subst_r Ha; d_hyp. d_subst_r Hb; d_hyp.
d_subst_r Ha; d_hyp. d_subst_r H; d_subst_r Hb; d_hyp. 
d_right; d_subst_r Hb; d_hyp. d_left; d_subst_r Ha; d_hyp.
constructor. d_intro; d_subst_r Hb; d_subst_r H; d_subst_r Ha; d_hyp.
d_apply_r d_strong_fixp; d_intro; d_subst_r Hb; d_mp; [d_hyp|].
d_subst_r Ha; d_subst_r H; d_hyp. d_intro; d_subst_r Hb; d_hyp.
Qed.

End Semantic_evaluation.

(*
The next result we need is about permutations of proposition variables. We show
that we can obtain a disjunction of all possible orderings.
*)
Section Permutation_deduction.

Implicit Types xs : list nat.

Fixpoint perm_clauses xs :=
  match xs with
  | [] => []
  | [_] => []
  | x :: (y :: _) as xs' => (#x ⟹ #y) :: perm_clauses xs'
  end.

Definition perm_form xs := ⋀ perm_clauses xs.

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
apply d_big_disj_intro with (q:=perm_form (y :: zs')).
apply elem_of_list_fmap; eexists; split; [done|].
apply elem_of_list_fmap; exists zs'; done.
(* y comes before zs' ∈ interleave x zs. *)
destruct zs as [|z zs]; simpl in *.
- apply elem_of_list_singleton in H; subst.
  unfold perm_form; simpl. d_split; d_hyp.
- inv H; clear H; rewrite ?perm_form_unfold.
  repeat d_split; d_hyp.
  apply elem_of_list_fmap in H2 as (zs'' & -> & H).
  rewrite perm_form_unfold; d_split; d_hyp.
Qed.

Lemma subseteq_fmap {X Y} (f : X -> Y) (l l' : list X) :
  l ⊆ l' -> f <$> l ⊆ f <$> l'.
Proof.
intros H y Hy. apply elem_of_list_fmap in Hy as (x & -> & Hx).
apply elem_of_list_fmap; exists x; auto.
Qed.

Lemma subseteq_mbind {X Y} (f : X -> list Y) x (xs : list X) :
  x ∈ xs -> f x ⊆ xs ≫= f.
Proof.
intros H y Hy; apply elem_of_list_bind; exists x; done.
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
Now we implement a decision procedure that looks for counterexamples. If no
counterexample is found the formula is true, and it is possible to give a
deduction.
*)
Section Counterexample_search.

Fixpoint case_form (md : nat) (pred : form term) (case : list (nat * nat)) :=
  match case with
  | [] => ⊤
  | (i, d) :: case' => if d <? md
    then (f_later d pred ⟺ #i) `∧` case_form md (#i) case'
    else (f_later d pred ⟹ #i) `∧` case_form md (#i) case'
  end.

Fixpoint case_context (case : list (nat * nat)) (i : nat) : nat :=
  match case with
  | [] => 0
  | (j, d) :: case' => d + if i =? j then 0 else case_context case' i
  end.

Definition eval_case (f : form term) (case : list (nat * nat)) :=
  Sω_leb Infinite (eval (interp (Finite ∘ case_context case) <$> f)).

Definition list_cases fv md :=
  let skips := seq 0 (2 + md) in
  let perms := permutations (seq 0 fv) in
  let cases := xs ← perms; mapM (λ i, pair i <$> skips) xs in
  cases.

Definition counterexample (f : form term) :=
  find (negb ∘ eval_case f) (list_cases (FV f) (MD f)).

Example not_strong_later_inj :
  counterexample ((▷#0 ⟹ ▷#1) ⟹ #0 ⟹ #1) = Some [(1, 0); (0, 1)].
Proof. done. Qed.

Example not_excluded_middle :
  counterexample (#0 `∨` (#0 ⟹ ⊥)) = Some [(0, 1)].
Proof. done. Qed.

Lemma eval_case_spec f case :
  eval_case f case = true <-> realizes (Finite ∘ case_context case) ⊤ f.
Proof.
unfold eval_case, realizes;
rewrite Sω_le_leb; done.
Qed.

Lemma counterexample_sound f case :
  counterexample f = Some case -> ∃ Γ, ¬ realizes Γ ⊤ f.
Proof. 
intros; eexists; rewrite <-eval_case_spec with (case:=case).
apply find_some in H as [_ <-]; simpl; destruct (eval_case _); done.
Qed.

Definition case_range fv (case : list (nat * nat)) :=
  ∀ i, i < fv -> ∃ d, (i, d) ∈ case.

Lemma list_cases_range case fv md :
  case ∈ list_cases fv md -> case_range fv case.
Proof.
unfold list_cases; intros.
eapply elem_of_list_bind in H as (xs & H1 & H2).
Admitted.

Lemma case_form_exhaustive fv md case a b :
  case_range fv case -> atom fv md a -> atom fv md b ->
  case_form md ⊥ case ⊢ a ⟹ b \/ case_form md ⊥ case ⊢ ▷b ⟹ a.
Proof.
Admitted.

Lemma case_form_reduce f  case :
  case_range (FV f) case ->
  ∃ a, atom (FV f) (MD f) a /\
  case_form (MD f) ⊥ case ⊢ f ⟺ a.
Proof.
intros; eapply d_reduce_to_atom.
intros; eapply case_form_exhaustive.
all: done.
Qed.

Lemma eval_case_complete f case :
  case_range (FV f) case ->
  eval_case f case = true ->
  case_form (MD f) ⊥ case ⊢ f.
Proof.
intros Hfv Heval; apply case_form_reduce in Hfv as (a & H1 & H2).
(* We must have a = ⊤. *)
Admitted.

Lemma d_list_cases fv md :
  ⊢ ⋁ (case_form md ⊥ <$> list_cases fv md).
Proof.
Admitted.

Theorem counterexample_complete f :
  counterexample f = None -> ⊢ f.
Proof.
unfold counterexample; intros. ecut.
apply d_list_cases with (fv:=FV f)(md:=MD f).
eapply d_big_disj_elim; intros p Hp.
apply elem_of_list_fmap in Hp as (case & -> & Hcase).
apply eval_case_complete. eapply list_cases_range, Hcase.
eapply find_none, negb_false_iff in H.
apply H. apply elem_of_list_In, Hcase.
Qed.

End Counterexample_search.

(*
The final result: if q always follows from p in the reference model, then there
exists a deduction of the type p ⊢ q.
*)
Theorem deduction_complete p q :
  (∀ Γ, realizes Γ p q) -> p ⊢ q.
Proof.
intros; apply d_impl_revert_top.
apply counterexample_complete.
destruct (counterexample _) eqn:E; [exfalso|done].
apply counterexample_sound in E as [Γ HΓ]; apply HΓ.
apply realizes_impl, H.
Qed.
