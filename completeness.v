(*
A constructive completeness proof for the later modality
========================================================
*)

Require Import Nat.
From stdpp Require Import list.

Inductive term :=
  | t_False
  | t_True
  | t_Prop (i : nat).

Inductive connective := Conj | Disj | Impl.

Inductive form (X : Type) :=
  | f_Term (x : X)
  | f_Later (p : form X)
  | f_Conn (c : connective) (p q : form X).

Arguments f_Term {_}.
Arguments f_Later {_}.
Arguments f_Conn {_}.

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

Definition f_later {X} n (f : form X) := Nat.iter n f_Later f.
Definition f_big {X} c (f0 : form X) fs := foldr (f_Conn c) f0 fs.

Notation "⊥" := (f_Term t_False).
Notation "⊤" := (f_Term t_True).
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

Ltac inv H := inversion H; subst.
Ltac cut x := transitivity x.
Ltac ecut := etransitivity.
Ltac refl := reflexivity.
Ltac conj_l := apply d_conj_elim_l.
Ltac conj_r := apply d_conj_elim_r.
Ltac disj_l := ecut; [|apply d_disj_intro_l].
Ltac disj_r := ecut; [|apply d_disj_intro_r].
Ltac impl_i := apply d_impl_intro.
Ltac impl_e := eapply d_impl_elim.

Global Instance d_pre_order :
  PreOrder deduction.
Proof.
split. intros p; apply d_refl.
intros p q r; apply d_trans.
Defined.

Lemma d_clr p q : ⊢ q -> p ⊢ q.
Proof. ecut. apply d_true_intro. done. Qed.

Lemma d_clr_l c p q : c ⊢ q -> p `∧` c ⊢ q.
Proof. ecut. conj_r. done. Qed.

Lemma d_clr_r c p q : c ⊢ q -> c `∧` p ⊢ q.
Proof. ecut. conj_l. done. Qed.

Ltac clr := apply d_clr.
Ltac clr_l := apply d_clr_l.
Ltac clr_r := apply d_clr_r.

Lemma d_impl_revert c p q : c ⊢ p ⟹ q -> c `∧` p ⊢ q.
Proof. intros; impl_e; [clr_r; done|conj_r]. Qed.

Lemma d_impl_revert_top p q : ⊢ p ⟹ q -> p ⊢ q.
Proof. intros; impl_e; [clr; done|refl]. Qed.

Section Deductions.

Lemma d_conj_comm p q :
  p `∧` q ⊢ q `∧` p.
Proof.
eapply d_conj_intro; [conj_r|conj_l].
Qed.

Lemma d_conj_assoc p q r :
  (p `∧` q) `∧` r ⊢ p `∧` (q `∧` r).
Proof.
repeat apply d_conj_intro.
clr_r; clr_r; done.
clr_r; clr_l; done.
clr_l; done.
Qed.

Lemma d_strong_fixp p :
  ▷p ⟹ p ⊢ p.
Proof.
impl_e; [clr|refl].
eapply d_later_fixp.
impl_i; impl_e; [conj_r|].
ecut. apply d_conj_comm. apply d_impl_revert.
ecut. apply d_later_intro. impl_i.
ecut. apply d_later_conj. apply d_later_mono.
impl_e; [conj_r|conj_l].
Qed.

Lemma d_later_impl p q :
  ▷p ⟹ ▷q ⊢ ▷(p ⟹ q).
Proof.
eapply d_disj_elim.
clr; apply d_compare with (p:=p)(q:=q).
- ecut. conj_r. apply d_later_intro.
- cut (▷q). impl_e. clr_r; done.
  ecut; [|apply d_later_intro].
  ecut; [|apply d_strong_fixp].
  impl_i; impl_e. clr_r; clr_l; done.
  impl_e. clr_r; clr_r; done. clr_l; done.
  apply d_later_mono; impl_i; clr_r; done.
Qed.

Lemma d_later_inj p q :
  ▷p ⊢ ▷q -> p ⊢ q.
Proof.
intros; impl_e; [clr|refl].
apply d_later_elim. ecut; [|apply d_later_impl].
impl_i; clr_l; done.
Qed.

Lemma d_compare_weak p q :
  ⊢ p ⟹ q `∨` q ⟹ p.
Proof.
eapply d_disj_elim.
clr; apply d_compare with (p:=p)(q:=q).
clr_l; disj_l; done. clr_l; disj_r.
impl_i; impl_e. clr_r; done. clr_l; constructor.
Qed.

Lemma d_big_disj_intro p q qs :
  q ∈ qs -> p ⊢ q -> p ⊢ ⋁ qs.
Proof.
induction qs; simpl; intros.
apply not_elem_of_nil in H; done.
inv H; [disj_l|disj_r]. done.
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
  | Finite n0, Finite n1 => n0 <= n1
  | _, Infinite => True
  | _, _ => False
  end.

Definition interp (Γ : nat -> Sω) (x : term) :=
  match x with
  | t_False => Finite 0
  | t_True => Infinite
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
unfold perm_form; simpl. disj_l; constructor.
simpl interleave; rewrite fmap_cons; simpl.
eapply d_disj_elim; [|disj_l; clear IHzs|disj_r].
clr; apply d_compare_weak with (p:=#x)(q:=#y).
rewrite perm_form_unfold; apply d_conj_comm.
(* interleave x into the tail. *)
apply d_impl_revert. ecut. apply d_conj_intro.
apply d_perm_form_tl. done. apply d_impl_revert.
ecut. apply IHzs. apply d_big_disj_elim; intros; impl_i; impl_i.
apply elem_of_list_fmap in H as (zs' & -> & H).
apply d_big_disj_intro with (q:=perm_form (y :: zs')).
apply elem_of_list_fmap; eexists; split; [done|].
apply elem_of_list_fmap; exists zs'; done.
(* y comes before zs' ∈ interleave x zs. *)
destruct zs as [|z zs]; simpl in *.
- apply elem_of_list_singleton in H; subst.
  unfold perm_form; simpl. apply d_conj_intro.
  clr_l; done. clr; done.
- inv H; clear H; rewrite ?perm_form_unfold.
  + repeat apply d_conj_intro. clr_l; done.
    clr_r; clr_r; clr_r; done. clr_r; clr_r; clr_l; done.
  + apply elem_of_list_fmap in H2 as (zs'' & -> & H).
    rewrite perm_form_unfold; apply d_conj_intro.
    clr_r; clr_l; clr_r; done. clr_r; clr_r; done.
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
ecut; [apply d_interleave with (x:=x)|apply d_big_disj_subseteq].
apply subseteq_fmap, subseteq_mbind, H.
Qed.

Lemma d_permutations xs :
  ⊢ ⋁ (perm_form <$> permutations xs).
Proof.
induction xs as [|x xs]; simpl. disj_l; constructor.
ecut; [apply IHxs|apply d_bind_interleave].
Qed.

End Permutation_deduction.

Section Counterexample_search.

Fixpoint case_form (d_max : nat) (case : list (nat * nat)) :=
  match case with
  | [] => ⊤ | [_] => ⊤
  | (i, d) :: ((j, _) :: _) as case' => if d <? d_max
    then (f_later d (#i) ⟺ #j) `∧` case_form d_max case'
    else (f_later d (#i) ⟹ #j) `∧` case_form d_max case'
  end.

Fixpoint case_context (case : list (nat * nat)) (acc : nat) (i : nat) : Sω :=
  match case with
  | [] => Finite 0
  | (j, d) :: case' => if i =? j
    then Finite acc
    else case_context case' (acc + S d) i
  end.

Definition eval_case (f : form term) (case : list (nat * nat)) :=
  Sω_leb Infinite (eval (interp (case_context case 0) <$> f)).

Definition list_cases fv md :=
  let skips := seq 0 (S md) in
  let perms := permutations (seq 0 fv) in
  let cases := xs ← perms; mapM (λ i, pair i <$> skips) xs in
  cases.

Definition counterexample (f : form term) :=
  find (negb ∘ eval_case f) (list_cases (FV f) (MD f)).

Example not_strong_later_inj :
  counterexample ((▷#0 ⟹ ▷#1) ⟹ #0 ⟹ #1) = Some [(1, 0); (0, 0)].
Proof. done. Qed.

Example leftover_middle_case :
  counterexample (#0 ⟹ #1 `∨` ▷▷#1 ⟹ #0) = Some [(1, 0); (0, 0)].
Proof. done. Qed.

Lemma eval_case_spec f case :
  eval_case f case = true <-> realizes (case_context case 0) ⊤ f.
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

Lemma eval_case_complete f d_max case :
  MD f <= d_max -> case_range (FV f) case ->
  eval_case f case = true -> case_form d_max case ⊢ f.
Proof.
(*
The case must have a sufficient variable range and modal depth. Then the case
hypothesis includes all the inequalities needed to reduce the formula f.
*)
Admitted.

Lemma list_cases_complete fv md :
  ⊢ ⋁ (case_form md <$> list_cases fv md).
Proof.
(*
First we split into all possible permutations, then for each permutation we
split each implication into a finite number of distances.
*)
Admitted.

Theorem counterexample_complete f :
  counterexample f = None -> ⊢ f.
Proof.
unfold counterexample; intros. ecut.
apply list_cases_complete with (fv:=FV f)(md:=MD f).
eapply d_big_disj_elim; intros p Hp.
apply elem_of_list_fmap in Hp as (case & -> & Hcase).
apply eval_case_complete. done.
eapply list_cases_range, Hcase.
eapply find_none, negb_false_iff in H.
apply H. apply elem_of_list_In, Hcase.
Qed.

End Counterexample_search.

Theorem deduction_complete p q :
  (∀ Γ, realizes Γ p q) -> p ⊢ q.
Proof.
intros; apply d_impl_revert_top.
apply counterexample_complete.
destruct (counterexample _) eqn:E; [exfalso|done].
apply counterexample_sound in E as [Γ HΓ]; apply HΓ.
apply realizes_impl, H.
Qed.
