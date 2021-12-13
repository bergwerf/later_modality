(* A decision procedure for propositional logic with the later modality. *)

Require Import Nat.
From stdpp Require Import list.

Inductive term :=
  | t_False
  | t_True
  | t_Prop (i : nat).

Inductive operator := Conj | Disj | Impl.

Inductive form (X : Type) :=
  | f_Term (x : X)
  | f_Later (p : form X)
  | f_Op (op : operator) (p q : form X).

Arguments f_Term {_}.
Arguments f_Later {_}.
Arguments f_Op {_}.

Fixpoint FV (f : form term) :=
  match f with
  | f_Term (t_Prop i) => S i
  | f_Term _ => 0
  | f_Later p => FV p
  | f_Op _ p q => max (FV p) (FV q)
  end.

Fixpoint MD (f : form term) :=
  match f with
  | f_Term _ => 0
  | f_Later p => S (MD p)
  | f_Op _ p q => max (MD p) (MD q)
  end.

Global Instance fmap_form : FMap form :=
  λ X Y f, fix rec (r : form X) :=
    match r with
    | f_Term x => f_Term (f x)
    | f_Later p => f_Later (rec p)
    | f_Op op p q => f_Op op (rec p) (rec q)
    end.

Definition f_big {X} op (f0 : form X) fs := foldr (f_Op op) f0 fs.

Notation "⊥" := (f_Term t_False).
Notation "⊤" := (f_Term t_True).
Notation "# i" := (f_Term (t_Prop i)) (at level 40, format "# i").
Notation "▷ p" := (f_Later p) (at level 49, right associativity, format "▷ p").
Notation "p ⟹ q" := (f_Op Impl p q) (at level 54, right associativity).
Notation "p `∧` q" := (f_Op Conj p q) (at level 56, left associativity).
Notation "p `∨` q" := (f_Op Disj p q) (at level 56, left associativity).
Notation "p ⟺ q" := (p ⟹ q `∧` q ⟹ p) (at level 54).
Notation "⋀ fs" := (f_big Conj ⊤ fs) (at level 57).
Notation "⋁ fs" := (f_big Disj ⊥ fs) (at level 57).

Reserved Notation "p ⊢ q" (at level 70).
Inductive deduction : form term -> form term -> Prop :=
  | d_refl p : p ⊢ p
  | d_trans p q r : p ⊢ q -> q ⊢ r -> p ⊢ r
  | d_true_intro p : p ⊢ ⊤
  | d_false_elim p : ⊥ ⊢ p
  | d_conj_intro c p q : c ⊢ p -> c ⊢ q -> c ⊢ p `∧` q
  | d_conj_elim_l p q : p `∧` q ⊢ p
  | d_conj_elim_r p q : p `∧` q ⊢ q
  | d_disj_intro_l p q : p ⊢ p `∨` q
  | d_disj_intro_r p q : q ⊢ p `∨` q
  | d_disj_elim c p q r : c ⊢ p `∨` q -> c `∧` p ⊢ r -> c `∧` q ⊢ r -> c ⊢ r
  | d_impl_intro c p q : c `∧` p ⊢ q -> c ⊢ p ⟹ q
  | d_impl_elim c p q : c ⊢ p ⟹ q -> c ⊢ p -> c ⊢ q
  | d_later_intro p : p ⊢ ▷p
  | d_later_top p : ⊤ ⊢ ▷p -> ⊤ ⊢ p
  | d_later_Löb p : ▷p ⊢ p -> ⊤ ⊢ p
  | d_later_mono p q : p ⊢ q -> ▷p ⊢ ▷q
  | d_later_conj p q : ▷p `∧` ▷q ⊢ ▷(p `∧` q)
  | d_later_cmp p q : ⊤ ⊢ p ⟹ q `∨` ▷q ⟹ p
where
"p ⊢ q" := (deduction p q).

Ltac cut x := transitivity x.
Ltac ecut := etransitivity.
Ltac refl := reflexivity.
Ltac conj_l := apply d_conj_elim_l.
Ltac conj_r := apply d_conj_elim_r.
Ltac disj_l := ecut; [|apply d_disj_intro_l].
Ltac disj_r := ecut; [|apply d_disj_intro_r].

Global Instance d_pre_order :
  PreOrder deduction.
Proof.
split. intros p; apply d_refl.
intros p q r; apply d_trans.
Defined.

Lemma d_weaken_top p q : ⊤ ⊢ q -> p ⊢ q.
Proof. ecut. apply d_true_intro. done. Qed.

Lemma d_weaken_l c p q : c ⊢ q -> c `∧` p ⊢ q.
Proof. ecut. conj_l. done. Qed.

Lemma d_weaken_r c p q : c ⊢ q -> p `∧` c ⊢ q.
Proof. ecut. conj_r. done. Qed.

Ltac clr := apply d_weaken_top.
Ltac clr_l := apply d_weaken_r.
Ltac clr_r := apply d_weaken_l.

Section Deductions.

Lemma d_impl_revert c p q :
  c ⊢ p ⟹ q -> c `∧` p ⊢ q.
Proof.
intros; eapply d_impl_elim; [clr_r; done|conj_r].
Qed.

Lemma d_impl_revert_top p q :
  ⊤ ⊢ p ⟹ q -> p ⊢ q.
Proof.
intros; eapply d_impl_elim; [clr; done|refl].
Qed.

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

Lemma d_strong_Löb p :
  ▷p ⟹ p ⊢ p.
Proof.
eapply d_impl_elim; [clr|refl].
eapply d_later_Löb.
eapply d_impl_intro.
eapply d_impl_elim; [conj_r|].
ecut. apply d_conj_comm. apply d_impl_revert.
ecut. apply d_later_intro. apply d_impl_intro.
ecut. apply d_later_conj. apply d_later_mono.
eapply d_impl_elim; [conj_r|conj_l].
Qed.

Lemma d_later_impl p q :
  ▷p ⟹ ▷q ⊢ ▷(p ⟹ q).
Proof.
eapply d_disj_elim.
clr; apply d_later_cmp with (p:=p)(q:=q).
- ecut. conj_r. apply d_later_intro.
- cut (▷q).
  eapply d_impl_elim. clr_r; done.
  ecut; [|apply d_later_intro].
  ecut; [|apply d_strong_Löb].
  apply d_impl_intro.
  eapply d_impl_elim. clr_r; clr_l; done.
  eapply d_impl_elim. clr_r; clr_r; done. clr_l; done.
  apply d_later_mono, d_impl_intro; clr_r; done.
Qed.

Lemma d_later_inj p q :
  ▷p ⊢ ▷q -> p ⊢ q.
Proof.
intros; eapply d_impl_elim; [clr|refl].
apply d_later_top. ecut; [|apply d_later_impl].
apply d_impl_intro; clr_l; done.
Qed.

Lemma d_except_zero p :
  ▷p ⊢ ▷⊥ `∨` ▷⊥ ⟹ p.
Proof.
eapply d_disj_elim.
clr; apply d_later_cmp with (p:=p)(q:=⊥).
2: clr_l; disj_r; done.
disj_l; ecut. eapply d_conj_intro. clr_r; refl.
clr_l. ecut. apply d_later_intro. refl.
ecut. apply d_later_conj. apply d_later_mono.
eapply d_impl_elim. clr_l; refl. clr_r; refl.
Qed.

Lemma d_trichotomy p q :
  ⊤ ⊢ ▷p ⟹ q `∨` p ⟺ q `∨` ▷q ⟹ p.
Proof.
eapply d_disj_elim; try clr_l. apply d_later_cmp with (p:=p)(q:=q).
eapply d_disj_elim. clr; apply d_later_cmp with (p:=q)(q:=p).
disj_l; disj_r; done.
clr_l; disj_l; disj_l; done.
disj_r; done.
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

End Deductions.

Section Model.

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
  | f_Op Conj p q => Sω_min (eval p) (eval q)
  | f_Op Disj p q => Sω_max (eval p) (eval q)
  | f_Op Impl p q =>
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
destruct (_ <=? _) eqn:E. done. apply Nat.leb_gt in E; lia.
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

End Model.

Section Decider.

Definition cons_prod {X} (hds : list X) (tls : list (list X))
  : list (list X) := flat_map (λ x, cons x <$> tls) hds.

Fixpoint encode_case (d_max : nat) (case : list (nat * nat)) :=
  match case with
  | [] => ⊤ | [_] => ⊤
  | (i, d) :: ((j, _) :: _) as case' =>
    if d =? d_max
    then (Nat.iter d f_Later (#i) ⟹ #j) `∧` encode_case d_max case'
    else (Nat.iter d f_Later (#i) ⟺ #j) `∧` encode_case d_max case'
  end.

Fixpoint prop_value (case : list (nat * nat)) (acc : nat) (i : nat) : Sω :=
  match case with
  | [] => Finite 0
  | (j, d) :: case' => if i =? j
    then Finite acc
    else prop_value case' (acc + S d) i
  end.

Definition check_case (f : form term) (case : list (nat * nat)) :=
  match (eval (interp (prop_value case 0) <$> f)) with
  | Finite _ => true
  | Infinite => false
  end.

Definition all_cases fv md :=
  let perms := permutations (seq 0 fv) in
  let skips := Nat.iter fv (cons_prod (seq 0 (S md))) [[]] in
  let cases := flat_map (λ perm, zip perm <$> skips) perms in
  cases.

Definition counter_example (f : form term) :=
  find (check_case f) (all_cases (FV f) (MD f)).

Example not_strong_later_inj :
  counter_example ((▷#0 ⟹ ▷#1) ⟹ #0 ⟹ #1) = Some [(1, 0); (0, 0)].
Proof. done. Qed.

Example leftover_middle_case :
  counter_example (#0 ⟹ #1 `∨` ▷▷#1 ⟹ #0) = Some [(1, 0); (0, 0)].
Proof. done. Qed.

End Decider.

Lemma check_case_sound f case :
  check_case f case = true -> ∃ Γ, ¬ realizes Γ ⊤ f.
Proof.
intros; exists (prop_value case 0); intros C.
unfold check_case, realizes in *; simpl in *.
destruct (eval _); done.
Qed.

Lemma counter_example_sound f case :
  counter_example f = Some case -> ∃ Γ, ¬ realizes Γ ⊤ f.
Proof.
intros; eapply check_case_sound.
apply find_some in H; apply H.
Qed.

Lemma all_cases_fv case fv md :
  case ∈ all_cases fv md -> foldl max 0 (map fst case) = fv.
Proof.
(*
Although this is easy to prove, I have skipped it because the case unfolding
may change depending on how I figure out a proof for all_cases_complete.
*)
Admitted.

Lemma check_case_complete f d_max case :
  MD f <= d_max ->
  FV f <= foldl max 0 (map fst case) ->
  check_case f case = false -> encode_case d_max case ⊢ f.
Proof.
(*
This is quite a bit of work. The case must have a sufficient variable range and
modal depth. Then the case hypothesis includes all the inequalities needed to
reduce the formula f.
*)
Admitted.

Lemma all_cases_complete fv md :
  ⊤ ⊢ ⋁ (encode_case md <$> all_cases fv md).
Proof.
(*
This is challenging, I do not yet know exactly how to approach this proof.
Intuitively this should hold; every situation satisfies one of the cases.
But how do we translate this into a deduction?
*)
Admitted.

Theorem counter_example_complete f :
  counter_example f = None -> ⊤ ⊢ f.
Proof.
unfold counter_example; intros. ecut.
apply all_cases_complete with (fv:=FV f)(md:=MD f).
eapply d_big_disj_elim; intros p Hp.
apply elem_of_list_fmap in Hp as (case & -> & Hcase).
apply check_case_complete. done.
erewrite all_cases_fv; [done|apply Hcase].
eapply find_none; [apply H|apply elem_of_list_In, Hcase].
Qed.

Theorem deduction_complete p q :
  (∀ Γ, realizes Γ p q) -> p ⊢ q.
Proof.
intros; apply d_impl_revert_top.
apply counter_example_complete.
destruct (counter_example _) eqn:E; [exfalso|done].
apply counter_example_sound in E as [Γ HΓ]; apply HΓ.
apply realizes_impl, H.
Qed.
