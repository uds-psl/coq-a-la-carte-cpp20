Set Implicit Arguments.
Require Import String List Omega.

(** * Introductory example: counting funtions *)
(** ** manual definitions *)

Inductive exp_var (exp : Type) :=
  var : nat -> exp_var exp.

Inductive exp_lam (exp : Type) :=
  lam : exp -> exp_lam exp
| app : exp -> exp -> exp_lam exp.

Inductive exp_bool (exp : Type) :=
  constBool : bool -> exp_bool exp
| If : exp -> exp -> exp -> exp_bool exp.

Inductive exp_arith (exp : Type) :=
| plus : exp -> exp -> exp_arith exp
| constNat : nat -> exp_arith exp.

Inductive Exp_lam :=
| inj_var_lam : exp_var Exp_lam -> Exp_lam
| inj_lam_lam : exp_lam Exp_lam -> Exp_lam.

Inductive Exp_bool :=
| inj_var_bool : exp_var Exp_bool -> Exp_bool
| inj_lam_bool : exp_lam Exp_bool -> Exp_bool
| inj_bool_bool : exp_bool Exp_bool -> Exp_bool.

Inductive Exp_arith :=
| inj_var_arith : exp_var Exp_arith -> Exp_arith
| inj_lam_arith : exp_lam Exp_arith -> Exp_arith
| inj_arith_arith : exp_arith Exp_arith -> Exp_arith.

Section count.

  Variable exp : Type.
  Variable count : exp -> nat.

  Definition count_var (s : exp_var exp) : nat :=
    match s with
    | var _ _ => 1
    end.

  Definition count_lam (s : exp_lam exp) : nat :=
    match s with
    | lam s => count s
    | app s t => count s + count t
    end.

  Definition count_bool (s : exp_bool exp) : nat :=
    match s with
    | constBool _ b => 1
    | If s t u => count s + count t + count u
    end.

  Variable count_gt : forall s, count s > 0.

  Lemma count_gt_var :
    forall s : exp_var exp, count_var s > 0.
  Proof.
    simpl; intros s.
    destruct s; simpl; eauto.
  Defined.

  Lemma count_gt_lam :
    forall s : exp_lam exp, count_lam s > 0.
  Proof.
    simpl; intros s.
    destruct s; simpl; eauto.
    - assert (H1 := count_gt e). 
      assert (H2 := count_gt e0).
      omega.
  Defined.

  Lemma count_gt_bool :
    forall s : exp_bool exp, count_bool s > 0.
  Proof.
    cbn; intros s.
    destruct s; cbn; eauto.
    - assert (H1 := count_gt e).
      assert (H2 := count_gt e0).
      assert (H3 := count_gt e1).
      omega.
  Defined.

End count.

Fixpoint Count_lam (s : Exp_lam) : nat :=
  match s with
  | inj_var_lam s => count_var s
  | inj_lam_lam s => count_lam Count_lam s
  end.
  
Fixpoint Count_gt_lam (s : Exp_lam) : Count_lam s > 0.
Proof.
  destruct s; cbn.
  - now apply count_gt_var. 
  - now apply count_gt_lam. 
Qed.

Fixpoint Count_bool (s : Exp_bool) : nat :=
  match s with
  | inj_var_bool s => count_var s
  | inj_lam_bool s => count_lam Count_bool s
  | inj_bool_bool s => count_bool Count_bool s
  end.
  
Fixpoint Count_gt_bool (s : Exp_bool) : Count_bool s > 0.
Proof.
  destruct s; cbn.
  - now apply count_gt_var. 
  - now apply count_gt_lam.
  - now apply count_gt_bool.
Qed.

(* Definition of Retracts *)
Class retract X Y :=
  {
    inj : X -> Y ;
    retr : Y -> option X;
    retract_works : forall x, retr (inj x) = Some x;
    retract_tight : forall x y, retr y = Some x -> inj x = y
  }.
Notation "X <: Y" := (retract X Y) (at level 75, no associativity).
Arguments Build_retract {X} {Y}.

Lemma retract_inj {X Y} {R : retract X Y} x y :
  inj x = inj y -> x = y.
Proof.
  intros. enough (Some x = Some y) by congruence.
  now rewrite <- !retract_works, H.
Qed.

Instance retract_var_lam : retract (exp_var Exp_lam) Exp_lam.
Proof.
  apply (Build_retract inj_var_lam (fun s => match s with | inj_var_lam s => Some s |_ => None end)).
  - eauto.
  - intros x []; congruence.
Defined.

Instance retract_lam_lam : retract (exp_lam Exp_lam) Exp_lam.
Proof.
  apply (Build_retract inj_lam_lam (fun s => match s with | inj_lam_lam s => Some s |_ => None end)).
  - eauto.
  - intros x []; congruence.
Defined.

Instance retract_var_bool : retract (exp_var Exp_bool) Exp_bool.
Proof.
  apply (Build_retract inj_var_bool (fun s => match s with | inj_var_bool s => Some s |_ => None end)).
  - eauto.
  - intros x []; congruence.
Defined.

Instance retract_lam_bool : retract (exp_lam Exp_bool) Exp_bool.
Proof.
  apply (Build_retract inj_lam_bool (fun s => match s with | inj_lam_bool s => Some s |_ => None end)).
  - eauto.
  - intros x []; congruence.
Defined.

Instance retract_bool_bool : retract (exp_bool Exp_bool) Exp_bool.
Proof.
  apply (Build_retract inj_bool_bool (fun s => match s with | inj_bool_bool s => Some s |_ => None end)).
  - eauto.
  - intros x []; congruence.
Defined.

Section SmartConstructors.
  Variable X: Type.
  Context `{retract (exp_lam X) X}.

  Definition lam_  (s : X) : X :=
    inj (lam s).

  Definition app_ (s t: X) : X :=
    inj (app s t).

  Context `{retract (exp_var X) X}.

  Definition var_ (x : nat) : X :=
    inj (@var X x).

  Context `{retract (exp_bool X) X}.

  Definition constBool_ (b : bool) : X :=
    inj (constBool _ b).

  Definition if_  (s t u : X) : X :=
    inj (If s t u).

End SmartConstructors.

Example s : Exp_bool :=
  lam_ (if_ (constBool_ true)  (constBool_ true)  (constBool_ true)).

(* ** Extension by Arithmetic Definitions *)

Section Arith.

  Variable exp : Type.
  Variable count : exp -> nat.

  Definition count_arith (s : exp_arith exp) :=
    match s with
    | constNat _ _ => 1
    | plus s t => 1 + count s + count t
    end.

  Variable count_gt : forall s, count s > 0.

  Lemma count_gt_arith s :
    count_arith s > 0.
  Proof.
    destruct s; cbn; eauto.
    assert (IH1 := count_gt e). assert (IH2 := count_gt e0).
    omega.
  Defined.

  Context `{retract (exp_arith exp) exp}.

  Definition constNat_  (n : nat) : exp :=
    inj (constNat _ n).

  Definition plus_ (s t: exp) : exp :=
    inj (plus s t).

End Arith.

Fixpoint Count_arith (s : Exp_arith) : nat :=
  match s with
  | inj_var_arith s => count_var s
  | inj_lam_arith s => count_lam Count_arith s
  | inj_arith_arith s => count_arith Count_arith s
  end.

Fixpoint Count_gt_arith (s : Exp_arith) : Count_arith s > 0.
Proof.
  destruct s; cbn.
  - now apply count_gt_var.
  - now apply count_gt_lam. 
  - now apply count_gt_arith. 
Qed.

(* ** Section 3 : Induction Principles *)


Definition in_var X (x : X) (s : exp_var X) :  Prop :=
  match s with
  | var _ _ => False
  end.

Definition in_lam X (x : X) (s : exp_lam X) :  Prop :=
  match s with
  | lam s => x = s
  | app s t => x = s \/ x = t
  end.

Definition in_bool X (x : X) (s:  exp_bool X) :  Prop :=
  match s with
  | If s t u => x = s \/ x = t \/ x = u
  | _ => False
  end.


Fixpoint Exp_lam_induction (P : Exp_lam -> Prop)
       (H_var : forall e : exp_var Exp_lam, (forall x, in_var x e -> P x) -> P (inj e))
       (H_lam : forall e : exp_lam Exp_lam, (forall x, in_lam x e -> P x) -> P (inj e)) (e : Exp_lam) : P e.
Proof.
  destruct e.
  - destruct e; intros; apply H_var. intros. inversion H.
  - destruct e.
    + intros; apply H_lam; intros. inversion H. subst. now eapply Exp_lam_induction.
    + intros; apply H_lam; intros. inversion H; subst; now eapply Exp_lam_induction.
Qed.

Fixpoint Exp_bool_induction (P : Exp_bool -> Prop)
       (H_var : forall e : exp_var Exp_bool, (forall x, in_var x e -> P x) -> P (inj e))
       (H_lam : forall e : exp_lam Exp_bool, (forall x, in_lam x e -> P x) -> P (inj e))
       (H_bool : forall e : exp_bool Exp_bool, (forall x, in_bool x e -> P x) -> P (inj e))
       (e : Exp_bool) : P e.
Proof.
  destruct e.
  - destruct e; intros; apply H_var. intros. inversion H.
  - destruct e.
    + intros; apply H_lam; intros. inversion H. subst. now eapply Exp_bool_induction.
    + intros; apply H_lam; intros. inversion H; subst; now eapply Exp_bool_induction.
  - destruct e.
    + intros; apply H_bool; intros. inversion H. 
    + intros; apply H_bool; intros. destruct H as [ | [ | ]]; subst; now eapply Exp_bool_induction.
Qed.

Section count_again.

  Variable exp : Type.
  Variable count : exp -> nat.

  Lemma count_gt'_var :
    forall s : exp_var exp, (forall s', in_var s' s -> count s' > 0) ->  count_var s > 0.
  Proof.
    simpl; intros s count_gt.
    destruct s; simpl; eauto.
  Qed.

  Lemma count_gt'_lam :
    forall s : exp_lam exp, (forall s', in_lam s' s -> count s' > 0) ->  count_lam count s > 0.
  Proof.
    simpl; intros s count_gt.
    destruct s; simpl; eauto.
    - specialize (count_gt e eq_refl). eauto.
    - assert (H1 := count_gt e (or_introl eq_refl)).
      assert (H2 := count_gt e0 (or_intror eq_refl)).
      omega.
  Qed.

  Lemma count_gt'_bool :
    forall s : exp_bool exp, (forall s', in_bool s' s -> count s' > 0) -> count_bool count s > 0.
  Proof.
    cbn; intros s count_gt.
    destruct s; cbn; eauto.
    - assert (H1 := count_gt e (or_introl eq_refl)).
      assert (H2 := count_gt e0 (or_intror (or_introl eq_refl))).
      assert (H3 := count_gt e1 (or_intror (or_intror eq_refl))).
      omega.
  Qed.

End count_again.
  
Lemma Count_gt'_lam (s : Exp_lam) : Count_lam s > 0.
Proof.
  induction s using Exp_lam_induction; cbn.
  - eapply count_gt'_var; eassumption.
  - now apply count_gt'_lam.
Qed.
  
Lemma Count_gt'_bool (s : Exp_bool) : Count_bool s > 0.
Proof.
  induction s using Exp_bool_induction; cbn.
  - eapply count_gt'_var; eassumption.
  - now apply count_gt'_lam.
  - now apply count_gt'_bool. 
Qed.
