Set Implicit Arguments.
Require Import String List Omega.
From TypeSafetyAgda Require Export extensible_array.

Require Import header_extensible tactics header_metacoq.

(** * Case study 1: Modular Type-Safety Proofs (originally in Agda)

We follow the above paper by Christopher Schwaab/Jeremy G. Siek, using our adapted approach.
 *)


(** ** Arithmetic expressions *)

Section Plus.

Variable exp: Type.
Context `{retract (exp_plus exp) exp}.

Variable wtyped : exp -> ty -> Prop.

Inductive wtyped_plus : exp -> ty -> Prop :=
| ok_value n : wtyped_plus (atom_ n) TNat
| ok_plus s t : wtyped s TNat -> wtyped t TNat -> wtyped_plus (plus_ s t) TNat.

Variable eval : exp -> exp -> Prop.

Inductive eval_plus : exp -> exp -> Prop :=
| stepl e1 e1' e2 : eval e1 e1' -> eval_plus (plus_ e1 e2) (plus_ e1' e2)
| stepr e1 e2 e2': eval e2 e2' -> eval_plus  (plus_ e1 e2) (plus_ e1 e2')
| sum n1 n2 : eval_plus  (plus_ (atom_ n1) (atom_ n2)) (atom_ (n1 + n2)).

Hint Constructors wtyped_plus eval_plus.

Variable retract_has_ty : forall s A, wtyped_plus s A -> wtyped s A.
Variable retract_has_ty_rev : forall s A, wtyped (inj s) A -> wtyped_plus (inj s) A.

Instance retract_has_ty_instance s A:
  Imp (wtyped_plus s A)  (wtyped s A).
Proof. exact (@retract_has_ty s A). Defined.

Instance retract_has_ty_rev_instance s A:
  ImpRev (wtyped (inj s) A) (wtyped_plus (inj s) A).
Proof. exact (@retract_has_ty_rev s A). Defined.

MetaCoq Run
Modular Lemma pres_plus where (exp_plus exp) extends exp at 0 with [~ eval_plus ~> eval ~] :
  forall e e', eval_plus e e' -> forall A, wtyped e A -> wtyped e' A.
Next Obligation.
  intros IH e e' Heval. destruct Heval; intros.
  - minversion H1. mconstructor. eapply IH; eassumption. eassumption.
  - minversion H1. mconstructor. eassumption. eapply IH; eassumption.
  - minversion H0. mconstructor.
Defined.

End Plus.

(** ** Option expressions *)

Section Option.

Variable exp: Type.
Context `{retract (exp_opt exp) exp}.

Variable wtyped : exp -> ty -> Prop.

Inductive wtyped_opt : exp -> ty -> Prop :=
| ok_none : wtyped_opt none_ TOption
| ok_some s : wtyped s TNat -> wtyped_opt (some_ s) TOption.

Variable eval : exp -> exp -> Prop.

Inductive eval_opt : exp -> exp -> Prop :=
| stepsome e1 e1' : eval e1 e1' -> eval_opt (some_ e1) (some_ e1').
Hint Constructors wtyped_opt eval_opt.

Variable retract_has_ty : forall s A, wtyped_opt s A -> wtyped s A.
Variable retract_has_ty_rev : forall s A, wtyped (inj s) A -> wtyped_opt (inj s) A.

Instance retract_has_ty_instance_opt s A:
  Imp (wtyped_opt s A)  (wtyped s A).
Proof. exact (@retract_has_ty s A). Defined.

Instance retract_has_ty_rev_instance_opt s A:
  ImpRev (wtyped (inj s) A) (wtyped_opt (inj s) A).
Proof. exact (@retract_has_ty_rev s A). Defined.

MetaCoq Run
Modular Lemma pres_opt where (exp_opt exp) extends exp at 0 with [~ eval_opt ~> eval ~] :
  forall e e', eval_opt e e' -> forall A, wtyped e A -> wtyped e' A.
Next Obligation.
  intros IH e e' Heval. destruct Heval; intros.
  - minversion H1. mconstructor. eapply IH; eassumption. 
Defined.

(** ** Array expressions *)

Context `{retract (exp_arr exp) exp}.

Inductive wtyped_arr : exp -> ty -> Prop :=
| ok_nil : wtyped_arr nil_ TArray
| ok_lookup a e : wtyped a TArray -> wtyped e TNat -> wtyped_arr (rd_ a e) TOption
| ok_ins a e n : wtyped a TArray -> wtyped e TNat -> wtyped  n TNat -> wtyped_arr (wr_ a e n) TArray.

Inductive L : exp -> exp -> exp -> Prop :=
  L_read a e n : L (wr_ a e n) e (some_ n)
| L_notfound e : L nil_ e none_
| L_rec e e' a n : e <> e' -> L a e' n -> L (wr_ a e n) e' n.

Inductive eval_arr : exp -> exp -> Prop :=
| steprd1 e a a' : eval a a' -> eval_arr (rd_ a e) (rd_ a' e)
| steprd2 e e' a : eval e e' -> eval_arr (rd_ a e) (rd_ a e')
| stepwr1 a n e a' : eval a a' -> eval_arr (wr_ a n e) (wr_ a' n e)
| stepwr2 a n e n' : eval n n' -> eval_arr (wr_ a n e) (wr_ a n' e)
| stepwr3 a n e e' : eval e e' -> eval_arr (wr_ a n e) (wr_ a n e')
| lookup a n s: L a n s -> eval_arr (rd_ a n) s.

Variable retract_has_ty' : forall s A, wtyped_arr s A -> wtyped s A.
Variable retract_has_ty_rev' : forall s A, wtyped (inj s) A -> wtyped_arr (inj s) A.

Instance retract_has_ty_instance' s A:
  Imp (wtyped_arr s A)  (wtyped s A).
Proof. exact (@retract_has_ty' s A). Defined.

Instance retract_has_ty_rev_instance' s A:
  ImpRev (wtyped (inj s) A) (wtyped_arr (inj s) A).
Proof. exact (@retract_has_ty_rev' s A). Defined.

Lemma L_lemma  a n s :
  L a n s -> wtyped a TArray -> wtyped n TNat -> wtyped s TOption.
Proof.
  intros. induction H1.
  - minversion H2. eapply retract_has_ty. eauto.
  - eapply retract_has_ty. eauto.
  - minversion H2. eapply IHL; eauto.
Qed.      

MetaCoq Run
Modular Lemma pres_arr where (exp_arr exp) extends exp at 0 with [~ eval_arr ~> eval ~] :
  forall e e', eval_arr e e' -> forall A, wtyped e A -> wtyped e' A.
Next Obligation.
  intros IH e e' Heval. destruct Heval; intros.
  - minversion H2. mconstructor; eauto.
  - minversion H2. mconstructor; eauto.
  - minversion H2. mconstructor; eauto.
  - minversion H2. mconstructor; eauto.
  - minversion H2. mconstructor; eauto.
  - minversion H2. eapply L_lemma; eauto.
Defined.    

End Option.

(** ** Composed development *)

Inductive wtyped : exp -> ty -> Prop :=
| wtyped_in_plus s A : wtyped_plus wtyped s A -> wtyped s A
| wtyped_in_arr s A : wtyped_arr wtyped s A -> wtyped s A
| wtyped_in_opt s A : wtyped_opt wtyped s A -> wtyped s A.

Hint Constructors wtyped_plus wtyped_arr wtyped_opt wtyped.

Inductive eval : exp -> exp -> Prop :=
| eval_in_plus s t : eval_plus eval s t -> eval s t
| eval_in_arr s t : eval_arr eval s t -> eval s t
| eval_in_opt s t : eval_opt eval s t -> eval s t.

Hint Constructors eval_plus eval_arr eval_opt eval.

Lemma wtyped_inv_plus :
  forall (s0 : exp_plus exp) (A : ty), wtyped (inj s0) A -> wtyped_plus wtyped (inj s0) A.
Proof.
  intros. inv H; inv H0; econstructor; eauto.
Qed.
Hint Resolve wtyped_inv_plus.

Lemma wtyped_inv_arr :
  forall (s0 : exp_arr exp) (A : ty), wtyped (inj s0) A -> wtyped_arr wtyped (inj s0) A.
Proof.
  intros. inv H; inv H0; econstructor; eauto.
Qed.
Hint Resolve wtyped_inv_arr.

Lemma wtyped_inv_opt :
  forall (s0 : exp_opt exp) (A : ty), wtyped (inj s0) A -> wtyped_opt wtyped (inj s0) A.
Proof.
  intros. inv H; inv H0; econstructor; eauto.
Qed.
Hint Resolve wtyped_inv_opt.

Instance exp_features : has_features "eval" := ["plus";"arr";"opt"].

MetaCoq Run
  Compose Fixpoint pres on 2 : forall e e', eval e e' -> forall A, wtyped e A -> wtyped e' A.
