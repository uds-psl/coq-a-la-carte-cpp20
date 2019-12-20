From SN Require Export expressions sn_bool sn_lam sn_var sn_arith.
Require Import header_metacoq.

(** ** Composition *)

(** *** Definition of typing *)

Inductive has_ty : list ty -> exp -> ty -> Prop :=
| inl_has_ty_var Gamma s A:  has_ty_var _ _ Gamma s A -> has_ty Gamma s A
| inl_has_ty_lam Gamma s A : has_ty_lam _ _ has_ty Gamma s A -> has_ty Gamma s A
| inl_has_ty_bool Gamma s A : has_ty_bool _ _ has_ty Gamma s A -> has_ty Gamma s A
| inl_has_ty_arith Gamma s A : has_ty_arith _ _ has_ty Gamma s A -> has_ty Gamma s A.
Instance has_ty_features : has_features "has_ty" := ["var";"lam";"bool";"arith"].

Hint Constructors has_ty.
Hint Constructors has_ty_var.

Lemma has_ty_rev_var: forall (Gamma0 : list ty) (s0 : exp_var (* ty *) (* exp *)) (A0 : ty),
    has_ty Gamma0 (inj s0) A0 -> has_ty_var _ _ Gamma0 (inj s0) A0.
Proof.
  intros. inversion H; subst; eauto; inversion H0. 
Qed.

Lemma has_ty_rev_lam: forall (Gamma0 : list ty) (s0 : exp_lam ty exp) (A0 : ty),
    has_ty Gamma0 (inj s0) A0 -> has_ty_lam _ _ has_ty Gamma0 (inj s0) A0.
Proof.
  intros. inversion H; subst; eauto; inversion H0. 
Qed.

Lemma has_ty_rev_bool: forall (Gamma0 : list ty) (s0 : exp_bool  exp) (A0 : ty),
    has_ty Gamma0 (inj s0) A0 -> has_ty_bool _ _ has_ty Gamma0 (inj s0) A0.
Proof.
  intros. inversion H; subst; eauto; inversion H0.
Qed.

Lemma has_ty_rev_arith: forall (Gamma0 : list ty) (s0 : exp_arith  exp) (A0 : ty),
    has_ty Gamma0 (inj s0) A0 -> has_ty_arith _ _ has_ty Gamma0 (inj s0) A0.
Proof.
  intros. inversion H; subst; eauto; inversion H0.
Qed.

Hint Resolve has_ty_rev_var has_ty_rev_lam has_ty_rev_bool has_ty_rev_arith.

Lemma up_ren_ext xi zeta :
  (forall x, xi x = zeta x) -> forall x, up_ren xi x = up_ren zeta x.
Proof.
  intros H [|]; try eauto. cbn. unfold funcomp. now rewrite H.
Qed.

Hint Resolve rinstInst_exp instId_exp rinstId_exp varL_exp varLRen_exp compComp_exp compComp'_exp compRen_exp compRen'_exp renComp_exp renComp'_exp renRen_exp renRen'_exp upId_exp_exp idSubst_exp upExtRen_exp_exp extRen_exp upExt_exp_exp extRen_exp upExt_exp_exp ext_exp up_ren_ren_exp_exp compRenRen_exp up_ren_subst_exp_exp compRenSubst_exp up_subst_ren_exp_exp compSubstRen_exp up_subst_subst_exp_exp compSubstSubst_exp rinstInst_up_exp_exp rinst_inst_exp up_ren_ren up_ren_ext.

(** # <a id="has_ty_ren" /> #*)
MetaCoq Run Compose
Lemma has_ty_ren on 3 : forall Gamma s A  (C : has_ty Gamma s A),
    forall (xi: nat -> nat) Delta, (forall x, nth_error Gamma x = nth_error Delta (xi x)) -> has_ty Delta (ren_exp xi s) A.
Hint Resolve has_ty_ren.

(** # <a id="has_ty_subst" /> #*)
MetaCoq Run Compose
Lemma has_ty_subst on 3 : forall Gamma s A  (C : has_ty Gamma s A),
    forall sigma Delta, (forall x A, nth_error Gamma x = Datatypes.Some A -> has_ty Delta (sigma x) A) -> has_ty Delta (subst_exp sigma s) A.
Hint Resolve has_ty_subst.

(** *** Definition of evaluation *)

Inductive step : exp -> exp -> Prop :=
| inl_step_var s s' : step_var _ s s' -> step s s'
| inl_step_lam s s' : step_lam _ _ subst_exp step s s' -> step s s'
| inl_step_bool s s' : step_bool _ step s s' -> step s s'
| inl_step_arith s s' : step_arith _ step s s' -> step s s'.
Instance step_features : has_features "step" := ["var";"lam";"bool";"arith"].

Hint Constructors step.

(** *** Type preservation *)

(** # <a id="preservation" /> #*)
MetaCoq Run Compose
Lemma preservation on 5 : forall Gamma s s' A,
    has_ty Gamma s A -> step s s' -> has_ty Gamma s' A.
Hint Resolve preservation.

(** *** Weak Normalisation *)

Instance exp_features : has_features "exp" := ["var";"lam";"bool";"arith"].
Instance ty_features : has_features "ty" := ["lam";"bool";"arith"].

Fixpoint L (A : ty) : exp -> Prop :=
  match A with
  | In_ty_lam A => fun s => L_lam _ _ subst_exp step L A s
  | In_ty_bool A => fun s => L_bool  _ A s
  | In_ty_arith A => fun s => L_arith  _ A s
  end.

Definition E := E_ _ _ step L.

Fixpoint L_ren (s : exp) A xi {struct A} :
  L A s -> L A (ren_exp xi s).
Proof.
  destruct A.
  - pose proof (L_ren_lam _ _).
    eapply H; eauto.
  - pose proof (@L_ren_bool ty _ exp _).
    eapply H; eauto.
  - pose proof (@L_ren_arith ty _ exp _).
    eapply H; eauto.
Qed.
Hint Resolve L_ren.

(** # <a id="wn_fundamental" /> #*)
MetaCoq Run Compose
Lemma wn_fundamental on 3 : forall Gamma s A (H: has_ty Gamma s A),
  has_ty_sem _ _ subst_exp step L Gamma s A.
Hint Resolve wn_fundamental.

Definition whnf (e : exp) : Prop :=
  match e with
  | In_exp_var s => whnf_var s
  | In_exp_lam s => whnf_lam _ _ s
  | In_exp_bool s => whnf_bool _ s
  | In_exp_arith s => whnf_arith _ s
  end.

(** # <a id="L_val" /> #*)
MetaCoq Run Compose
Lemma L_val on 0 : forall (A : ty)  (s : exp),
    L A s -> whnf s.
Hint Resolve L_val.

Lemma wn s A:
  has_ty nil s A -> exists v, star step s v /\ whnf v.
Proof.
  intros C%wn_fundamental.
  specialize (C var_).
  unfold E_ in C. asimpl in C.
  edestruct C as (v&?&?).
  - unfold G. intros [|]; cbn; congruence.
  - exists v. split; eauto using L_val.
Qed.

(** *** Strong Normalisation *)

Fixpoint L_strong (A : ty):  exp -> Prop :=
  match A with
  | In_ty_lam A => fun s =>  @L_strong_lam _ exp _ _ subst_exp step whnf L_strong A s
  | In_ty_bool A => fun s => @L_strong_bool exp _ A s
  | In_ty_arith A => fun s => @L_strong_arith exp _ A s
  end.

Lemma E_strong_var A x:
  E_strong _ _ step whnf L_strong A (var_ x).
Proof.
  constructor.
  - cbn. contradiction.
  - intros. minversion H; inversion H0. 
Qed.
(** # <a id="whnf_anti_renaming" /> #*)
MetaCoq Run Compose
Lemma whnf_anti_renaming on 0 : forall s xi,
  whnf (ren_exp xi s) -> whnf s.

Fixpoint L_close_ren xi  (s : exp) A {struct A} :
  L_strong A s -> L_strong A (ren_exp xi s).
Proof.
  destruct A.
  - pose proof (L_close_ren_lam ty _).
    eapply H; eauto.
  - pose proof (@L_close_ren_bool ty _ exp _).
    eapply H; eauto.
  - pose proof (@L_close_ren_arith ty _ exp _).
    eapply H; eauto.
Qed.

MetaCoq Run Compose
Lemma step_inst on 3 : forall s s' sigma (H : step s s'),
  step (s[sigma]) (s'[sigma]).

Hint Resolve E_strong_var whnf_anti_renaming L_close_ren step_inst.

Lemma ren_preserves xi s :
  (forall (t : exp_lam ty exp), ren_exp xi s = inj t -> exists (s' : exp_lam ty exp) , s = inj s') /\
  (forall (t : exp_bool exp), ren_exp xi s = inj t -> exists (s' : exp_bool exp) , s = inj s') /\
  (forall (t : exp_arith exp), ren_exp xi s = inj t -> exists (s' : exp_arith exp) , s = inj s').
Proof.
  induction s; destruct e; cbn; repeat split; try inversion 1; subst; eauto.  
Qed.

Lemma ren_preserves_lam xi s :
  (forall (t : exp_lam ty exp), ren_exp xi s = inj t -> exists (s' : exp_lam ty exp) , s = inj s').
Proof.
  eapply ren_preserves.
Qed.
Hint Resolve ren_preserves_lam.

Lemma ren_preserves_bool xi s :
  (forall (t : exp_bool exp), ren_exp xi s = inj t -> exists (s' : exp_bool exp) , s = inj s').
Proof.
  eapply ren_preserves.
Qed.
Hint Resolve ren_preserves_bool.

Lemma ren_preserves_arith xi s :
  (forall (t : exp_arith exp), ren_exp xi s = inj t -> exists (s' : exp_arith exp) , s = inj s').
Proof.
  eapply ren_preserves.
Qed.
Hint Resolve ren_preserves_arith.
(** # <a id="step_anti_renaming" /> #*)
MetaCoq Run Compose
Lemma step_anti_renaming on 3 by inversion : forall s xi t (H : step (ren_exp xi s) t), exists t', t = ren_exp xi t' /\ step s t'.
Hint Resolve step_anti_renaming.

Lemma retract_step_lam :   forall (e : exp_lam ty exp) (e' : exp), step (inj e) e' -> step_lam _ exp subst_exp step (inj e) e'.
Proof.
  intros. inversion H; destruct e; subst; (try now inversion H0); eauto.
Qed.  
Hint Resolve retract_step_lam.

Lemma retract_step_bool :   forall (e : exp_bool exp) (e' : exp), step (inj e) e' -> step_bool exp step (inj e) e'.
Proof.
  intros. inversion H; destruct e; subst; (try now inversion H0); eauto.
Qed.  
Hint Resolve retract_step_bool.

Lemma retract_step_arith :   forall (e : exp_arith exp) (e' : exp), step (inj e) e' -> step_arith exp step (inj e) e'.
Proof.
  intros. inversion H; destruct e; subst; (try now inversion H0); eauto.
Qed.  
Hint Resolve retract_step_arith.
(** # <a id="sn_fundamental" /> #*)
MetaCoq Run Compose 
Fixpoint sn_fundamental on 3 : forall Gamma s A (H: has_ty Gamma s A),
  has_ty_sem_strong _ _ subst_exp step whnf L_strong Gamma s A.

Lemma sn_lam s A:
  has_ty nil s A -> sn step s.
Proof.
  intros H%sn_fundamental.
  specialize (H var_). asimpl in H.
  eapply E_strong_sn, H.
  intros []; cbn; congruence.
Qed.
