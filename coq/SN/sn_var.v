Require Export tactics header_metacoq.
From SN Require Export expressions defs.

(** ** mini-ML: Variables *)

Arguments var_ {_ _}.

Section MiniML_var.

Variable exp : Type.
Context `{retract (exp_var) exp}.

Variable ty : Type.

Hint Rewrite retract_works : retract_forward.

Variable ren_exp : forall   (xiexp : ( fin  ) -> fin ) (s : exp ), exp.
Variable retract_ren_exp : forall   (xiexp : ( fin  ) -> fin ) s, ren_exp xiexp (inj s) = ren_exp_var  _  _ xiexp s.
Variable subst_exp : forall   (sigmaexp : ( fin  ) -> exp ) (s : exp ), exp .
Variable retract_subst_exp : forall   (sigmaexp : ( fin  ) -> exp ) s, subst_exp sigmaexp (inj s) = subst_exp_var  _ sigmaexp s.
Variable var_exp : nat -> exp.
Variable subst_id_exp : forall s, subst_exp var_exp s = s.

Hint Rewrite retract_ren_exp retract_subst_exp : retract_forward.

(** *** Preservation *)

Variable has_ty : list ty -> exp -> ty -> Prop.

Inductive has_ty_var : list ty -> exp -> ty -> Prop :=
| var_has_ty Γ x A : nth_error Γ x = Datatypes.Some A -> has_ty_var Γ (var_ x) A.

Variable retract_has_ty : forall Gamma s A, has_ty_var Gamma s A -> has_ty Gamma s A.
Variable retract_has_ty_rev : forall Gamma s A, has_ty Gamma (inj s) A -> has_ty_var Gamma (inj s) A.

Instance retract_has_ty_instance Gamma s A:
  Imp (has_ty_var Gamma s A) (has_ty Gamma s A).
Proof. exact (retract_has_ty Gamma s A). Defined.

Instance retract_has_ty_rev_instance Gamma s A:
  ImpRev (has_ty Gamma (inj s) A) (has_ty_var Gamma (inj s) A).
Proof. exact (retract_has_ty_rev Gamma s A). Defined.

(** # <a id="has_ty_ren_var" /> #*)
Lemma has_ty_ren_var Gamma s A (IH : forall Gamma s A, has_ty Gamma s A -> forall (xi: nat -> nat) Delta, (forall x, nth_error Gamma x = nth_error Delta (xi x)) -> has_ty Delta (ren_exp xi s) A):
   has_ty_var Gamma s A -> forall xi Delta, (forall x, nth_error Gamma x = nth_error Delta (xi x)) -> has_ty Delta (ren_exp xi s) A.
Proof.
  intros C. inversion C; subst; intros; msimpl.
  - mconstructor. rewrite <- H1. eauto.
Defined.
(** # <a id="has_ty_subst_var" /> #*)
Lemma has_ty_subst_var Gamma s A (IH : forall Gamma s A, has_ty Gamma s A -> forall sigma Delta, (forall x A, nth_error Gamma x = Datatypes.Some A -> has_ty Delta (sigma x) A) -> has_ty Delta (subst_exp sigma s) A):
   has_ty_var Gamma s A -> forall sigma Delta, (forall x A, nth_error Gamma x = Datatypes.Some A -> has_ty Delta (sigma x) A) -> has_ty Delta (subst_exp sigma s) A.
Proof.
  intros C. inversion C; subst; intros.
  - msimpl. now eapply H1. 
Defined.

Inductive step_var : exp -> exp -> Prop := .
Variable step : exp -> exp -> Prop.

(** # <a id="step_anti_renaming_var" /> #*)
Lemma step_anti_renaming_var s xi t : step_var (ren_exp xi s) t -> exists t', t = ren_exp xi t' /\ step s t'.
Proof.
  inversion 1.
Defined.

(** # <a id="step_inst_var" /> #*)
Lemma step_inst_var s s' sigma :
  step_var s s' -> step (subst_exp sigma s) (subst_exp sigma s').
Proof.
  inversion 1.
Qed.

(** # <a id="preservation_var" /> #*)
Lemma preservation_var Gamma s s' A :
  has_ty Gamma s A -> step_var s s' -> has_ty Gamma s' A.
Proof.
  inversion 2.
Defined.

(** *** Weak Head Normalisation *)

MetaCoq Run Modular Fixpoint whnf_var where exp_var extends exp :=
  fun (e : exp_var) =>
  match e with
  | var _ => False
  end.

Variable whnf_whnf_var : forall e, whnf (inj e) = whnf_var e.

Hint Rewrite whnf_whnf_var : retract_forward.
Hint Rewrite <- whnf_whnf_var : retract_rev.

(** # <a id="whnf_anti_renaming_var" /> #*)
Lemma whnf_anti_renaming_var s xi :
  whnf (ren_exp_var _  _ xi s) -> whnf (inj s).
Proof.
  destruct s; msimpl; eauto.
Qed.

Variable ren_preserves : forall xi s t, ren_exp xi s = inj t -> exists s', s = inj s'.

Lemma ren_preserves_var : forall s xi x, ren_exp xi s = var_ x -> exists x', s = var_ x' /\ xi x' = x.
Proof.
  intros. destruct (ren_preserves _ _ _ H0) as (? & ?). subst.

  rewrite retract_ren_exp in H0.
  destruct x0; minversion H0.
  exists n. eauto.
Qed.

Variable L : ty -> exp -> Prop.

Definition E_ (A : ty) (s : exp) : Prop :=
  exists v, star step s v /\ L A v.

Definition G (Gamma : list ty) : (nat -> exp)  -> Prop :=
  fun σ => forall (x : nat) A, nth_error Gamma x = Datatypes.Some A -> L A (σ x) .

Definition has_ty_sem (Gamma : list ty) (s: exp) (A: ty) : Prop :=
  forall sigma, G Gamma sigma -> E_ A (subst_exp sigma s).

Lemma val_inclusion A e :
  L A e -> E_ A e.
Proof. intros. unfold E_. exists e. split; eauto. Qed.

Lemma wn_fundamental_var Gamma s A :
  has_ty_var Gamma s A -> has_ty_sem Gamma s A.
Proof.
  intros C. intros sigma D. unfold E_. inversion C; subst.
  specialize (D _ _ H0). msimpl. eauto.
Defined.

(** *** Strong Normalisation  *)

Variable L_strong: ty -> exp -> Prop.

Inductive E_strong' (L_A : exp -> Prop) (s : exp) :  Prop :=
 | E_strong_In  : (whnf s -> L_A s) -> (forall s', step s s' -> E_strong' L_A s') -> E_strong' L_A s.

Definition E_strong (A : ty) : exp -> Prop :=
  E_strong' (L_strong A).

Lemma E_strong_sn s A:
  E_strong A s -> sn step s.
Proof.
  induction 1. constructor. intros s' HH. eauto.
Qed.

Lemma E_strong_step s L_A :
  E_strong' L_A s -> forall s', step s s' -> E_strong' L_A s'.
Proof.
 induction 1; eauto.
Qed.

Lemma E_strong_base  s A :
  whnf s -> E_strong A s -> L_strong A s.
Proof.
  intros C []; eauto.
Qed.

Definition G_strong (Gamma : list ty) : (nat -> exp)  -> Prop :=
  fun σ => forall (x : nat) A, nth_error Gamma x = Datatypes.Some A -> E_strong A (σ x) .

Definition has_ty_sem_strong (Gamma : list ty) (s: exp) (A: ty) : Prop :=
  forall sigma, G_strong Gamma sigma -> E_strong A (subst_exp sigma s).

Lemma sn_fundamental_var Gamma s A :
  has_ty_var Gamma s A -> has_ty_sem_strong Gamma s A.
Proof.
  inversion 1. subst. unfold has_ty_sem_strong. intros.
  unfold G_strong in H2. specialize (H2 _ _ H1). now msimpl.
Qed.
  
End MiniML_var.
