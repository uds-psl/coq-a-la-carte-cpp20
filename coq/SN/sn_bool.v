From SN Require Export expressions sn_var.


(** ** MiniML: Boolean expressions *)

Section MiniML_Bool.

Variable ty : Type.
Context `{HT : retract (ty_bool) ty}.
Variable exp : Type.
Context `{retract (exp_bool exp) exp}.

Hint Rewrite retract_works : retract_forward.

Variable ren_exp : forall   (xiexp : ( fin  ) -> fin ) (s : exp ), exp.
Variable retract_ren_exp : forall   (xiexp : ( fin  ) -> fin ) s, ren_exp xiexp (inj s) = ren_exp_bool  _  ren_exp _ xiexp s.
Variable subst_exp : forall   (sigmaexp : ( fin  ) -> exp ) (s : exp ), exp .
Variable retract_subst_exp : forall   (sigmaexp : ( fin  ) -> exp ) s, subst_exp sigmaexp (inj s) = subst_exp_bool _ subst_exp _ sigmaexp s.

Hint Rewrite retract_ren_exp retract_subst_exp : retract_forward.
Hint Rewrite retract_ren_exp retract_subst_exp : retract_rev.

(** *** Preservation *)

Variable has_ty : list ty -> exp -> ty -> Prop.

Inductive has_ty_bool (Gamma : list ty) : exp -> ty -> Prop :=
| hasty_ConstBool (b : bool): has_ty_bool Gamma (constBool_ b) boolTy_
| hasty_If (s t u : exp) A : has_ty Gamma s boolTy_ -> has_ty Gamma t A -> has_ty Gamma u A -> has_ty_bool Gamma (If_ s t u) A.

Variable retract_has_ty : forall Gamma s A, has_ty_bool Gamma s A -> has_ty Gamma s A.
Variable retract_has_ty_rev : forall Gamma s A, has_ty Gamma (inj s) A -> has_ty_bool Gamma (inj s) A.

Instance retract_has_ty_instance Gamma s A:
  Imp (has_ty_bool Gamma s A) (has_ty Gamma s A).
Proof. exact (retract_has_ty Gamma s A). Defined.

Instance retract_has_ty_rev_instance Gamma s A:
  ImpRev (has_ty Gamma (inj s) A) (has_ty_bool Gamma (inj s) A).
Proof. exact (retract_has_ty_rev Gamma s A). Defined.

Variable step: exp -> exp -> Prop.

Inductive step_bool : exp -> exp -> Prop :=
| stepIfBeta b t u : step_bool (If_ (constBool_ b) t u) (if b then t else u)
| stepIf1 s s' t u : step s s' -> step_bool (If_ s t u) (If_ s' t u)
| stepIf2 s t t' u : step t t' -> step_bool (If_ s t u) (If_ s t' u)
| stepIf3 s t u u': step u u' -> step_bool (If_ s t u) (If_ s t u').

Variable retract_step: forall e e', step_bool e e' -> step e e'.
Variable retract_step_rev: forall e e', step (inj e) e' -> step_bool (inj e) e'.

Instance retract_step_instance e e':
  Imp (step_bool e e') (step e e').
Proof. exact (retract_step e e'). Defined.

Instance retract_step_rev_instance e e':
  ImpRev  (step (inj e) e') (step_bool (inj e) e').
Proof. exact (retract_step_rev e e'). Defined.
(** # <a id="has_ty_ren_bool" /> #*)
MetaCoq Run Modular Lemma has_ty_ren_bool
where exp_bool exp extends exp with [~ has_ty_bool ~> has_ty ~] :
  forall Gamma s A,
   has_ty_bool Gamma s A -> forall xi Delta, (forall x, nth_error Gamma x = nth_error Delta (xi x)) -> has_ty Delta (ren_exp xi s) A.
Next Obligation.
  intros IH Gamma s A C. inversion C; subst; intros; msimpl.
  - mconstructor.
  - mconstructor.
    + eapply IH ; eassumption.
    + eapply IH; eassumption.
    + eapply IH; eassumption.
Defined.
(** # <a id="has_ty_subst_bool" /> #*)
MetaCoq Run Modular Lemma has_ty_subst_bool
where exp_bool exp extends exp with [~ has_ty_bool ~> has_ty ~] :
 forall Gamma s A, has_ty_bool Gamma s A -> forall sigma Delta, (forall x A, nth_error Gamma x = Datatypes.Some A -> has_ty Delta (sigma x) A) -> has_ty Delta (subst_exp sigma s) A.
Next Obligation.
  intros IH Gamma s A C. inversion C; subst; intros.
  - mconstructor.
  - mconstructor.
    + eapply IH; eassumption.
    + eapply IH; eassumption.
    + eapply IH; eassumption.
Defined.
(** # <a id="preservation_bool" /> #*)
MetaCoq Run Modular Lemma preservation_bool
where exp_bool exp extends exp with [~ step_bool ~> step ~] :
 forall Gamma s s' A, has_ty Gamma s A -> step_bool s s' -> has_ty Gamma s' A.
Next Obligation.
  intros IH Gamma s s' A. intros C D. revert Gamma A C. induction D; intros.
  - minversion C. destruct b; eauto.
  - minversion C. mconstructor; eauto.
  - minversion C. mconstructor; eauto.
  - minversion C.
    mconstructor; eauto.
Defined.

(** *** Weak Head Normalisation *)

(** # <a id="L_bool" /> #*)
MetaCoq Run Modular Fixpoint L_bool where ty_bool extends ty :=
fun (A : ty_bool) =>
  match A with
  | Bool_ => fun e => match retr e with
                      | Datatypes.Some (constBool b) => True
                      | _ => False
                      end
  end.

Variable retract_L : forall A e, L (inj A) e = L_bool A e.

Lemma star_If1 s s' t u :
  star step s s' -> star step (If_ s t u) (If_ s' t u).
Proof.
  induction 1; eauto.
  - econstructor; try apply IHstar.
    apply retract_step. now econstructor.
Qed.
(** # <a id="whnf_bool" /> #*)
MetaCoq Run Modular Fixpoint whnf_bool where exp_bool exp extends exp :=
fun e : exp_bool exp =>
  match e with
  | constBool _  => True
  | _ => False
  end.

Variable whnf_whnf_bool : forall e, whnf (inj e) = whnf_bool e.

Hint Rewrite retract_L whnf_whnf_bool : retract_forward.
Hint Rewrite retract_L whnf_whnf_bool : retract_rev.

(** # <a id="L_val_bool" /> #*)
MetaCoq Run Modular Lemma L_val_bool
where ty_bool extends ty with [~ L_bool ~> L ~] :
forall (A : ty_bool)  (s : exp), L_bool A s -> whnf s.
Next Obligation.
  unfold L_bool.
  intros IH A s. destruct A; cbn; eauto; repeat rewrite whnf_whnf_bool.
  destruct (retr s) eqn:HH; try contradiction. rewrite <- (retract_tight HH). (* TODO: This should be automated. *)
  msimpl.
  destruct e; intros; cbn; eauto.
Qed.

(** # <a id="L_ren_bool" /> #*)
MetaCoq Run Modular Lemma L_ren_bool
where ty_bool extends ty with [~ L_bool ~> L ~] :
  forall s A xi, L_bool A s -> L (inj A) (ren_exp xi s).
Next Obligation.
  unfold L_bool.
  intros I s A xi. revert s xi. induction A; eauto.
  - intros. cbn in H0. destruct (retr s) eqn:HH; try contradiction.
    minversion HH. subst. destruct e; try contradiction.
    msimpl. red. now msimpl.
Defined.

(** # <a id="wn_fundamental_bool" /> #*)
MetaCoq Run Modular Lemma wn_fundamental_bool 
where exp_bool exp extends exp with [~ has_ty_bool ~> has_ty ~] :
forall Gamma s A, has_ty_bool Gamma s A -> has_ty_sem _ _ subst_exp step L Gamma s A.
Next Obligation.
  intros IH Gamma s A. intros C. intros sigma D. unfold E_. inversion C; subst.
  - exists (constBool_ b). msimpl.
    split.
    + constructor.
    + msimpl. red. now msimpl.      
  - rename s0 into s.
    destruct (IH _ _ _ H0 _ D) as (s'&?&?).
    msimpl_in H4. hnf in H4. destruct (retr s') eqn:HH; try inversion H4.
    destruct e; try inversion H4.
    minversion HH. 
    clear H4.
    msimpl.
    destruct b.
    + destruct (IH _ _ _ H1 _ D) as (t'&?&?).
      exists t'. split.
      * eapply star_trans. apply (star_If1 _ _ _ _ H3).
        econstructor; [mconstructor|eauto].
      * eauto.
    + destruct (IH _ _ _ H2 _ D) as (u'&?&?).
      exists u'. split.
      * eapply star_trans. apply (star_If1 _ _ _ _ H3).
        econstructor; [mconstructor|eauto].
      * eauto.
Defined.

(** *** Strong Normalisation *)

(** # <a id="L_strong_bool" /> #*)
MetaCoq Run Modular Fixpoint L_strong_bool where ty_bool extends ty :=
fun  (A : ty_bool ) =>
  match A with
   | Bool_ => fun e => match retract_R e with
                      | Datatypes.Some (constBool b) => True
                      | _ => False
                   end
  end.

Variable retract_L_strong  : forall A e,  L_strong_bool A e = L_strong (inj A) e.
Hint Rewrite <- retract_L_strong : retract_forward.

Arguments has_ty_sem_strong {_} {_} {_} {_} {_}.

(** # <a id="whnf_anti_renaming_bool" /> #*)
Lemma whnf_anti_renaming_bool s xi :
  whnf (ren_exp_bool _  ren_exp _ xi s) -> whnf (inj s).
Proof.
  destruct s; msimpl; eauto.
Qed.

Variable ren_preserves : forall xi s t, ren_exp xi s = inj t -> exists s', s = inj s'.

Lemma ren_preserves_If : forall s xi t u v, ren_exp xi s = If_ t u v -> exists t' u' v', s = If_ t' u' v'
                                                                                  /\ ren_exp xi t' = t
                                                                                  /\ ren_exp xi u' = u
                                                                                  /\ ren_exp xi v' = v.
Proof.
  intros. destruct (ren_preserves _ _ _ H0) as (? & ?). subst.
  msimpl_in H0. destruct x; minversion H0.
  exists e, e0, e1. split; eauto.
Qed.

Lemma ren_preserves_constBool : forall s xi b, ren_exp xi s = constBool_ b -> s = constBool_ b.
Proof.
  intros. destruct (ren_preserves _ _ _ H0) as (? & ?). subst.
  msimpl_in H0. now destruct x; minversion H0.
Qed.

(** # <a id="step_anti_renaming_bool" /> #*)
MetaCoq Run Modular Lemma step_anti_renaming_bool
where exp_bool exp extends exp with [~ step_bool ~> step ~] :
  forall  s' xi t, step_bool (ren_exp xi s') t -> exists t', t = ren_exp xi t' /\ step s' t'.
Next Obligation.
  intros IH s' xi t. inversion 1; eauto; msimpl.
  - destruct b; subst.
    + symmetry in H2. eapply ren_preserves_If in H2 as (? & ? & ? & ? & ? & ? & ?). subst.
      eapply ren_preserves_constBool in H2. subst.
      exists x0. split; eauto. mconstructor.
    + symmetry in H2. eapply ren_preserves_If in H2 as (? & ? & ? & ? & ? & ? & ?). subst.
      eapply ren_preserves_constBool in H2. subst.
      exists x1. split; eauto. mconstructor.
  - subst. symmetry in H1. eapply ren_preserves_If in H1 as (? & ? & ? & ? & ? & ? & ?). subst.
    eapply IH in H2 as (? & ? & ?). subst.
    exists (If_ x2 x0 x1). msimpl. split; eauto.
    mconstructor. eauto.
  - subst. symmetry in H1. eapply ren_preserves_If in H1 as (? & ? & ? & ? & ? & ? & ?). subst.
    eapply IH in H2 as (? & ? & ?). subst.
    exists (If_ x x2 x1). msimpl. split; eauto.
    mconstructor. eauto.
  - subst. symmetry in H1. eapply ren_preserves_If in H1 as (? & ? & ? & ? & ? & ? & ?). subst.
    eapply IH in H2 as (? & ? & ?). subst.
    exists (If_ x x0 x2). msimpl. split; eauto.
    mconstructor. eauto.
Defined.

Lemma L_close_ren_bool xi s A :
  L_strong_bool A s -> L_strong (inj A) (ren_exp xi s).
Proof.
  induction A; eauto. msimpl. unfold L_strong_bool.
  destruct (retr s) eqn:HH; try contradiction.
  minversion HH.
  destruct e; try contradiction.
  intros. msimpl. eassumption.
Qed.

(** # <a id="step_inst_bool" /> #*)
MetaCoq Run Modular Lemma step_inst_bool
where exp_bool exp extends exp with [~ step_bool ~> step ~] :
forall s s' sigma, step_bool s s' -> step (subst_exp sigma s) (subst_exp sigma s').
Next Obligation.
  intros _ s s' sigma.
  destruct 1; msimpl; eauto.
  all: try mconstructor; eauto.
  - destruct b; mconstructor; eauto.
Defined.

Arguments has_ty_sem_strong : clear implicits.

(** # <a id="sn_fundamental_bool" /> #*)
MetaCoq Run Modular Lemma sn_fundamental_bool
where ty_bool extends ty with [~ has_ty_bool ~> has_ty ~] : 
forall Gamma s A, has_ty_bool Gamma s A -> has_ty_sem_strong _ _ subst_exp step whnf L_strong Gamma s A.
Next Obligation.
  intros IH Gamma s A. induction 1.
  - unfold has_ty_sem_strong. intros. msimpl.
    constructor.
    + intros. msimpl. hnf.
      destruct retr eqn:EE; minversion EE. econstructor.
    + intros. minversion H1.
  - unfold has_ty_sem_strong. intros.
    assert (IH1 := IH _ _ _ H0 _ H3).
    assert (IH2 := IH _ _ _ H1 _ H3).
    assert (IH3 := IH _ _ _ H2 _ H3).
    apply E_strong_sn in IH1. apply E_strong_sn in IH2 as IH2'. apply E_strong_sn in IH3 as IH3'.
    msimpl. remember (subst_exp sigma s) as s'. remember (subst_exp sigma t) as t'.
    remember (subst_exp sigma u) as u'. clear Heqs' Heqt' Hequ'. clear s t u H0 H1 H2.
    revert t' IH2 IH2' u' IH3 IH3'.
    induction IH1 as [s'].
    intros t' IH2 IH2'. induction IH2' as [t'].  intros u' IH3 IH3'. induction IH3' as [u'].
    constructor.
    + intros. rewrite whnf_whnf_bool in *. contradiction.
    + intros.
      minversion H7; eauto using E_strong_step.
      * destruct b; eauto.
      * eapply H1; eauto.
      * eapply H4; eauto. eapply E_strong_step; try eapply H9; eauto.
      * eapply H6; eauto. eapply E_strong_step; try eapply H9; eauto.
Defined.

End MiniML_Bool.
