From SN Require Export expressions sn_var.


(** ** mini-ML: Arithmetic terms *)

Section MiniML_Arith.

Variable ty : Type.
Context `{HT : retract (ty_arith) ty}.
Variable exp : Type.
Context `{retract (exp_arith exp) exp}.

Hint Rewrite retract_works : retract_forward.

Variable ren_exp : forall   (xiexp : ( fin  ) -> fin ) (s : exp ), exp.
Variable retract_ren_exp : forall   (xiexp : ( fin  ) -> fin ) s, ren_exp xiexp (inj s) = ren_exp_arith  _  ren_exp _ xiexp s.
Variable subst_exp : forall   (sigmaexp : ( fin  ) -> exp ) (s : exp ), exp .
Variable retract_subst_exp : forall   (sigmaexp : ( fin  ) -> exp ) s, subst_exp sigmaexp (inj s) = subst_exp_arith _ subst_exp _ sigmaexp s.

Hint Rewrite retract_ren_exp retract_subst_exp : retract_forward.
Hint Rewrite retract_ren_exp retract_subst_exp : retract_rev.

(** *** Preservation *)

Variable has_ty : list ty -> exp -> ty -> Prop.

Inductive has_ty_arith (Gamma : list ty) : exp -> ty -> Prop :=
| hasty_ConstNat (n : nat): has_ty_arith Gamma (constNat_ n) natTy_
| hasty_plus (s t : exp) : has_ty Gamma s natTy_ -> has_ty Gamma t natTy_ -> has_ty_arith Gamma (plus_ s t) natTy_.

Variable retract_has_ty : forall Gamma s A, has_ty_arith Gamma s A -> has_ty Gamma s A.
Variable retract_has_ty_rev : forall Gamma s A, has_ty Gamma (inj s) A -> has_ty_arith Gamma (inj s) A.

Instance retract_has_ty_instance Gamma s A:
  Imp (has_ty_arith Gamma s A) (has_ty Gamma s A).
Proof. exact (retract_has_ty Gamma s A). Defined.

Instance retract_has_ty_rev_instance Gamma s A:
  ImpRev (has_ty Gamma (inj s) A) (has_ty_arith Gamma (inj s) A).
Proof. exact (retract_has_ty_rev Gamma s A). Defined.

Variable step: exp -> exp -> Prop.

Inductive step_arith : exp -> exp -> Prop :=
| stepPlus n m : step_arith (plus_ (constNat_ n) (constNat_ m)) (constNat_ (n + m))
| stepPlus1 s s' t : step s s' -> step_arith (plus_ s t) (plus_ s' t)
| stepPlus2 s t t' : step t t' -> step_arith (plus_ s t) (plus_ s t').

Variable retract_step: forall e e', step_arith e e' -> step e e'.
Variable retract_step_rev: forall e e', step (inj e) e' -> step_arith (inj e) e'.

Instance retract_step_instance e e':
  Imp (step_arith e e') (step e e').
Proof. exact (retract_step e e'). Defined.

Instance retract_step_rev_instance e e':
  ImpRev  (step (inj e) e') (step_arith (inj e) e').
Proof. exact (retract_step_rev e e'). Defined.

(** # <a id="has_ty_ren_arith" /> #*)
MetaCoq Run Modular Lemma has_ty_ren_arith
where exp_arith exp extends exp with [~ has_ty_arith ~> has_ty ~] :
  forall Gamma s A,
   has_ty_arith Gamma s A -> forall xi Delta, (forall x, nth_error Gamma x = nth_error Delta (xi x)) -> has_ty Delta (ren_exp xi s) A.
Next Obligation.
  intros IH Gamma s A. intros C. inversion C; subst; intros; msimpl.
  - mconstructor.
  - mconstructor.
    + eapply IH ; eassumption.
    + eapply IH; eassumption.
Defined.
(** # <a id="has_ty_subst_arith" /> #*)
MetaCoq Run Modular Lemma has_ty_subst_arith
where exp_arith exp extends exp with [~ has_ty_arith ~> has_ty ~] :
 forall Gamma s A, has_ty_arith Gamma s A -> forall sigma Delta, (forall x A, nth_error Gamma x = Datatypes.Some A -> has_ty Delta (sigma x) A) -> has_ty Delta (subst_exp sigma s) A.
Next Obligation.
  intros IH Gamma s A C. inversion C; subst; intros.
  - mconstructor.
  - mconstructor.
    + eapply IH ; eassumption.
    + eapply IH; eassumption.
Defined.
(** # <a id="preservation_arith" /> #*)
MetaCoq Run Modular Lemma preservation_arith
where exp_arith exp extends exp with [~ step_arith ~> step ~] :
 forall Gamma s s' A, has_ty Gamma s A -> step_arith s s' -> has_ty Gamma s' A.
Next Obligation.
  intros IH Gamma s s' A C D. revert Gamma A C. induction D; intros.
  - minversion C. mconstructor.
  - minversion C. mconstructor; eauto.
  - minversion C. mconstructor; eauto.
Defined.

(** *** Weak Head Normalisation *)

MetaCoq Run Modular Fixpoint L_arith where ty_arith extends ty :=
fun (A : ty_arith) =>
  match A with
  | natTy => fun e => match retr e with
                  | Datatypes.Some (constNat n) => True
                  | _ => False
                  end
  end.

Variable retract_L : forall A e, L_arith A e = L (inj A) e.

Lemma star_plus1 s s' t :
  star step s s' -> star step (plus_ s t) (plus_ s' t).
Proof.
  induction 1; eauto.
  - econstructor; try apply IHstar.
    now mconstructor.
Qed.

Lemma star_plus2 s t' t :
  star step t t' -> star step (plus_ s t) (plus_ s t').
Proof.
  induction 1; eauto.
  - econstructor; try apply IHstar.
    now mconstructor.
Qed.

MetaCoq Run Modular Fixpoint whnf_arith where exp_arith exp extends exp :=
fun e : exp_arith exp =>
  match e with
  | constNat _  => True
  | _ => False
  end.

Variable whnf_whnf_arith : forall e, whnf (inj e) = whnf_arith e.

Hint Rewrite <- retract_L : retract_forward.
Hint Rewrite whnf_whnf_arith : retract_forward.
Hint Rewrite <- retract_L whnf_whnf_arith : retract_rev.

MetaCoq Run Modular Lemma L_val_arith
where ty_arith extends ty with [~ L_arith ~> L ~] :
forall (A : ty_arith)  (s : exp), L_arith A s -> whnf s.
Next Obligation.
  intros IH A s. destruct A; cbn; eauto; repeat rewrite whnf_whnf_arith.
  destruct (retr s) eqn:HH; try contradiction.
  minversion HH. 
  destruct e; intros; cbn; eauto. firstorder. 
  now rewrite whnf_whnf_arith. 
Qed.

MetaCoq Run Modular Lemma L_ren_arith
where ty_arith extends ty with [~ L_arith ~> L ~] :
  forall s A xi, L_arith A s -> L (inj A) (ren_exp xi s).
Next Obligation.
  intros IH s A xi. revert s xi. induction A; eauto.
  - intros. cbn in H0. destruct (retr s) eqn:HH; try contradiction.
    apply retract_tight in HH. subst. destruct e; try contradiction.
    now msimpl. 
Defined.

MetaCoq Run Modular Lemma wn_fundamental_arith 
where exp_arith exp extends exp with [~ has_ty_arith ~> has_ty ~] :
forall Gamma s A, has_ty_arith Gamma s A -> has_ty_sem _ _ subst_exp step L Gamma s A.
Next Obligation.
  intros IH Gamma s A. intros C. intros sigma D. unfold E_. inversion C; subst.
  - exists (constNat_ n). now msimpl.
  - rename s0 into s.
    destruct (IH _ _ _ H0 _ D) as (s'&?&?).
    destruct (IH _ _ _ H1 _ D) as (t'&?&?).
    msimpl_in H3. destruct (retr s') eqn:HH; try inversion H3.
    destruct e; try inversion H3. 
    msimpl_in HH. subst.
    clear H3.
    msimpl.
    msimpl_in H5. destruct (retr t') eqn:HHH; try inversion H5.
    destruct e; try inversion H5. 
    msimpl_in HHH. subst.
    clear H5.

    exists (constNat_ (n + n0)).
    split.
    + eapply star_trans. eapply star_plus1. eauto.
      eapply star_trans. eapply star_plus2. eauto.
      
      econstructor; [mconstructor|eauto].
    + now msimpl. 
Defined.

(** *** Strong Normalisation *)

MetaCoq Run Modular Fixpoint L_strong_arith where ty_arith extends ty :=
fun  (A : ty_arith ) =>
  match A with
   | natTy_ => fun e => match retr e with
                      | Datatypes.Some (constNat b) => True
                      | _ => False
                   end
  end.

Variable retract_L_strong  : forall A e,  L_strong_arith A e = L_strong (inj A) e.
Hint Rewrite <- retract_L_strong : retract_forward.

Arguments has_ty_sem_strong {_} {_} {_} {_} {_}.

Lemma whnf_anti_renaming_arith s xi :
  whnf (ren_exp_arith _  ren_exp _ xi s) -> whnf (inj s).
Proof.
  destruct s; msimpl; eauto.
Qed.

Variable ren_preserves : forall xi s t, ren_exp xi s = inj t -> exists s', s = inj s'.

Lemma ren_preserves_Plus : forall s xi t u, ren_exp xi s = plus_ t u -> exists t' u', s = plus_ t' u'
                                                                         /\ ren_exp xi t' = t
                                                                         /\ ren_exp xi u' = u.
Proof.
  intros. destruct (ren_preserves _ _ _ H0) as (? & ?). subst.
  msimpl_in H0.
  destruct x; minversion H0.
  exists e, e0. split; eauto.
Qed.

Lemma ren_preserves_constNat : forall s xi b, ren_exp xi s = constNat_ b -> s = constNat_ b.
Proof.
  intros. destruct (ren_preserves _ _ _ H0) as (? & ?). subst.
  msimpl_in H0.
  destruct x; minversion H0.
  reflexivity.
Qed.

Variable step_anti_renaming : forall s xi t,  step (ren_exp xi s) t -> exists t', t = ren_exp xi t' /\ step s t'.

MetaCoq Run Modular Lemma step_anti_renaming_arith
where exp_arith exp extends exp with [~ step_arith ~> step ~] :
  forall  s' xi t, step_arith (ren_exp xi s') t -> exists t', t = ren_exp xi t' /\ step s' t'.
Next Obligation.
  intros IH s' xi t. inversion 1; eauto; msimpl.
  - symmetry in H2. eapply ren_preserves_Plus in H2 as (? & ? & ? & ? & ?). subst.
    eapply ren_preserves_constNat in H3. subst.
    eapply ren_preserves_constNat in H4. subst.
    exists (constNat_ (n + m)). split; eauto. now msimpl.
    mconstructor.
  - subst. symmetry in H1. eapply ren_preserves_Plus in H1 as (? & ? & ? & ? & ?). subst.
    eapply step_anti_renaming in H2 as (? & ? & ?). subst.
    exists (plus_ x1 x0).
    msimpl. split; eauto.
    mconstructor. eauto.
  - subst. symmetry in H1. eapply ren_preserves_Plus in H1 as (? & ? & ? & ? & ?). subst.
    eapply step_anti_renaming in H2 as (? & ? & ?). subst.
    exists (plus_ x x1). msimpl. split; eauto.
    mconstructor. eauto.
Defined.

Lemma L_close_ren_arith xi s A :
  L_strong_arith A s -> L_strong (inj A) (ren_exp xi s).
Proof.
  induction A; eauto. msimpl. unfold L_strong_arith.
  destruct (retr s) eqn:HH; try contradiction.
  minversion HH. clear H0.
  destruct e; try contradiction.
  intros. msimpl. eassumption.
Qed.

MetaCoq Run Modular Lemma step_inst_arith
where exp_arith exp extends exp with [~ step_arith ~> step ~] :
forall s s' sigma, step_arith s s' -> step (subst_exp sigma s) (subst_exp sigma s').
Next Obligation.
  intros IH s s' sigma.
  destruct 1; msimpl; eauto.
  all: try mconstructor; eauto.
Defined.

Arguments has_ty_sem_strong : clear implicits.

MetaCoq Run Modular Lemma sn_fundamental_arith
where ty_arith extends ty with [~ has_ty_arith ~> has_ty ~] : 
forall Gamma s A, has_ty_arith Gamma s A -> @has_ty_sem_strong _ _ subst_exp step whnf L_strong Gamma s A.
Next Obligation.
  intros IH Gamma s A. induction 1.
  - unfold has_ty_sem_strong. intros. msimpl.
    constructor.
    + intros. msimpl. hnf.
      destruct retr eqn:EE; minversion EE. econstructor.
    + intros. minversion H1.
  - unfold has_ty_sem_strong. intros.
    assert (IH1 := IH _ _ _ H0 _ H2).
    assert (IH2 := IH _ _ _ H1 _ H2).
    apply E_strong_sn in IH1. apply E_strong_sn in IH2 as IH2'. 
    msimpl. remember (subst_exp sigma s) as s'. remember (subst_exp sigma t) as t'.
    clear Heqs' Heqt'. clear s t H0 H1.
    revert t' IH2 IH2'.
    induction IH1 as [s'].
    intros t' IH2 IH2'. induction IH2' as [t'].  
    constructor.
    + intros. rewrite whnf_whnf_arith in *. contradiction.
    + intros.
      minversion H5; eauto using E_strong_step.
      * econstructor. intros.
        -- intros. msimpl. hnf.
           destruct retr eqn:EE; minversion EE. econstructor.
        -- intros. minversion H6.
      * eapply H1; eauto.
      * eapply H4; eauto. eapply E_strong_step; try eapply H9; eauto.
Defined.

End MiniML_Arith.
