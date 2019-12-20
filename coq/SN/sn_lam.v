Require Export tactics header_metacoq.
From SN Require Export expressions defs.
Require Export FunctionalExtensionality.


(** ** mini-ML: Lambda expressions *)

Section MiniML_Lambda.

Variable ty : Type.
Context {HT_lam : included ty_lam ty}.

Variable exp : Type.
Context `{Hr : retract exp_var exp}.
Context `{retract (exp_lam ty exp) exp}.


Hint Rewrite retract_works : retract_forward.

Notation var_exp := (var_ _ _).
Variable upRen_exp_exp : forall   (xi : ( fin  ) -> fin ), ( fin  ) -> fin .
Variable ren_exp : forall   (xiexp : ( fin  ) -> fin ) (s : exp ), exp .
Variable up_exp_exp : forall   (sigma : ( fin  ) -> exp ), ( fin  ) -> exp .
Variable subst_exp : forall   (sigmaexp : ( fin  ) -> exp ) (s : exp ), exp .
Variable upId_exp_exp : forall  (sigma : ( fin  ) -> exp ) (Eq : forall x, sigma x = (var_exp ) x), forall x, (up_exp_exp sigma) x = (var_exp ) x.
Variable idSubst_exp : forall  (sigmaexp : ( fin  ) -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp ), subst_exp sigmaexp s = s.
Variable upExtRen_exp_exp : forall   (xi : ( fin  ) -> fin ) (zeta : ( fin  ) -> fin ) (Eq : forall x, xi x = zeta x), forall x, (upRen_exp_exp xi) x = (upRen_exp_exp zeta) x.
Variable extRen_exp : forall   (xiexp : ( fin  ) -> fin ) (zetaexp : ( fin  ) -> fin ) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp ), ren_exp xiexp s = ren_exp zetaexp s.
Variable upExt_exp_exp : forall   (sigma : ( fin  ) -> exp ) (tau : ( fin  ) -> exp ) (Eq : forall x, sigma x = tau x), forall x, (up_exp_exp sigma) x = (up_exp_exp tau) x.
Variable ext_exp : forall   (sigmaexp : ( fin  ) -> exp ) (tauexp : ( fin  ) -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp ), subst_exp sigmaexp s = subst_exp tauexp s.
Variable up_ren_ren_exp_exp : forall    (xi : ( fin  ) -> fin ) (tau : ( fin  ) -> fin ) (theta : ( fin  ) -> fin ) (Eq : forall x, (funcomp tau xi) x = theta x), forall x, (funcomp (upRen_exp_exp tau) (upRen_exp_exp xi)) x = (upRen_exp_exp theta) x.
Variable compRenRen_exp : forall    (xiexp : ( fin  ) -> fin ) (zetaexp : ( fin  ) -> fin ) (rhoexp : ( fin  ) -> fin ) (Eqexp : forall x, (funcomp zetaexp xiexp) x = rhoexp x) (s : exp ), ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s.
Variable up_ren_subst_exp_exp : forall    (xi : ( fin  ) -> fin ) (tau : ( fin  ) -> exp ) (theta : ( fin  ) -> exp ) (Eq : forall x, (funcomp tau xi) x = theta x), forall x, (funcomp (up_exp_exp tau) (upRen_exp_exp xi)) x = (up_exp_exp theta) x.
Variable compRenSubst_exp : forall    (xiexp : ( fin  ) -> fin ) (tauexp : ( fin  ) -> exp ) (thetaexp : ( fin  ) -> exp ) (Eqexp : forall x, (funcomp tauexp xiexp) x = thetaexp x) (s : exp ), subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s.
Variable up_subst_ren_exp_exp : forall    (sigma : ( fin  ) -> exp ) (zetaexp : ( fin  ) -> fin ) (theta : ( fin  ) -> exp ) (Eq : forall x, (funcomp (ren_exp zetaexp) sigma) x = theta x), forall x, (funcomp (ren_exp (upRen_exp_exp zetaexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x.
Variable compSubstRen_exp : forall    (sigmaexp : ( fin  ) -> exp ) (zetaexp : ( fin  ) -> fin ) (thetaexp : ( fin  ) -> exp ) (Eqexp : forall x, (funcomp (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp ), ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s.
Variable up_subst_subst_exp_exp : forall    (sigma : ( fin  ) -> exp ) (tauexp : ( fin  ) -> exp ) (theta : ( fin  ) -> exp ) (Eq : forall x, (funcomp (subst_exp tauexp) sigma) x = theta x), forall x, (funcomp (subst_exp (up_exp_exp tauexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x.
Variable compSubstSubst_exp : forall    (sigmaexp : ( fin  ) -> exp ) (tauexp : ( fin  ) -> exp ) (thetaexp : ( fin  ) -> exp ) (Eqexp : forall x, (funcomp (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp ), subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s.
Variable rinstInst_up_exp_exp : forall   (xi : ( fin  ) -> fin ) (sigma : ( fin  ) -> exp ) (Eq : forall x, (funcomp (var_exp ) xi) x = sigma x), forall x, (funcomp (var_exp ) (upRen_exp_exp xi)) x = (up_exp_exp sigma) x.
Variable rinst_inst_exp : forall   (xiexp : ( fin  ) -> fin ) (sigmaexp : ( fin  ) -> exp ) (Eqexp : forall x, (funcomp (var_exp ) xiexp) x = sigmaexp x) (s : exp ), ren_exp xiexp s = subst_exp sigmaexp s.


Variable retract_ren_exp : forall   (xiexp : ( fin  ) -> fin ) s, ren_exp xiexp (inj s) = ren_exp_lam _ _ upRen_exp_exp ren_exp _ xiexp s.
Variable retract_subst_exp : forall   (sigmaexp : ( fin  ) -> exp ) s, subst_exp sigmaexp (inj s) = subst_exp_lam _ _ up_exp_exp subst_exp _ sigmaexp s.

Variable upRen_exp_exp_def :
   upRen_exp_exp  = up_ren  .

Variable up_exp_exp_def :
  forall sigma x, up_exp_exp sigma  x = scons (var_exp 0) (sigma >> ren_exp S) x.

Variable up_exp_exp_def' :
  forall sigma , up_exp_exp sigma   = scons (var_exp 0) (sigma >> ren_exp S) .

Variable subst_exp_var :
  forall sigma n, subst_exp sigma (var_exp n) = sigma n.

Lemma rinstInst_exp   (xiexp : ( fin  ) -> fin ) : ren_exp xiexp = subst_exp (funcomp (var_exp ) xiexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => rinst_inst_exp xiexp (_) (fun n => eq_refl) x)). Qed.

Lemma instId_exp  : subst_exp (var_exp ) = id .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => idSubst_exp (var_exp ) (fun n => eq_refl) (id x))). Qed.

Lemma rinstId_exp  : @ren_exp   id = id .
Proof. exact (eq_trans (rinstInst_exp id) instId_exp). Qed.


Lemma compComp_exp    (sigmaexp : ( fin  ) -> exp ) (tauexp : ( fin  ) -> exp ) (s : exp ) : subst_exp tauexp (subst_exp sigmaexp s) = subst_exp (funcomp (subst_exp tauexp) sigmaexp) s .
Proof. exact (compSubstSubst_exp sigmaexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp    (sigmaexp : ( fin  ) -> exp ) (tauexp : ( fin  ) -> exp ) : funcomp (subst_exp tauexp) (subst_exp sigmaexp) = subst_exp (funcomp (subst_exp tauexp) sigmaexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compComp_exp sigmaexp tauexp n)). Qed.

Lemma compRen_exp    (sigmaexp : ( fin  ) -> exp ) (zetaexp : ( fin  ) -> fin ) (s : exp ) : ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp (funcomp (ren_exp zetaexp) sigmaexp) s .
Proof. exact (compSubstRen_exp sigmaexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_exp    (sigmaexp : ( fin  ) -> exp ) (zetaexp : ( fin  ) -> fin ) : funcomp (ren_exp zetaexp) (subst_exp sigmaexp) = subst_exp (funcomp (ren_exp zetaexp) sigmaexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compRen_exp sigmaexp zetaexp n)). Qed.

Lemma renComp_exp    (xiexp : ( fin  ) -> fin ) (tauexp : ( fin  ) -> exp ) (s : exp ) : subst_exp tauexp (ren_exp xiexp s) = subst_exp (funcomp tauexp xiexp) s .
Proof. exact (compRenSubst_exp xiexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_exp    (xiexp : ( fin  ) -> fin ) (tauexp : ( fin  ) -> exp ) : funcomp (subst_exp tauexp) (ren_exp xiexp) = subst_exp (funcomp tauexp xiexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renComp_exp xiexp tauexp n)). Qed.

Lemma renRen_exp    (xiexp : ( fin  ) -> fin ) (zetaexp : ( fin  ) -> fin ) (s : exp ) : ren_exp zetaexp (ren_exp xiexp s) = ren_exp (funcomp zetaexp xiexp) s .
Proof. exact (compRenRen_exp xiexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_exp    (xiexp : ( fin  ) -> fin ) (zetaexp : ( fin  ) -> fin ) : funcomp (ren_exp zetaexp) (ren_exp xiexp) = ren_exp (funcomp zetaexp xiexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renRen_exp xiexp zetaexp n)). Qed.

Lemma varL_exp   (sigmaexp : ( fin  ) -> exp ) : funcomp (subst_exp sigmaexp) (var_exp ) = sigmaexp .
Proof. unfold funcomp. apply functional_extensionality. intros. now rewrite subst_exp_var. Qed.

Hint Rewrite rinstId_exp compComp_exp compComp'_exp compRen_exp compRen'_exp renComp_exp renComp'_exp renRen_exp renRen'_exp varL_exp : retract_forward.
Hint Rewrite <- rinstInst_exp : retract_forward.

Hint Rewrite compSubstSubst_exp subst_exp_var using (try reflexivity) : retract_forward.

Hint Rewrite retract_ren_exp retract_subst_exp  up_exp_exp_def up_exp_exp_def': retract_forward.
Hint Rewrite retract_ren_exp retract_subst_exp up_exp_exp_def up_exp_exp_def': retract_rev.

(** *** Preservation *)
Variable has_ty : list ty -> exp -> ty -> Prop.

Inductive has_ty_lam (Gamma : list ty) : exp -> ty -> Prop :=
| hasty_app (A B: ty) s t : has_ty Gamma s (arr_ A B) -> has_ty Gamma t A -> has_ty_lam Gamma (app_ s t) B
| hasty_lam A B s: has_ty (A :: Gamma) s B ->  has_ty_lam Gamma (ab_ A s) (arr_ A B).

Require Import SN.sn_var.

Variable  hasty_var : forall Gamma s A, has_ty_var _ _ Gamma s A -> has_ty Gamma s A.

Variable retract_has_ty : forall Gamma s A, has_ty_lam Gamma s A -> has_ty Gamma s A.
Variable retract_has_ty_rev : forall Gamma s A, has_ty Gamma (inj s) A -> has_ty_lam Gamma (inj s) A.

Instance retract_has_ty_instance Gamma s A:
  Imp (has_ty_lam Gamma s A) (has_ty Gamma s A).
Proof. exact (retract_has_ty Gamma s A). Defined.

Instance retract_has_ty_rev_instance Gamma s A:
  ImpRev (has_ty Gamma (inj s) A) (has_ty_lam Gamma (inj s) A).
Proof. exact (retract_has_ty_rev Gamma s A). Defined.

Variable step: exp -> exp -> Prop.

Inductive step_lam : exp -> exp -> Prop :=
| stepBeta (s: exp) A t: step_lam (app_ (ab_ A s) t) (subst_exp (scons t var_exp) s)
| stepAppL s s' t : step s s' -> step_lam (app_ s t) (app_ s' t)
| stepAppR s t t' : step t t' -> step_lam (app_ s t) (app_ s t')
| stepLam A s s': step s s' -> step_lam (ab_ A s) (ab_ A s').


Lemma stepBeta' s A t t':
  t' = subst_exp (scons t var_exp) s -> step_lam (app_ (ab_ A s) t) t'.
Proof. intros ->. apply stepBeta. Qed.

Variable retract_step: forall e e', step_lam e e' -> step e e'.

Instance retract_step_instance e e':
  Imp (step_lam e e') (step e e').
Proof. exact (retract_step e e'). Defined.

Variable retract_step_rev : forall e e', step (inj e) e' -> step_lam (inj e) e'.

Instance retract_step_rev_instance e e':
  ImpRev  (step (inj e) e') (step_lam (inj e) e').
Proof. exact (retract_step_rev e e'). Defined.

(** # <a id="has_ty_ren_lam" /> #*)
MetaCoq Run Modular Lemma has_ty_ren_lam
  where exp_lam ty exp extends exp with [~ has_ty_lam ~> has_ty ~] : forall Gamma s A,
   has_ty_lam Gamma s A -> forall xi Delta, (forall x, nth_error Gamma x = nth_error Delta (xi x)) -> has_ty Delta (ren_exp xi s) A.
Next Obligation.
  intros IH Gamma s A C. inversion C; subst; intros.
  - unfold app_. mconstructor.
    + eapply has_ty_ren; eauto.
    + eapply has_ty_ren; eauto.
  - unfold ab_. mconstructor.
    eapply has_ty_ren. eassumption.
    intros. msimpl. destruct x as [|]; intros; fsimpl; eauto.
    + cbn. now rewrite H1.
Defined.
(** # <a id="has_ty_subst_lam" /> #*)
MetaCoq Run Modular Lemma has_ty_subst_lam
where exp_lam ty exp extends exp with [~ has_ty_lam ~> has_ty ~] : forall Gamma s A,
   has_ty_lam Gamma s A -> forall sigma Delta, (forall x A, nth_error Gamma x = Datatypes.Some A -> has_ty Delta (sigma x) A) -> has_ty Delta (subst_exp sigma s) A.
Next Obligation.
  intros IH Gamma s A C. inversion C; subst; intros.
  - mconstructor.
    + apply has_ty_subst with (Gamma := Gamma); eauto.
    + eapply has_ty_subst; eauto.
  - mconstructor.
    eapply has_ty_subst; [eassumption|]. intros.
    destruct x as [|]; intros.
    + apply hasty_var. econstructor. eauto.
    + eapply has_ty_ren; eauto.
Defined.
(** # <a id="preservation_lam" /> #*)
MetaCoq Run Modular Lemma preservation_lam
where exp_lam ty exp extends exp with [~ has_ty_lam ~> has_ty ; step_lam ~> step ~] :
 forall Gamma s s' A, has_ty Gamma s A -> step_lam s s' -> has_ty Gamma s' A.
Next Obligation.
  intros IH Gamma s s' A C D. revert Gamma A C.
  induction D; intros; try now (minversion C; mconstructor; eauto).
  - minversion C. minversion H1.
    eapply has_ty_subst; eauto.
    + intros [|]; intros; cbn; eauto.
      * inversion H0; subst. eassumption.
      * eapply hasty_var. econstructor. eauto.
Defined.

(** *** Weak Head Normalisation  *)

Variable L : ty -> exp -> Prop.

MetaCoq Run Modular Fixpoint L_lam where ty_lam ty extends ty :=
 fun (A : ty_lam ty) =>
  match A with
  | arr A1 A2 => fun e => match retract_R e with
                      | Datatypes.Some (ab B s) => forall xi v, L A1 v -> E_ _ _ step L A2 (subst_exp (scons v (xi >> var_exp)) s)
                      | _ => False
                      end
  end.

Variable retract_L  : forall A e,  L_lam A e = L (inj A) e.
Hint Rewrite <- retract_L: retract_rev.
Hint Rewrite <- retract_L : retract_forward.

Lemma star_appL s s' t :
  star step s s' -> star step (app_ s t) (app_ s' t).
Proof.
  induction 1; eauto.
  - econstructor; try apply IHstar. msimpl. now mconstructor.
Qed.

Lemma star_appR s t t' :
  star step t t' -> star step (app_ s t) (app_ s t').
Proof.
  induction 1; eauto.
  - econstructor; try apply IHstar. msimpl. now mconstructor.
Qed.
(** # <a id="whnf_lam" /> #*)
MetaCoq Run Modular Fixpoint whnf_lam where exp_lam ty exp extends exp :=
 fun (e : exp_lam ty exp) =>
  match e with
  | ab a b => True
  | _ => False
  end.

Variable retract_whnf_lam : forall e, whnf (inj e) = whnf_lam e.
Hint Rewrite retract_whnf_lam : retract_rev.
Hint Rewrite retract_whnf_lam : retract_forward.

Lemma L_val_lam (A : ty_lam ty)  (s : exp) :
  L_lam A s -> whnf s.
Proof.
  destruct A; cbn; eauto; msimpl.
  destruct (retr s) eqn:HH; try contradiction.
  minversion HH.
  msimpl.
  destruct e; intros; cbn; eauto.
Qed.
(** # <a id="L_ren_lam" /> #*)
MetaCoq Run Modular Lemma L_ren_lam where ty_lam ty extends ty with [~ L_lam ~> L ~] :
forall s A xi,
  L_lam A s -> L (inj A) (ren_exp xi s).
Next Obligation.
  intros IH s A xi. revert s xi. induction A; eauto.
  - intros. cbn in H0. cbn.
    destruct (retr s) eqn: s'; try contradiction.
    minversion s'. subst. 
    destruct e; try contradiction.
    msimpl.
    intros zeta v H''. specialize (H0 (xi >> zeta) _ H'').
    destruct H0 as (?&?&?).
    exists x. split; eauto. msimpl. now fsimpl.
Defined. 
(** # <a id="wn_fundamental_lam" /> #*)
MetaCoq Run Modular Lemma wn_fundamental_lam
where exp_lam ty exp extends exp with [~ has_ty_lam ~> has_ty ~] : forall Gamma s A,
  has_ty_lam Gamma s A -> has_ty_sem _ _ subst_exp step L Gamma s A.
Next Obligation.
  intros IH Gamma s A C. intros sigma D. unfold E_. inversion C; subst; msimpl.
  - destruct (IH _ _ _ H0 sigma D) as (v1&?&?).
    destruct (IH _ _ _ H1 sigma D) as (v2&?&?).
    msimpl_in H3.
    destruct (retr v1) eqn:HH; try contradiction.
    minversion HH. clear H6. subst.
    destruct e; try now (inversion H3).
    edestruct  (H3 id _ H5) as (v'&?&?).
    exists v'; split; eauto.
    enough (star step (app_ (inj (ab _ _ t0 e)) v2) v').
    { eapply star_trans.
      apply (star_appL _ _ _ H2). eapply star_trans.
      apply (star_appR _ _ _ H4).  eassumption. }
    econstructor; [|eapply H6]. mconstructor.
  - apply val_inclusion. msimpl.
    intros.
    specialize (IH _ _ _ H0).
    unfold has_ty_sem in IH.
    assert (G _ _ L (A0 ::Gamma) (v .: (sigma >> ren_exp xi))). 
    { unfold G. intros [|] ? ?.
      - cbn in H2. inversion H2; subst. cbn. eassumption.
      - cbn in *. specialize (D _ _ H2).
        now apply L_ren.  }
    destruct (IH _ H2) as (v'&?&?).
    exists v'; split; eauto.
    msimpl. fsimpl. now msimpl.
Defined.

(** *** Strong Normalisation *)

Variable L_strong: ty -> exp -> Prop.

(** # <a id="step_inst_lam" /> #*)
MetaCoq Run Modular Lemma step_inst_lam
where exp_lam ty exp extends exp with [~ step_lam ~> step ~] : forall s s' sigma,
  step_lam s s' -> step (subst_exp sigma s) (subst_exp sigma s').
Next Obligation.
  intros IH s s' sigma. destruct 1; msimpl; eauto.
  all: try mconstructor; eauto.
  - apply imp. apply stepBeta'.  
    msimpl. fsimpl. msimpl. now fsimpl.
Defined.

Variable whnf_anti_renaming : forall s xi,  whnf (ren_exp xi s) -> whnf s.

Lemma whnf_anti_renaming_lam s xi :
  whnf (ren_exp_lam _ _ up_ren ren_exp _ xi s) -> whnf (inj s).
Proof.
  destruct s; msimpl; eauto.
Qed.

Variable ren_preserves : forall xi s t, ren_exp xi s = inj t -> exists s', s = inj s'.

Lemma ren_preserves_ab : forall s xi T t, ren_exp xi s = ab_ T t -> exists t', s = ab_ T t' 
                                                                     /\ ren_exp (upRen_exp_exp xi) t' = t.
Proof.
  clear - retract_whnf_lam retract_L retract_ren_exp up_exp_exp_def' up_exp_exp_def retract_subst_exp ren_preserves.
  intros. destruct (ren_preserves _ _ _ H0) as (? & ?). subst.

  rewrite retract_ren_exp in H0.
  destruct x; minversion H0.
  exists e. split. reflexivity. reflexivity.                             
Defined.

Lemma ren_preserves_app : forall s xi t1 t2, ren_exp xi s = app_ t1 t2 -> exists t1' t2', s = app_ t1' t2'
                                                                             /\ ren_exp xi t1' = t1
                                                                             /\ ren_exp xi t2' = t2.
Proof.
  intros. destruct (ren_preserves _ _ _ H0) as (? & ?). subst.

  rewrite retract_ren_exp in H0.
  destruct x; minversion H0.
  exists e, e0. split; eauto.
Qed.

Variable ren_var:
  forall (xi : fin -> fin) (n : fin), var_exp (xi n) = ren_exp xi (var_exp n).

(** # <a id="step_anti_renaming_lam" /> #*)
MetaCoq Run Modular Lemma step_anti_renaming_lam where exp_lam ty exp extends exp with [~ step_lam ~> step ~] : forall  s' xi t, step_lam (ren_exp xi s') t -> exists t', t = ren_exp xi t' /\ step s' t'.
Next Obligation.
  intros IH s' xi t. inversion 1; eauto; msimpl.
  - symmetry in H2. eapply ren_preserves_app in H2 as (? & ? & ? & ? & ?). subst t0 s'.
    eapply ren_preserves_ab in H3 as (? & ? & ?). subst.
    asimpl in H0.
    exists (subst_exp (x0, var_exp) x1).
    msimpl. fsimpl. split.
    eapply ext_exp. intros []; cbv; try reflexivity. eapply ren_var.      
    mconstructor.
  - subst t. symmetry in H1. eapply ren_preserves_app in H1 as (? & ? & ? & ? & ?). subst.
    eapply IH in H2 as (? & ? & ?). subst.
    exists (app_ x1 x0). msimpl. split; eauto.
    mconstructor. eauto.
  - subst t. symmetry in H1. eapply ren_preserves_app in H1 as (? & ? & ? & ? & ?). subst.
    eapply IH in H2 as (? & ? & ?). subst.
    exists (app_ x x1). msimpl. split; eauto.
    mconstructor. eauto.
  - subst t. symmetry in H1. eapply ren_preserves_ab in H1 as (? & ? & ?). subst.
    eapply IH in H2 as (? & ? & ?). subst.
    exists (ab_ A x0). msimpl. split; eauto.
    mconstructor. eauto.
Defined.
  
Lemma close_ren  :
  (forall (xi : nat -> nat) s A, L_strong A s -> L_strong A (ren_exp xi s)) ->
  (forall xi s A, E_strong _ _ step whnf L_strong A s -> E_strong _ _ step whnf L_strong A (ren_exp xi s)).
Proof.
  intros. induction H1.
  constructor.
  - intros. apply H0, H1. eapply whnf_anti_renaming; eauto.
  - intros. apply step_anti_renaming in H4 as (t'&?&?). subst.
    apply H3; eauto.
Qed.

Fixpoint L_strong_lam (A : ty_lam ty): exp -> Prop :=
  match A with
  | arr A1 A2 => fun e => match retract_R e with
                      | Datatypes.Some (ab B s) => forall xi v, E_strong' _ step whnf (L_strong A1) v -> E_strong' _ step whnf (L_strong A2) (subst_exp (v .: (xi >> var_exp)) s)
                      | _ => False
                      end
  end.

Variable retract_L_strong  : forall A e,  L_strong_lam A (inj e) = L_strong (inj A) (inj e).
Hint Rewrite <- retract_L_strong : retract_forward.
Hint Rewrite <- retract_L_strong : retract_backward.

(** # <a id="L_close_ren_lam" /> #*)
MetaCoq Run Modular Lemma L_close_ren_lam 
where ty_lam ty extends ty with [~ L_strong_lam ~> L_strong ~] : 
forall xi s A, L_strong_lam A s -> L_strong (inj A) (ren_exp xi s).
Next Obligation.
  intros IH xi s A. induction A; eauto. msimpl.
  destruct (retr s) eqn:HH; try contradiction.
  apply retract_tight in HH. subst.
  destruct e; try contradiction.
  intros. msimpl. intros. msimpl.
  fsimpl. eauto.
Defined.

Variable E_strong_var : forall x A, E_strong _ _ step whnf L_strong A (var_exp x).

(** # <a id="sn_fundamental_lam" /> #*)
MetaCoq Run Modular Lemma sn_fundamental_lam
where ty_lam ty extends ty with [~ has_ty_lam ~> has_ty ~] : 
forall Gamma s A, has_ty_lam Gamma s A -> has_ty_sem_strong _ _ subst_exp step whnf L_strong Gamma s A.
Next Obligation.
  intros IH Gamma s A. intros C. destruct C.
  -  intros sigma D.
    assert (IH1 := IH _ _ _ H0 _ D).
    assert (IH2 := IH _ _ _ H1 _ D).
    msimpl.
    remember (subst_exp sigma s) as s'. remember (subst_exp sigma t) as t'.
    clear s t Heqs' Heqt' H0 H1.
    apply E_strong_sn in IH1 as IH1'. apply E_strong_sn in IH2 as IH2'.
    revert t' IH2 IH2'. induction IH1' as [s].
    intros t' IH2 IH2'. induction IH2' as [t].
    constructor.
    + msimpl. contradiction.
    + intros ? HH. minversion HH; eauto using E_strong_step.
      * msimpl_in IH1.
      apply E_strong_base in IH1.
       -- msimpl_in IH1. unfold ab_ in IH1. rewrite <- retract_L_strong in IH1.
        cbn in IH1.
        rewrite retract_works in IH1. (* TODO *)
        specialize (IH1 id t). eapply IH1.
        assumption.
       --  now msimpl.
     * apply H1; eauto. eapply E_strong_step; eauto.
     * apply H3; eauto. eapply E_strong_step; eauto.
  - intros sigma ctx. cbn.
    assert (sn step (subst_exp (up_exp_exp sigma) s)).
    { eapply E_strong_sn.
      specialize (IH _ _ _ H0). unfold has_ty_sem_strong in IH. apply IH.
      intros [|]; intros; msimpl.
      - cbn in H1. inversion H1. apply E_strong_var.
      - apply close_ren. apply L_close_ren. eauto.  }
    msimpl. rewrite <- up_exp_exp_def'.
    remember (subst_exp (up_exp_exp sigma) s) as s'.
    specialize (IH _ _ _ H0). unfold has_ty_sem_strong in IH.
    assert (forall tau, G_strong _ _ step whnf L_strong (A :: Gamma) (up_exp_exp sigma >> subst_exp tau) -> E_strong _ _ step whnf L_strong B (subst_exp tau s')).
    { intros. rewrite Heqs'. revert H2. msimpl. fsimpl. msimpl.   eauto.  }
    clear Heqs'.
    induction H1. constructor.
    + intros. clear H3. msimpl.
      intros.  apply H2.
      intros [|]; intros; msimpl; eauto.
      * fsimpl. msimpl. inversion H5. subst. eauto.
      * fsimpl. msimpl.
        eapply close_ren. apply L_close_ren. cbn in H5. eauto.
    + intros. minversion H4.
      apply H3; eauto.
      intros. specialize (H2 _ H5). eapply E_strong_step; eauto.
Defined.


End MiniML_Lambda.
