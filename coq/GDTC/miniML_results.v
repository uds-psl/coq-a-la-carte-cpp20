From GDTC Require Import miniML.

(** ** Composed results for mini-ML  *)

Fixpoint eval n (s : exp) env : option value :=
  match s with
  | exp_lam_C s => eval_fix eval n (inj s) env
  | exp_bool_C s => eval_bool eval n (inj s) env
  | exp_arith_C s => eval_arith eval n (inj s) env
  | exp_case_C s => eval_case eval n (inj s) env
  | exp_fix_C s => eval_fix eval n (inj s) env
  end.

Lemma eval1 n s env : eval n (exp_lam_C s) env = eval_fix eval n (inj s) env.
Proof.
  now destruct n.
Qed.

Lemma eval2 n s env : eval n (exp_bool_C s) env = eval_bool eval n (inj s) env.
Proof.
  now destruct n.
Qed.

Lemma eval3 n s env : eval n (exp_arith_C s) env = eval_arith eval n (inj s) env.
Proof.
  now destruct n.
Qed.

Lemma eval4 n s env : eval n (exp_case_C s) env = eval_case eval n (inj s) env.
Proof.
  now destruct n.
Qed.

Lemma eval5 n s env : eval n (exp_fix_C s) env = eval_fix eval n (inj s) env.
Proof.
  now destruct n.
Qed.

Lemma monotone n s t env : eval n s env = Some t -> forall m, m >= n -> eval m s env = Some t.
Proof.
  induction n in s, env, t |- * using size_ind.
  destruct s.
  - setoid_rewrite eval1.
    eapply monotone_fix. intros; eauto.
  - setoid_rewrite eval2.
    eapply monotone_bool. intros. eauto.
  - setoid_rewrite eval3.
    eapply monotone_arith. intros; eauto.
  - setoid_rewrite eval4.
    eapply monotone_case. intros; eauto.
  - setoid_rewrite eval5.
    eapply monotone_fix. intros; eauto.
Qed.

Fixpoint beq (s t : ty) : bool :=
  match s with
  | ty_lam_C s => beq_ty_lam beq s t
  | ty_bool_C s => beq_ty_bool s t
  | ty_arith_C s => beq_ty_arith s t
  end.

Lemma ty_induction : forall P : ty -> Prop,
       (forall e : ty_lam ty, (forall x, In_ty_lam x e -> P x) -> P (ty_lam_C e)) ->
       (forall e : ty_bool, (forall x, In_ty_bool x e -> P x) -> P (ty_bool_C e)) ->
       (forall e : ty_arith, (forall x, In_ty_arith x e -> P x) -> P (ty_arith_C e)) -> forall e,P e.
Proof.
  fix ty_induction 5. intros. destruct e.
  - eapply H. intros.
    destruct t. cbn in H2. destruct H2; subst.
    + eapply ty_induction. eauto. eauto. eauto.
    + eapply ty_induction. eauto. eauto. eauto.
  - eapply H0. intros.
    destruct t. cbn in H2. destruct H2; subst.
  - eapply H1. intros.
    destruct t. cbn in H2. destruct H2; subst.
Qed.

Lemma beq_correct (s t : ty) :
  beq s t = true <-> s = t.
Proof.
  induction s in t |- * using ty_induction.
  - eapply beq_ty_correct_lam; eauto. 
  - eapply beq_ty_bool_correct; eauto. 
  - eapply beq_ty_arith_correct; eauto.
Qed.

Fixpoint typeof (Gamma : nat -> ty) (s : exp) : option ty :=
  match s with
  | exp_lam_C s => typeof_lam beq typeof Gamma s
  | exp_bool_C s => typeof_bool beq typeof Gamma s
  | exp_arith_C s => typeof_arith typeof Gamma s
  | exp_case_C s => typeof_case beq typeof Gamma s
  | exp_fix_C s => typeof_fix beq typeof Gamma s
  end.

Inductive vtypeis : value -> ty -> Prop :=
| vtypeis_Lam s t   : vtypeis_lam  typeof vtypeis s t -> vtypeis (inj s) t
| vtypeis_Bool s t  : vtypeis_bool s t -> vtypeis (inj s) t
| vtypeis_Arith s t : vtypeis_arith s t -> vtypeis (inj s) t
| vtypeis_Fix s t : vtypeis_fix typeof vtypeis s t -> vtypeis (inj s) t.

Lemma typeof_sound
      (Gamma : nat -> ty) n
      (s : exp) env ty v :
  (forall n, vtypeis (env n) (Gamma n)) ->
  typeof Gamma s = Some ty ->
  eval n s env = Some v ->
  vtypeis v ty.
Proof.
  intros.
  induction n in s, Gamma, env, ty, v, H, H0, H1 |- * using size_ind.
  destruct s.
  -rewrite eval1 in H1. eapply typeof_sound_lam; cbn; eauto.
    eapply beq_correct. firstorder. firstorder.
    + firstorder. inv H3. eauto. econstructor. eauto.
    + firstorder. inv H3. eauto. econstructor. eauto.
  - rewrite eval2 in H1. eapply typeof_bool_sound; cbn; eauto. exact beq_correct.
    firstorder.
    + inversion H3; subst; eauto.
    + econstructor. eauto.
  - rewrite eval3 in H1. eapply typeof_arith_sound; cbn; eauto.
    firstorder.
    + inversion H3; subst; eauto.
    + econstructor. eauto.
  - rewrite eval4 in H1. eapply typeof_case_sound; cbn; eauto. exact beq_correct.
    firstorder.
    + inversion H3; subst; eauto.
    + econstructor. eauto.
  - rewrite eval5 in H1. eapply typeof_sound_lam; cbn; eauto. exact beq_correct.
    firstorder. firstorder.
    + firstorder. inv H3. eauto. econstructor. eauto.
    + firstorder. inv H3. eauto. econstructor. eauto.
Qed.
