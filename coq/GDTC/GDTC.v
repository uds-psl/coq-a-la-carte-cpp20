Require Import header_metacoq tactics GDTC.features.
Set Implicit Arguments.

(** ** mini-ML: lambda expression  *)

Section MiniML_Lambda.

Variable T E V : Type.
Context `{retract (ty_lam T) T}.
Context `{retract (exp_lam T E) E}.
Context {HR : retract (value_lam E V)  V}.

MetaCoq Run Modular
 Fixpoint eval_lam where exp_lam T E extends E with eval :=
  fun (n : nat) (s : E) (env : nat -> V) =>
  match n with
    0 => None
  | S n =>
    match retr s with
    | Some (var v) => ret (env v)
    | Some (app s t) => mlet v <- eval n s env ;;
                mlet v' <- eval n t env ;;
                mlet (Clos s e) <- retract_R v ;;
                eval n s (v' .: e)
    | Some (lam ty s) => ret (inj (Clos s env))
    | None => None
    end
  end.

MetaCoq Run
 Modular Lemma monotone_lam where exp_lam T E extends E at 1 with [~ eval_lam ~> eval ~] :
  forall n s env, forall t, eval_lam n s env = Some t -> forall m, m >= n -> eval_lam m s env = Some t.
Next Obligation.
  intros n IH s env t. intros. destruct n; cbn  in *.
  - inversion H1.
  - destruct m; try omega. cbn.
    destruct (retr s) eqn:E0; try congruence.
    destruct e.
    + inversion H1. reflexivity.
    + destruct (eval n e env) eqn:E1.
      destruct (eval n e0 env) eqn:E2.
      all: try now cbn in *; congruence.
      assert (m >= n) by omega.
      eapply IH in E1 as ->; hnf; eauto.
      eapply IH in E2 as ->; hnf; eauto. cbn in *.
      destruct (retr v) eqn:E3. cbn in *. destruct v1.
      all: eauto.
    + eassumption.
Qed.

Variable beq : T -> T -> bool.

Definition beq_ty_lam (t1 : ty_lam T) (t2 : T) : bool :=
  match t1, retr t2 with
  | Arr t11 t12, Some (Arr t21 t22) => beq t11 t21 && beq t12 t22
  | _ , _ => false
  end.

MetaCoq Run
 Modular Lemma beq_ty_correct_lam where ty_lam T extends T at 1 with [~ beq_ty_lam ~> beq ~] :
  forall t1 t2, beq_ty_lam t1 t2 = true <-> inj t1 = t2.
Next Obligation.
  intros t1 IH t2.
  destruct t1.
  assert (IH1 := IH t).
  assert (IH2 := IH t0). clear IH.
  cbn. destruct (retr t2) eqn:E1.
  - destruct t1.
    rewrite Bool.andb_true_iff.
    setoid_rewrite IH1.
    setoid_rewrite IH2. all:cbn; eauto.
    split.
    + intros [-> ->]. now msimpl_in E1.
    + intros; subst. now minversion E1. 
  - intuition. subst. minversion E1.
Qed.
Hypothesis beq_correct : forall t1 t2, beq t1 t2 = true <-> t1 = t2. 

Variable typeof : (nat -> T) -> E -> option T.

Definition typeof_lam
           (Gamma : nat -> T) (s : exp_lam T E) : option T :=
  match s with
  | var x => ret (Gamma x)
  | app s t => match (typeof Gamma s, typeof Gamma t) with
              | (Some A, Some C) =>
                match retract_R A
                with Some (Arr T1 T2) => if beq T1 C then Some T2 else None
                | _ => None
                end
              | _ => None
                end
  | lam tp s => match typeof (tp .: Gamma) s with Some tp' => ret (inj (Arr tp tp')) | None => None end
  end.

Variable vtypeis : V -> T -> Prop.

Inductive vtypeis_lam : value_lam E V -> T -> Prop :=
| wf_value_C s typ env rett Γ :
    (forall x, vtypeis (env x) (Γ x)) ->
    typeof (typ .: Γ) s = Some rett ->
    vtypeis_lam (Clos s env) (inj (Arr typ rett)).
Hypothesis vtypeis_inj : forall s t, vtypeis (inj s) t <-> vtypeis_lam s t.

Instance vtypeis_inj_imp s t : Imp (vtypeis_lam s t)  (vtypeis (inj s) t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.

Instance vtypeis_inj_imprev s t : ImpRev (vtypeis (inj s) t) (vtypeis_lam s t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.

MetaCoq Run
Modular Lemma typeof_lam_sound where exp_lam T E extends E at 1 with [~ typeof_lam ~> typeof ; eval_lam ~> eval ~] :
  forall n s Gamma env ty v,
            (forall n, vtypeis (env n) (Gamma n)) ->
            typeof_lam Gamma s = Some ty ->
            eval_lam n (inj s) env = Some v ->
            vtypeis v ty.
Next Obligation.
  intros n IH s Gamma env ty v.
  unfold subterm_rel, nat_subterm' in *.
  intros H_env.
  destruct n; cbn; intros.
  - congruence.
  - msimpl_in H2. destruct s.
    + cbn in *. destruct (typeof _ e) eqn:E1; try congruence. inv H2. inv H1.
      mconstructor; eauto.
    + cbn in *.
      destruct (eval n e env) eqn:E2; cbn in *; try congruence.
      destruct (eval n e0 env) eqn:E3; cbn in *; try congruence.
      destruct (retr v0) eqn:E4; cbn in *; try congruence.
      destruct v2.
      msimpl_in E4. subst.
      destruct (typeof Gamma e) eqn:E4; try congruence.
      destruct (typeof Gamma e0) eqn:E5; try congruence.
      destruct (retr t) eqn:E6; try congruence.
      destruct t1; try congruence.
      destruct (beq t1 t0) eqn:E7; try congruence.
      msimpl_in E6. subst.
      eapply beq_correct in E7. subst. inv H2.
      assert (E2' := E2). assert (E3' := E3).
      eapply IH in E2; eauto.
      eapply IH in E3; eauto.
      minversion E2. inv E2.
      minversion H5.  inv H1.
      eapply IH in H7; eauto.

      intros ?. cbn. destruct n0; eauto.
    + cbn in *. inv H2. inv H1. eauto.
Qed.

End MiniML_Lambda.

(** ** mini-ML: boolean expressions  *)

Section MiniML_Bool.

Variable T : Type.
Context `{retract ty_bool T}.
  
Variable E : Type.
Context `{retract (exp_bool E) E}.

Variable V : Type.
Context `{retract value_bool V}.

Variable eval : nat -> E -> (nat -> V)  -> option V.

Definition eval_bool (n : nat) (s : E) (env : nat -> V) : option V :=
  match n with
    0 => None
  | S n =>
    mlet s <- retr s ;;
    match s with
    | constBool b => ret (inj (Boolean b))
    | If s t u => mlet v <- eval n s env ;;
                 mlet (Boolean b) <- retract_R v ;;
                 if b
                 then
                   eval n t env
                 else
                   eval n u env
    end
  end.

MetaCoq Run
Modular Lemma monotone_bool where exp_bool E extends E at 1 with [~ eval_bool ~> eval ~] :
  (forall (n : nat) (s : E) (env : nat -> V) t,
    eval_bool n s env = Some t -> forall m, m >= n -> eval_bool m s env = Some t).
Next Obligation.
  intros n IH **.
  intros. destruct n; cbn  in *.
  - inversion H2.
  - destruct m; try omega. cbn.
    destruct (retr s) eqn:E0.
    destruct e; cbn in *.
    + inversion H2. reflexivity.
    + destruct (eval n e env) eqn:E1; cbn in *; try congruence.
      eapply IH in E1 as ->; eauto with arith. cbn in *.
      destruct (retr v); cbn in *; try congruence.
      destruct v0; try congruence.
      destruct b.
      * eapply IH in H2; eauto with arith.
      * eapply IH in H2; eauto with arith.
    + eauto.
Qed.

Definition beq_ty_bool (t1 : ty_bool) (t2 : T) : bool :=
  match t1, retr t2 with
  | Bool, Some (Bool) => true
  | _ , _ => false
  end.

Variable beq : T -> T -> bool.

Instance subt_bool : InRelC _ := (@subterm_ty_bool T).

MetaCoq Run
Modular Lemma beq_ty_bool_correct where ty_bool extends T at 1 with [~ beq_ty_bool ~> beq ~] : forall (t1 : ty_bool) (t2 : T),
  beq_ty_bool t1 t2 = true <-> inj t1 = t2.
Next Obligation.
  intros t1 IH t2.
  destruct t1.
  cbn. destruct (retr t2) eqn:E1.
  - destruct t. minversion E1. firstorder.
  - split. firstorder congruence. intros; subst. minversion E1. 
Defined.

Hypothesis beq_correct : forall t1 t2, beq t1 t2 = true <-> t1 = t2.

Variable (typeof : (nat -> T) -> E -> option T).

Definition typeof_bool
           (Gamma : nat -> T) (s : exp_bool E) : option T :=
  match s with
  | constBool b => ret (inj (Bool))
  | If s t u => mlet ts <- typeof Gamma s ;;
               mlet Bool <- retr ts ;;
               mlet ty_t <- typeof Gamma t ;;
               mlet tu <- typeof Gamma u ;;
               if beq ty_t tu then ret ty_t else None
  end.

Variable vtypeis : V -> T -> Prop.

Inductive vtypeis_bool : value_bool -> T -> Prop :=
| vtypeis_bool_C b :
    vtypeis_bool (Boolean b) (inj Bool).

Hypothesis vtypeis_inj : forall s t, vtypeis (inj s) t <-> vtypeis_bool s t.

Instance vtypeis_inj_imp_bool s t : Imp (vtypeis_bool s t)  (vtypeis (inj s) t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.

Instance vtypeis_inj_imprev_bool s t : ImpRev (vtypeis (inj s) t) (vtypeis_bool s t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.

MetaCoq Run
Modular Lemma typeof_bool_sound where exp_bool E extends E at 1 with [~ typeof_bool ~> typeof ; eval_bool ~> eval ~] :
 forall n s Gamma env ty v,
  (forall n, vtypeis (env n) (Gamma n)) ->
  typeof_bool Gamma s = Some ty ->
  eval_bool n (inj s) env = Some v ->
  vtypeis v ty.
Next Obligation.
  intros n IH **. destruct n; cbn in H4; inversion H4; clear H4.
  msimpl_in H6.
  destruct s.
  - minversion H6. inv H3. mconstructor.
  - cbn in *.
    destruct (eval n e env) eqn:E1; cbn in *; try congruence.
    destruct (retr v0) eqn:E2; cbn in *; try congruence.
    destruct v1 eqn:E3; cbn in *; try congruence.
    cbn in H3.
    destruct (typeof Gamma e) eqn:E4; cbn in *; try congruence.
    destruct (retr t) eqn:E5; cbn in *; try congruence.
    destruct t0.
    destruct (typeof Gamma e0) eqn:E6; cbn in *; try congruence.
    destruct (typeof Gamma e1) eqn:E7; cbn in *; try congruence.
    destruct (beq t0 t1) eqn:E8; cbn in *; try congruence.
    minversion E2. minversion H3. minversion E5.
    destruct b.
    + eapply IH in H6; eauto.
    + eapply IH in H6; eauto.
      eapply beq_correct in E8. now subst.
Qed.

End MiniML_Bool.

(** ** mini-ML: arithmetic expressions  *)

Section MiniML_Arith.

Variable E : Type.
Context `{retract (exp_arith E) E}.

Variable V : Type.
Context `{retract value_arith V}.

Variable T : Type.
Context `{retract ty_arith T}.

Variable eval : nat -> E -> (nat -> V)  -> option V.

Definition eval_arith (n : nat) (s : E) (env : nat -> V) : option V :=
  match n with
    0 => None
  | S n =>
    mlet s <- retr s ;;
    match s with
    | Num n => ret (inj (Number n))
    | Plus s t => mlet v1 <- eval n s env ;;
                 mlet v2 <- eval n t env ;;
                 mlet (Number n1) <- retract_R v1 ;;
                 mlet (Number n2) <- retract_R v2 ;;
                 ret (inj (Number (n1 + n1)))
    end
  end.

MetaCoq Run
Modular Lemma monotone_arith where exp_arith E extends E at 1 with [~ eval_arith ~> eval ~] :
  forall (n : nat) (s : E) (env : nat -> V) t,
    eval_arith n s env = Some t -> forall m, m >= n -> eval_arith m s env = Some t.
Next Obligation.
  intros n IH **.
  destruct n; cbn in *.
  - congruence.
  - destruct m; try omega; cbn.
    destruct (retr s) eqn:E1; cbn in *; try congruence.
    destruct e eqn:E2; cbn in *.
    + congruence.
    + destruct (eval n e0 env) eqn:E3; cbn in *; try congruence.
      destruct (eval n e1 env) eqn:E4; cbn in *; try congruence.
      assert (m >= n) by omega.
      eapply IH in E3 as ->; eauto.
      eapply IH in E4 as ->; eauto.
Qed.

Definition beq_ty_arith (t1 : ty_arith) (t2 : T) : bool :=
  match t1, retr t2 with
  | Nat, Some (Nat) => true
  | _ , _ => false
  end.

Variable beq : T -> T -> bool.

Instance subt_arith : InRelC _ := (@subterm_ty_arith T).
MetaCoq Run
Modular Lemma beq_ty_arith_correct where ty_arith extends T at 1 with [~ beq_ty_arith ~> beq ~] : forall (t1 : ty_arith) (t2 : T),
  beq_ty_arith t1 t2 = true <-> inj t1 = t2.
Next Obligation.
  intros t1 IH t2.
  destruct t1.
  cbn. destruct (retr t2) eqn:E1.
  - destruct t. minversion E1. firstorder.
  - split. firstorder congruence.  intros <-. minversion E1.
Defined.

Hypothesis beq_correct : forall t1 t2, beq t1 t2 = true <-> t1 = t2.

Variable (typeof : (nat -> T) -> E -> option T).

Definition typeof_arith
           (Gamma : nat -> T) (s : exp_arith E) : option T :=
  match s with
  | Num n => ret (inj (Nat))
  | Plus s t  => mlet ts <- typeof Gamma s ;;
                mlet Nat <- retr ts;;
                mlet t_t <- typeof Gamma t ;;
                mlet Nat <- retr t_t ;;
                ret (inj Nat)
  end.

Variable vtypeis : V -> T -> Prop.

Inductive vtypeis_arith : value_arith -> T -> Prop :=
| vtypeis_arith_C n :
    vtypeis_arith (Number n) (inj Nat).

Hypothesis vtypeis_inj : forall s t, vtypeis (inj s) t <-> vtypeis_arith s t.


Instance vtypeis_inj_imp_arith s t : Imp (vtypeis_arith s t)  (vtypeis (inj s) t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.

Instance vtypeis_inj_imprev_arith s t : ImpRev (vtypeis (inj s) t) (vtypeis_arith s t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.


MetaCoq Run
Modular Lemma typeof_arith_sound where exp_arith E extends E at 1 with [~ typeof_arith ~> typeof ; eval_arith ~> eval ~] :
 forall n s Gamma env ty v,
  (forall n, vtypeis (env n) (Gamma n)) ->
  typeof_arith Gamma s = Some ty ->
  eval_arith n (inj s) env = Some v ->
  vtypeis v ty.
Next Obligation.
  intros n IH **. destruct n; cbn in H4; inversion H4; clear H4.
  msimpl_in H6.
  destruct s.
  - minversion H6. inv H3. mconstructor.
  - cbn in *.
    destruct (eval n e env) eqn:E1; cbn in *; try congruence.
    destruct (eval n e0 env) eqn:E2; cbn in *; try congruence.
    destruct (retr v0) eqn:E3; cbn in *; try congruence.
    destruct (retr v1) eqn:E4; cbn in *; try congruence.
    all:destruct v2 eqn:E5; cbn in *; try congruence.
    destruct v3 eqn:E6; cbn in *; try congruence.
    minversion H6.

    destruct (typeof Gamma e) eqn:E7; cbn in *; try congruence.
    destruct (retr t) eqn:E8; cbn in *; try congruence.
    destruct (typeof Gamma e0) eqn:E9; cbn in *; try congruence.
    destruct (retr t1) eqn:E10; cbn in *; try congruence.
    all: destruct t0; try destruct t2; try congruence. inv H3.
    mconstructor.
Qed.

End MiniML_Arith.

(** ** mini-ML: natCase expressions  *)

Section MiniML_Case.

Variable E : Type.
Context `{True}.
Context `{retract (exp_case E) E}.

Variable T : Type.
Context { HR : retract ty_arith T}.

Variable V : Type.
Context `{retract value_arith V}.

Variable eval : nat -> E -> (nat -> V)  -> option V.

Definition eval_case (n : nat) (s : E) (env : nat -> V) : option V :=
  match n with
    0 => None
  | S n =>
    mlet s <- retr s ;;
    match s with
    | Case s t u => mlet v1 <- eval n s env ;;
                   mlet (Number n1) <- retr v1 ;;
                   match n1 with
                   | 0 => eval n t env
                   | S n' => eval n u (inj (Number n') .: env)
                   end
    end
  end.

MetaCoq Run
Modular Lemma monotone_case where exp_case E extends E at 1 with [~ eval_case ~> eval ~] :
  forall (n : nat) (s : E) (env : nat -> V) t,
    eval_case n s env = Some t -> forall m, m >= n -> eval_case m s env = Some t.
Next Obligation.
  intros n IH **.
  destruct n; cbn in *.
  - congruence.
  - destruct m; try omega; cbn.
    destruct (retr s) eqn:E1; cbn in *; try congruence.
    destruct e eqn:E2; cbn in *.
    destruct (eval n e0 env) eqn:E3; cbn in *; try congruence.
    destruct (retr v) eqn:E4; cbn in *; try congruence.
    destruct v0, n0.
    + eapply IH in E3 as ->; eauto with arith.
      cbn. rewrite E4. cbn.
      eapply IH in H2 as ->; eauto with arith.
    + eapply IH in E3 as ->; eauto with arith.
      cbn. rewrite E4. cbn.
      eapply IH in H2 as ->; eauto with arith.
Qed.

Variable beq : T -> T -> bool.

Hypothesis beq_correct : forall t1 t2, beq t1 t2 = true <-> t1 = t2.

Variable (typeof : (nat -> T) -> E -> option T).

Definition typeof_case
           (Gamma : nat -> T) (s : exp_case E) : option T :=
  match s with
  | Case s t u  => mlet ts <- typeof Gamma s ;;
                  mlet Nat <- retr ts;;
                  mlet t_t <- typeof Gamma t ;;
                  mlet t_u <- typeof (inj Nat .: Gamma) u ;;
                  if beq t_t t_u then ret t_t else None
  end.

Variable vtypeis : V -> T -> Prop.

Hypothesis vtypeis_inj : forall s t, vtypeis (inj s) t <-> vtypeis_arith s t.

Instance vtypeis_inj_imp_arith' s t : Imp (vtypeis_arith s t)  (vtypeis (inj s) t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.

Instance vtypeis_inj_imprev_arith' s t : ImpRev (vtypeis (inj s) t) (vtypeis_arith s t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.

MetaCoq Run
Modular Lemma typeof_case_sound where exp_case E extends E at 1 with [~ typeof_case ~> typeof ; eval_case ~> eval ~] :
 forall n s Gamma env ty v,
  (forall n, vtypeis (env n) (Gamma n)) ->
  typeof_case Gamma s = Some ty ->
  eval_case n (inj s) env = Some v ->
  vtypeis v ty.
Next Obligation.
  intros n IH **. destruct n; cbn in H4; inversion H4; clear H4.
  msimpl_in H6.
  destruct s; cbn in *.
  destruct (eval n e env) eqn:E1; cbn in *; try congruence.
  destruct (retr v0) eqn:E2; cbn in *; try congruence.
  destruct v1, n0.
  - destruct (typeof Gamma e) eqn:E3; cbn in *; try congruence.
    destruct (retr t) eqn:E4; cbn in *; try congruence.
    destruct t0.
    destruct (typeof Gamma e0) eqn:E5; cbn in *; try congruence.
    destruct (typeof _ e1) eqn:E6; cbn in *; try congruence.
    destruct (beq t0 t1) eqn:E7.
    + inv H3. minversion E2.
      minversion E4.
      eapply beq_correct in E7. subst.
      eapply IH in E1; eauto.
    + inversion H3.
  - destruct (typeof Gamma e) eqn:E3; cbn in *; try congruence.
    destruct (retr t) eqn:E4; cbn in *; try congruence.
    destruct t0.
    destruct (typeof Gamma e0) eqn:E5; cbn in *; try congruence.
    destruct (typeof _ e1) eqn:E6; cbn in *; try congruence.
    destruct (beq t0 t1) eqn:E7.
    + inv H3. minversion E2.
      minversion E4.
      eapply beq_correct in E7. subst.
      eapply IH in E1; eauto.
      eapply IH in H6; eauto.
      intros. destruct n1.
      mconstructor. eauto.
    + inversion H3.
Qed.

End MiniML_Case.

(** ** mini-ML: recursive abstractions  *)

Section MiniML_Fix.

Variable T : Type.
Context `{retract (ty_lam T) T}.

Variable E : Type.
Context {ret_lam : retract (exp_lam T E) E}.
Context {ret_fix : retract (exp_fix T E) E}.

Variable V : Type.
Context {ret_lam_value : retract (value_lam E V) V}.
Context {ret_fix_value : retract (value_fix E V) V}.

Variable eval : nat -> E -> (nat -> V)  -> option V.

Definition eval_fix (n : nat) (s : E) (env : nat -> V) : option V :=
  match n with
    0 => None
  | S n =>
    match @retr _ _ ret_fix s with
    | Some (fixp ty _ s) => ret (inj (RClos s env))
    | None => match @retract_R _ _ ret_lam s with
             | Some (app s t) => mlet v <- eval n s env ;;
                                 mlet v' <- eval n t env ;;
                                 match @retract_R _ _ ret_lam_value v with
                                 | Some (Clos s e) => eval n s (v' .: e)
                                 | None => mlet (RClos s e) <- @retract_R _ _ ret_fix_value v ;;
                                          eval n s (v .: v' .: e)
                                 end
             | Some _ => eval_lam eval n s env
             | None => None
             end
    end
  end.

MetaCoq Run
  Modular Lemma monotone_fix where exp_fix T E extends E at 1 with [~ eval_fix ~> eval ~] :
  forall n s env, forall t, eval_fix n s env = Some t -> forall m, m >= n -> eval_fix m s env = Some t.
Next Obligation.
  intros n IH s env t. intros. destruct n; cbn  in *.
  - inversion H0.
  - destruct m; try omega. cbn.
    destruct (retr s) eqn:E0; try congruence.
    destruct (@retract_R _ _ ret_lam s) eqn:E1; try congruence.
    destruct e; try congruence.
    + eapply monotone_lam. 2:eassumption. 2:omega. firstorder.
    + destruct (eval n e env) eqn:E2.
      destruct (eval n e0 env) eqn:E3.
      all: try now cbn in *; congruence.
      assert (m >= n) by omega.
      eapply IH in E2 as ->; hnf; eauto.
      eapply IH in E3 as ->; hnf; eauto. cbn in *.
      destruct (@retract_R _ _ ret_lam_value v) eqn:E4. cbn in *. destruct v1.
      all: eauto.
      destruct (@retract_R _ _ ret_fix_value v) eqn:E5. cbn in *. destruct v1.
      all:eauto.
    + eapply monotone_lam. 2:eassumption. 2:omega. firstorder.
Qed.

Variable beq : T -> T -> bool.

Variable typeof : (nat -> T) -> E -> option T.

Definition typeof_fix
           (Gamma : nat -> T) (s : exp_fix T E) : option T :=
  match s with
  | fixp arg_ty ret_ty s => mlet tp' <- typeof (inj (Arr arg_ty ret_ty) .: arg_ty .: Gamma) s;;
                            if beq tp' ret_ty then  ret (inj (Arr arg_ty ret_ty)) else None
                                                                                             
  end.

Hypothesis beq_correct : forall t1 t2, beq t1 t2 = true <-> t1 = t2.

Hypothesis typeof_fix_inj : forall Gamma s, typeof Gamma (inj s) = typeof_fix Gamma s.
Hypothesis typeof_fix_inj' : forall Gamma s, typeof Gamma (@retract_I _ _ ret_lam s) = typeof_lam beq typeof Gamma s.

Variable vtypeis : V -> T -> Prop.

Inductive vtypeis_fix : value_fix E V -> T -> Prop :=
| wf_value_RC s argt env rett Γ :
    (forall x, vtypeis (env x) (Γ x)) ->
    typeof (inj (Arr argt rett) .: argt .: Γ) s = Some rett ->
    vtypeis_fix (RClos s env) (inj (Arr argt rett)).

Hypothesis vtypeis_inj : forall s t, vtypeis (inj s) t <-> vtypeis_fix s t.
Hypothesis vtypeis_inj' : forall s t, vtypeis (@retract_I _ _ ret_lam_value s) t <-> vtypeis_lam typeof vtypeis s t.


Instance vtypeis_inj_imp_fix s t : Imp (vtypeis_fix s t)  (vtypeis (inj s) t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.

Instance vtypeis_inj_imprev_fix s t : ImpRev (vtypeis (inj s) t) (vtypeis_fix s t).
Proof.
  hnf. eapply vtypeis_inj.
Qed.

Instance vtypeis_inj_imp_lam' s t : Imp (vtypeis_lam typeof vtypeis s t)  (vtypeis (inj s) t).
Proof.
  hnf. eapply vtypeis_inj'.
Qed.

Instance vtypeis_inj_imprev_lam' s t : ImpRev (vtypeis (@retract_I _ _ ret_lam_value s) t) (vtypeis_lam typeof vtypeis s t).
Proof.
  hnf. eapply vtypeis_inj'.
Qed.



MetaCoq Run Modular
Lemma typeof_sound_lam where exp_fix T E extends E at 1 with [~ typeof_fix ~> typeof ; eval_fix ~> eval ~] :
  forall n s Gamma env ty v,
            (forall n, vtypeis (env n) (Gamma n)) ->
            typeof Gamma s = Some ty ->
            eval_fix n s env = Some v ->
            vtypeis v ty.
Next Obligation.
  intros n IH s Gamma env ty v.
  unfold subterm_rel, nat_subterm' in *.
  intros H_env.
  destruct n; cbn; intros.
  - congruence.
  - destruct (retr s) eqn:E0.
    + destruct e.
      minversion H1. 
      minversion E0.
      
      rewrite typeof_fix_inj in H0. cbn in H0.
      destruct typeof eqn:E1; cbn in *; try congruence. 
      destruct (beq t1 t0) eqn:E2; try congruence. inv H0.
      mconstructor; eauto.
      rewrite E1. f_equal. now eapply beq_correct.
    + destruct (@retract_R _ _ ret_lam s) eqn:E1; cbn in *; try congruence.
      destruct e; cbn in *; try congruence.
      * minversion E1. 
        eapply typeof_lam_sound in H1; eauto.
        now rewrite typeof_fix_inj' in H0.
      * destruct (eval n e env) eqn:E2; cbn in *; try congruence.
        destruct (eval n e0 env) eqn:E3; cbn in *; try congruence.
        destruct (retr v0) eqn:e4; cbn in *; try congruence.
        -- destruct v2.
           minversion e4.
           minversion E1.
           rewrite typeof_fix_inj' in H0. cbn in H0.
           destruct (typeof Gamma e) eqn:E4; cbn in *; try congruence.
           destruct (typeof Gamma e0) eqn:E5; cbn in *; try congruence.
           destruct (retr t) eqn:E6; cbn in *; try congruence.
           destruct t1; inv H0.
           destruct (beq t1 t0) eqn:E7; try congruence.
           eapply beq_correct in E7; subst. inv H4.
           eapply IH in E2; eauto.
           eapply IH in E3; eauto.
           minversion E2.
           minversion E6.
           eapply IH in H1; eauto.  cbn. destruct n0; eauto.
        -- destruct (@retract_R _ _ ret_fix_value v0) eqn:E4; cbn in *; try congruence.
           destruct v2; cbn in *.
           minversion E1.
           rewrite typeof_fix_inj' in H0.
           cbn in H0.
           destruct (typeof Gamma e) eqn:E5; cbn in *; try congruence.
           destruct (typeof Gamma e0) eqn:E6; cbn in *; try congruence.
           destruct (retr t) eqn:E7; cbn in *; try congruence.
           destruct t1; inv H0.
           destruct (beq t1 t0) eqn:E8; try congruence.
           eapply beq_correct in E8; subst. inv H4.
           eapply IH in E2; eauto.
           eapply IH in E3; eauto.
           minversion E4.
           minversion E2.
           minversion E7.
           eapply IH in H1; eauto.  cbn. destruct n0 as [ | [] ]; eauto.
           now mconstructor. 
      * minversion E1.
        eapply typeof_lam_sound in H1; eauto.
        now rewrite typeof_fix_inj' in H0.
Qed.
        
End MiniML_Fix.
