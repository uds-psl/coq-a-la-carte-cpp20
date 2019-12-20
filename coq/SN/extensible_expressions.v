Require Export header_extensible.
Require Export unscoped.


(** Example Generation for expressions. *)

Inductive ty_lam (T : Type) := arr : T -> T -> ty_lam T.

Definition Arr {T: Type} `{retract (ty_lam T) T} (A B : T) :  T :=
  inj (arr _ A B).

Inductive exp_lam (T E: Type) := lam : T -> E -> exp_lam T E | app : E -> E -> exp_lam T E | var : nat -> exp_lam T E.

Definition Lam {T E: Type} (*`{retract (ty_lam T) T}*) `{retract (exp_lam T E) E} (ty : T) (s : E) : E :=
  inj (lam _ _ ty s).

Definition App {T E: Type} `{retract (exp_lam T E) E} (s t: E) : E :=
  inj (app _ _ s t).

Definition Var {T E: Type} `{retract (exp_lam T E) E} (x : nat) : E :=
  inj (var _ _ x).

Hint Unfold Arr Lam App Var.

Ltac automate_inj :=
  match goal with
  | [H : Var _ = _ |- _] => apply retract_inj in H; inversion H; subst
  | [H : App _ _ = _ |- _] => apply retract_inj in H; inversion H; subst
  | [H : Lam _ _ = _ |- _] => apply retract_inj in H; inversion H; subst
  | [H : Arr _ _ = _ |- _] => apply retract_inj in H; inversion H; subst
  end.

(* EASY *)
Arguments lam {_} {_} s A.
Arguments app {_} {_} s t.
Arguments var {_} {_} x.
Arguments arr {_} A B.


(*
Module Type LamSubstitution.

(* Needed: New variables. Requires also variable for identity. *)
Parameter T E: Type.

(* Needed: Context *)
Context `{retract (ty_lam T) T}.
Context `{retract (exp_lam T E) E}.

Parameter ren_E : (nat -> nat) -> E -> E.
Parameter ren_T: (nat -> nat) -> T -> T.
Parameter ren_id : forall (s : E), forall f, (forall x, f x = x) -> ren_E f s = s.
Parameter subst_E : (nat -> E) -> E -> E.
Parameter subst_id : forall f, (forall x, f x = Var x) -> forall s, subst_E f s = s.

(* Only change: Var/App/Lam instead of var/app/lam. *)
Definition ren_exp_lam (xi : nat -> nat) (s : exp_lam T E) : E :=
  match s with
  | var x => Var (xi x)
  | app s t => App (ren_E xi s) (ren_E xi t)
  | lam A s => Lam A (ren_E (scons 0 (funcomp S xi)) s)
end.

End LamSubstitution.


Module T <: LamSubstitution.
  Definition T := nat.
  Definition E := nat.

End T.
*)


(* Needed: A new section. *)
Section LamSubstitution.

(* Needed: New variables. Requires also variable for identity. *)
Variable T E: Type.

(* Needed: Context *)
(* Context `{retract (ty_lam T) T}. *)
Context `{retract (exp_lam T E) E}.

Variable ren_E : (nat -> nat) -> E -> E.
Variable ren_T: (nat -> nat) -> T -> T.
Variable ren_id : forall (s : E), forall f, (forall x, f x = x) -> ren_E f s = s.
Variable subst_E : (nat -> E) -> E -> E.
Variable subst_id : forall f, (forall x, f x = Var x) -> forall s, subst_E f s = s.

(* Only change: Var/App/Lam instead of var/app/lam. *)
Definition ren_exp_lam (xi : nat -> nat) (s : exp_lam T E) : E :=
  match s with
  | var x => Var (xi x)
  | app s t => App (ren_E xi s) (ren_E xi t)
  | lam A s => Lam A (ren_E (scons 0 (funcomp S xi)) s)
end.


(** TODO: Renamings = Substitutions, Composition *)

Variable subst_ren_exp: forall xi, subst_E (xi >> Var)  = ren_E xi .
Variable subst_exp_comp : forall sigma tau s, subst_E sigma (subst_E tau s) = subst_E (funcomp (subst_E sigma) tau) s .
Variable subst_exp_comp' : forall sigma tau, (subst_E tau) >> (subst_E sigma)  = subst_E (funcomp (subst_E sigma) tau) .

Context `{retract_ren : forall s xi, ren_E xi (inj s) = ren_exp_lam xi s}.

Lemma ren_id_lam (s : exp_lam T E) (IH : (* forall s',  In_lam s' s -> *) forall s', forall f, (forall x, f x = x) -> ren_E f s' = s') :
  forall f, (forall x, f x = x) -> ren_exp_lam f s = inj s.
Proof.
  destruct s as [s|s t|x]; intros; cbn.
  - unfold Lam. f_equal. f_equal.
    apply IH.
    + intros [|x]; eauto.
      cbn. unfold funcomp. now rewrite H0.
  - repeat rewrite IH; try reflexivity; cbn; eauto.
  - rewrite H0. reflexivity.
Defined.

Definition up_exp_exp (sigma : nat -> E) : nat -> E :=
  scons (Var 0) (funcomp (ren_E S) sigma).

Definition subst_exp_lam (sigma : nat -> E) (s : exp_lam T E) : E :=
  match s with
  | var x => sigma x
  | app s t => App (subst_E sigma s) (subst_E sigma t)
  | lam A s => Lam A (subst_E (up_exp_exp sigma) s)
  end.

(* Context `{retract_subst :  forall s sigma, subst_exp sigma (inj s) = subst_exp_lam sigma s}. *)

Lemma subst_id_lam (s : exp_lam T E) (IH : forall s', (* In_lam s' s -> *) forall f, (forall x, f x = Var x) -> subst_E f s' = s') :
  forall f, (forall x, f x = Var x) -> subst_exp_lam f s = inj s.
Proof.
  destruct s as [s|s t|x]; intros; cbn.
  - unfold Lam. f_equal. f_equal.
    apply IH.
(*    + constructor. *)
    + intros [|x]; eauto. cbn. unfold funcomp.
      (* Here we need the retract property of renaming. *)
      now rewrite H0, retract_ren. (* TODO: This will also have to happen in the later definition. *)
  - repeat rewrite IH; try reflexivity; cbn; eauto.
  - now rewrite H0.
Defined.

End LamSubstitution.


(** * Boolean expressions *)

Inductive ty_bool := Bool_ : ty_bool.

Inductive exp_bool E := constBool : bool -> exp_bool E | If_ : E -> E -> E -> exp_bool E.

Definition Bool {T} `{retract ty_bool T} : T :=
  inj Bool_.

Definition If {E} `{retract (exp_bool E) E} (s t u : E) : E :=
  inj (If_ _ s t u).

Definition ConstBool {E} `{retract (exp_bool E) E} (b : bool) : E :=
  inj (constBool _ b).

Arguments constBool {_} b.
Arguments If_ {_} s t u.

Section BoolSubstitution.
Variable T E: Type.

(* Needed: Context *)
Context `{retract (ty_bool ) T}.
Context `{retract (exp_bool E) E}.

Variable Var : nat -> E.

Variable ren_E : (nat -> nat) -> E -> E.
Variable ren_T: (nat -> nat) -> T -> T.
Variable ren_id : forall (s : E), forall f, (forall x, f x = x) -> ren_E f s = s.
Variable subst_E : (nat -> E) -> E -> E.
Variable subst_id : forall f, (forall x, f x = Var x) -> forall s, subst_E f s = s.

(** TODO: Renamings = Substitutions, Composition *)

Variable subst_ren_exp: forall xi, subst_E (xi >> Var)  = ren_E xi .
Variable subst_exp_comp : forall sigma tau s, subst_E sigma (subst_E tau s) = subst_E (funcomp (subst_E sigma) tau) s .
Variable subst_exp_comp' : forall sigma tau, (subst_E tau) >> (subst_E sigma)  = subst_E (funcomp (subst_E sigma) tau) .

Definition ren_exp_bool (xi : nat -> nat) (s : exp_bool E) : E :=
  match s with
  | constBool b => ConstBool b
  | If_ s t u => If (ren_E xi s) (ren_E xi t) (ren_E xi u)
end.

Context `{forall s xi, ren_E xi (inj s) = ren_exp_bool xi s}.

Lemma ren_id_bool (s : exp_bool E) (IH : forall s', forall f, (forall x, f x = x) -> ren_E f s' = s') :
  forall f, (forall x, f x = x) -> ren_exp_bool f s = inj s.
Proof.
  destruct s as [b|s t u]; intros; cbn.
  - reflexivity.
  - repeat rewrite IH; eauto.
Defined.

Definition subst_exp_bool (sigma : nat -> E) (s : exp_bool E) : E :=
  match s with
  | constBool b => ConstBool b
  | If_ s t u => If (subst_E sigma s) (subst_E sigma t) (subst_E sigma u)
end.

Variable retract_subst : forall s sigma, subst_E sigma (inj s) = subst_exp_bool sigma s.


Lemma subst_id_bool (s : exp_bool E) (IH : forall s', (* In_bool s' s -> *) forall f, (forall x, f x = Var x) -> subst_E f s' = s') :
  forall f, (forall x, f x = Var x) -> subst_exp_bool f s = inj s.
Proof.
  destruct s as [b|s t u]; intros; cbn.
  - reflexivity.
  - repeat rewrite IH; eauto.
Defined.

End BoolSubstitution.


(** * Getting them together. *)

Inductive ty := In_ty_lam : ty_lam ty -> ty | In_ty_bool : ty_bool -> ty.

Definition In_ty_lam T `{retract (ty_lam T) T} (t : T) t' : Prop :=
  match t' with
  | arr_ t1 t2 => t = t1 \/ t = t2
  end.

Inductive exp := In_exp_lam : exp_lam ty exp -> exp | In_exp_bool : exp_bool  exp -> exp | Test : exp.

(* I: In_.... thing.
   R : matching, get some and the constructor, else get None
*)
Instance ty_lam_ty : retract (ty_lam ty) ty.
Proof.
  eapply Build_retract with (retract_I := In_ty_lam) (retract_R := fun x => match x with | In_ty_lam (arr s t) => Datatypes.Some (arr s t) | _ => Datatypes.None end).
  - intros []. reflexivity.
  - intros x [].
    + destruct t. intros H. inversion H. subst. reflexivity.
    + cbn. congruence.
Defined.

Lemma some_none_explosion {X : Type} {x : X} {H : Prop} :
  Datatypes.None = Datatypes.Some x  -> H.
Admitted.


Instance exp_lam_exp : retract (exp_lam ty exp) exp.
Proof.
  pose (R := fun x => match x with | In_exp_lam (lam A s) => Datatypes.Some (lam A s) | In_exp_lam (app  s t) => Datatypes.Some (app s t) | In_exp_lam (var x) => Datatypes.Some (var x) | _ => Datatypes.None   end).
  eapply Build_retract with (retract_I := In_exp_lam) (retract_R := R).
  - intros []; reflexivity.
  - refine (fun x y => match y with | In_exp_lam s => _ | _ => some_none_explosion end).
    all: cbn.

    intros x []. cbn. destruct e; intros H; inversion H; subst; reflexivity. cbn. congruence.
Defined.

Instance ty_bool_ty : retract ty_bool  ty.
Proof.
  pose (R := fun x => match x with | In_ty_bool Bool_ => Datatypes.Some Bool_ | _ => Datatypes.None end).
  eapply Build_retract with (retract_I := In_ty_bool) (retract_R := R).
  - intros []. reflexivity.
  - intros x []. cbn. destruct t. intros H. inversion H. subst. intros H. cbn in H. destruct t. inversion H. reflexivity.
Defined.

Instance exp_bool_exp : retract (exp_bool exp) exp.
Proof.
  pose (R := fun x => match x with | In_exp_bool (constBool b) => Datatypes.Some (constBool b) | In_exp_bool (If_  s t u) => Datatypes.Some (If_ s t u) | _ => Datatypes.None  end).
  eapply Build_retract with (retract_I := In_exp_bool) (retract_R := R).
  - intros []; reflexivity.
  - intros x []. cbn. destruct e; intros H; inversion H; subst; reflexivity.
    cbn. destruct e; intros H; inversion H;  subst; reflexivity.
Defined.



(** ** Renamings and Substitutions *)

Fixpoint ren_exp (xi : nat -> nat) (s : exp) : exp :=
  match s with
  | In_exp_lam s => ren_exp_lam _ _ ren_exp xi s
  | In_exp_bool s => ren_exp_bool _ ren_exp xi s
  end.

Fixpoint ren_id (s : exp) : forall f, (forall x, f x = x) -> ren_exp f s = s.
Proof.
  destruct s.
  - intros. cbn. f_equal. rewrite ren_id_lam. reflexivity. eauto. assumption.
  - intros. cbn. f_equal. rewrite ren_id_bool. reflexivity. eauto. assumption.
Qed.

Hint Resolve ren_id.

Fixpoint subst_exp (xi : nat -> exp) (s : exp) : exp :=
  match s with
  | In_exp_lam s => subst_exp_lam _ _ ren_exp subst_exp xi s
  | In_exp_bool s => subst_exp_bool  _ subst_exp xi s
  end.

Fixpoint subst_id (s : exp) : forall f, (forall x, f x = Var x) -> subst_exp f s = s.
Proof.
    destruct s.
  - intros. cbn. f_equal. rewrite subst_id_lam. reflexivity. eauto. apply subst_id. assumption.
  - intros. cbn. f_equal. erewrite subst_id_bool. reflexivity. eauto. assumption.
Qed.

Hint Resolve subst_id.
