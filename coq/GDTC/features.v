Require Import header_metacoq.

Set Implicit Arguments.

(** * Case Study 2: Monotonicty and Type Safety for big-step mini-ML  *)

(** ** Autosubst 2 generated code  *)

Notation included F T := (retract (F T) T)%type.
Notation "s .: T" := (fun n => match n with 0 => s | S n => T n end) (right associativity, at level 70).

Section Lambdas.

Variable T : Type.
Inductive ty_lam := Arr : T -> T -> ty_lam.
Context `{retract ty_lam T}.
Definition In_ty_lam (t : T) t' : Prop :=
  match t' with
  | Arr t1 t2 => t = t1 \/ t = t2
  end.

Variable E : Type.
Inductive exp_lam := lam : T -> E -> exp_lam | app : E -> E -> exp_lam | var : nat -> exp_lam.
Context `{retract exp_lam E}.

Definition In_lam (x : E) (s : exp_lam) :  Prop :=
  match s with
  | lam ty s => x = s
  | app s t => x = s \/ x = t
  | _ => False
  end.
Global Instance In_ty_lam' : InRelC _ := Build_InRelC In_ty_lam.

Definition Lam (ty : T) (s : E) : E :=
  inj (lam ty s).

Definition App (s t: E) : E :=
  inj (app s t).

Definition Var (x : nat) : E :=
  inj (var x).


Variable V : Type.
Inductive value_lam  :=
| Clos : E -> (nat -> V) -> value_lam.

End Lambdas.

Section Booleans.

  Variable T : Type.
Inductive ty_bool := Bool : ty_bool.
Context `{retract ty_bool T}.

Definition In_ty_bool (x : T) (y : ty_bool) := False.

Global Instance subterm_ty_bool : InRelC _ := Build_InRelC In_ty_bool.
  
Variable E : Type.
Inductive exp_bool:= constBool : bool -> exp_bool | If : E -> E -> E -> exp_bool.
Context `{retract exp_bool E}.

Definition In_bool (x : E) (s:  exp_bool) :  Prop :=
  match s with
  | If s t u => x = s \/ x = t \/ x = u
  | _ => False
  end.

Variable V : Type.
Inductive value_bool :=
| Boolean : bool -> value_bool.
Context `{retract value_bool V}.

End Booleans.

Arguments subterm_ty_bool {_}.

Section Arith.
  Variable E : Type.
Inductive exp_arith := Num (n : nat) | Plus : E -> E -> exp_arith.
Context `{retract exp_arith E}.

Definition In_arith (x : E) (s:  exp_arith) :  Prop :=
  match s with
  | Plus s t => x = s \/ x = t
  | _ => False
  end.

Variable V : Type.
Inductive value_arith :=
| Number : nat -> value_arith.
Context `{retract value_arith V}.

Inductive ty_arith := Nat : ty_arith.
Variable T : Type.
Context `{retract ty_arith T}.
Definition In_ty_arith (x : T) (y : ty_arith) := False.

Global Instance subterm_ty_arith : InRelC _ := Build_InRelC In_ty_arith.

End Arith.

Section NatCase.
  Variable E : Type.
Inductive exp_case := Case : E -> E -> E -> exp_case.
Context `{True}. (* FIXME: removing this changes names *)
Context `{retract exp_case E}.

Definition In_case (x : E) (s:  exp_case) :  Prop :=
  match s with
  | Case s t u => x = s \/ x = t \/ x = u
  end.

Variable T : Type.
Context { HR : retract ty_arith T}. (* TODO: How to signal this in autosubst? The nat_case feature depends on the arith feature, at least for types.  *)

Global Instance subterm_ty_arith' : InRelC _ := Build_InRelC (@In_ty_arith T).

Variable V : Type.
Context `{retract value_arith V}.
End NatCase.
Arguments subterm_ty_arith {_}.

Section Fix.
  
Variable T : Type.

Variable E : Type.

Inductive exp_fix := fixp : T -> T -> E -> exp_fix.

Context {ret_lam : retract (exp_lam T E) E}.
Context {ret_fix : retract exp_fix E}.

(* Version to use a general induction principle. *)
Definition In_fix (x : E) (s : exp_fix) :  Prop :=
  match s with
  | fixp ty _ s => x = s
  end.

Variable V : Type.

Context {ret_lam_value : retract (value_lam E V) V}.

Inductive value_fix := RClos : E -> (nat -> V) -> value_fix.
Context {ret_fix_value : retract (value_fix) V}.
End Fix.
