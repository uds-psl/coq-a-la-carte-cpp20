Require Export header_metacoq.
From GDTC Require Export features GDTC.

(** ** Autosubst 2 generated combined mini-ML types  *)

Inductive ty : Type :=
  ty_lam_C : ty_lam ty -> ty
| ty_bool_C : ty_bool -> ty
| ty_arith_C : ty_arith -> ty.

Inductive exp :=
| exp_lam_C : exp_lam ty exp -> exp
| exp_bool_C : exp_bool exp -> exp
| exp_arith_C : exp_arith exp -> exp
| exp_case_C : exp_case exp -> exp
| exp_fix_C : exp_fix ty exp -> exp.

Inductive value :=
| value_lam_C : value_lam exp value -> value
| value_bool_C : value_bool -> value
| value_arith_C : value_arith -> value
| value_fix_C : value_fix exp value -> value.

Instance ret_exp_lam : retract (exp_lam ty exp) exp.
Proof.
  unshelve eexists.
  - exact exp_lam_C.
  - intros []. all:try exact (Some e). all:exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_exp_bool : retract (exp_bool exp) exp.
Proof.
  unshelve eexists.
  - exact exp_bool_C.
  - intros []. all: try exact (Some e). all:exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_exp_arith : retract (exp_arith exp) exp.
Proof.
  unshelve eexists.
  - exact exp_arith_C.
  - intros []. all: try exact (Some e). all:exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_exp_case : retract (exp_case exp) exp.
Proof.
  unshelve eexists.
  - exact exp_case_C.
  - intros []. all: try exact (Some e). all:exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_exp_fix : retract (exp_fix ty exp) exp.
Proof.
  unshelve eexists.
  - exact exp_fix_C.
  - intros []. all: try exact (Some e). all:exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.


Instance ret_value_lam : retract (value_lam exp value) value.
Proof.
  unshelve eexists.
  - exact value_lam_C.
  - intros []. all: try exact (Some v). all:exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_value_bool : retract (value_bool) value.
Proof.
  unshelve eexists.
  - exact value_bool_C.
  - intros []. all: try exact (Some v). all:exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_value_arith : retract (value_arith) value.
Proof.
  unshelve eexists.
  - exact value_arith_C.
  - intros []. all: try exact (Some v). all:exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_fix_arith : retract (value_fix exp value) value.
Proof.
  unshelve eexists.
  - exact value_fix_C.
  - intros []. all: try exact (Some v). all:exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_ty_lam : retract (ty_lam ty) ty.
Proof.
  unshelve eexists.
  - exact ty_lam_C.
  - intros []. all: try exact (Some t). all: exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_ty_bool : retract (ty_bool) ty.
Proof.
  unshelve eexists.
  - exact ty_bool_C.
  - intros []. all: try exact (Some t). all: exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.

Instance ret_ty_arith : retract (ty_arith) ty.
Proof.
  unshelve eexists.
  - exact ty_arith_C.
  - intros []. all: try exact (Some t). all: exact None.
  - reflexivity.
  - intros. cbn in *. destruct y; try now inversion H; subst.
Defined.
(* END AS *)
