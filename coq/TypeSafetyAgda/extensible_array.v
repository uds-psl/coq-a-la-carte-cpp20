Require Export header_extensible.

Section ty.
Inductive ty  : Type :=
  | TArray : ty
  | TOption : ty
  | TNat : ty .

Lemma congr_TArray  : TArray  = TArray  .
Proof. congruence. Qed.

Lemma congr_TOption  : TOption  = TOption  .
Proof. congruence. Qed.

Lemma congr_TNat  : TNat  = TNat  .
Proof. congruence. Qed.

End ty.

Section exp_plus.
Variable exp : Type.

Inductive exp_plus  : Type :=
  | atom : nat   -> exp_plus
  | plus : exp   -> exp   -> exp_plus .

Variable retract_exp_plus : retract exp_plus exp.

Definition atom_  (s0 : nat ) : _ :=
  inj (atom s0).

Definition plus_  (s0 : exp ) (s1 : exp ) : _ :=
  inj (plus s0 s1).

Lemma congr_atom_  { s0 : nat   } { t0 : nat   } : s0 = t0 -> atom_ s0 = atom_ t0 .
Proof. congruence. Qed.

Lemma congr_plus_  { s0 : exp   } { s1 : exp   } { t0 : exp   } { t1 : exp   } : s0 = t0 -> s1 = t1 -> plus_ s0 s1 = plus_ t0 t1 .
Proof. congruence. Qed.

End exp_plus.

Section exp_opt.
Variable exp : Type.

Inductive exp_opt  : Type :=
  | none : exp_opt
  | some : exp   -> exp_opt .

Variable retract_exp_opt : retract exp_opt exp.

Definition none_  : _ :=
  inj (none ).

Definition some_  (s0 : exp ) : _ :=
  inj (some s0).

Lemma congr_none_  : none_  = none_  .
Proof. congruence. Qed.

Lemma congr_some_  { s0 : exp   } { t0 : exp   } : s0 = t0 -> some_ s0 = some_ t0 .
Proof. congruence. Qed.

End exp_opt.

Section exp_arr.
Variable exp : Type.

Inductive exp_arr  : Type :=
  | nil : exp_arr
  | rd : exp   -> exp   -> exp_arr
  | wr : exp   -> exp   -> exp   -> exp_arr .

Variable retract_exp_arr : retract exp_arr exp.

Definition nil_  : _ :=
  inj (nil ).

Definition rd_  (s0 : exp ) (s1 : exp ) : _ :=
  inj (rd s0 s1).

Definition wr_  (s0 : exp ) (s1 : exp ) (s2 : exp ) : _ :=
  inj (wr s0 s1 s2).

Lemma congr_nil_  : nil_  = nil_  .
Proof. congruence. Qed.

Lemma congr_rd_  { s0 : exp   } { s1 : exp   } { t0 : exp   } { t1 : exp   } : s0 = t0 -> s1 = t1 -> rd_ s0 s1 = rd_ t0 t1 .
Proof. congruence. Qed.

Lemma congr_wr_  { s0 : exp   } { s1 : exp   } { s2 : exp   } { t0 : exp   } { t1 : exp   } { t2 : exp   } : s0 = t0 -> s1 = t1 -> s2 = t2 -> wr_ s0 s1 s2 = wr_ t0 t1 t2 .
Proof. congruence. Qed.

End exp_arr.

Section exp.
Inductive exp  : Type :=
  | In_exp_plus : exp_plus exp  -> exp
  | In_exp_arr : exp_arr exp  -> exp
  | In_exp_opt : exp_opt exp  -> exp .

Lemma congr_In_exp_plus  { s0 : exp_plus exp  } { t0 : exp_plus exp  } : s0 = t0 -> In_exp_plus s0 = In_exp_plus t0 .
Proof. congruence. Qed.

Lemma congr_In_exp_arr  { s0 : exp_arr exp  } { t0 : exp_arr exp  } : s0 = t0 -> In_exp_arr s0 = In_exp_arr t0 .
Proof. congruence. Qed.

Lemma congr_In_exp_opt  { s0 : exp_opt exp  } { t0 : exp_opt exp  } : s0 = t0 -> In_exp_opt s0 = In_exp_opt t0 .
Proof. congruence. Qed.

Global Instance retract_exp_plus_exp  : retract (exp_plus exp) exp := Build_retract In_exp_plus (fun x => match x with
| In_exp_plus s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_exp_plus t' => fun H => congr_In_exp_plus (eq_sym (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_exp_opt_exp  : retract (exp_opt exp) exp := Build_retract In_exp_opt (fun x => match x with
| In_exp_opt s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_exp_opt t' => fun H => congr_In_exp_opt (eq_sym (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_exp_arr_exp  : retract (exp_arr exp) exp := Build_retract In_exp_arr (fun x => match x with
| In_exp_arr s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_exp_arr t' => fun H => congr_In_exp_arr (eq_sym (Some_inj H))
| _ => some_none_explosion
end) .

End exp.


Arguments atom_ {_} {_}.
Arguments rd_ {_} {_}.
Arguments wr_ {_} {_}.
Arguments plus_ {_} {_}.
Arguments none_ {_} {_}.
Arguments some_ {_} {_}.
Arguments nil_ {_} {_}.
