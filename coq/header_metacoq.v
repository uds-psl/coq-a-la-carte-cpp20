Require Export header_extensible.

From MetaCoq.Template Require Export All.
From MetaCoq.Checker Require Export Checker uGraph.

Local Set Implicit Arguments. 
Require Export String List Omega.
Export ListNotations.
Local Unset Strict Implicit. 

(** ** MetaCoq Commands *)

Class subtermC A := subterm_rel : A -> A -> Prop.
Class InRelC B := {in_subtype : Type ; in_rel : in_subtype -> B -> Prop }.


Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | s => (Γ, s)
  end.

Derive Subterm for nat.

Fixpoint replace_term (c : term) d (t : term) :=
  if @eq_term config.type_in_type init_graph c t then d else
    match t with
  | tRel i => tRel i
  | tEvar ev args => tEvar ev (List.map (replace_term c d) args)
  | tLambda na T M => tLambda na (replace_term c d T) (replace_term c d M)
  | tApp u v => tApp (replace_term c d u) (List.map (replace_term c d) v)
  | tProd na A B => tProd na (replace_term c d A) (replace_term c d B)
  | tCast C kind t => tCast (replace_term c d C) kind (replace_term c d t)
  | tLetIn na b t b' => tLetIn na (replace_term c d b) (replace_term c d t) (replace_term c d b')
  | tCase ind p C brs =>
    let brs' := List.map (on_snd (replace_term c d)) brs in
    tCase ind (replace_term c d p) (replace_term c d C) brs'
  | tProj p C => tProj p (replace_term c d C)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (replace_term c d) (replace_term c d)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (replace_term c d) (replace_term c d)) mfix in
    tCoFix mfix' idx
  | tConst name u => tConst name u
  | x => x
  end.
Require Import Ascii.

Fixpoint name_after_dot' (s : string) (r : string) :=
  match s with
  | EmptyString => r
  | String "#" xs => name_after_dot' xs xs (* see Coq_name in a section *)
  | String ("."%char) xs => name_after_dot' xs xs
  | String _ xs => name_after_dot' xs r
  end.

Definition name_after_dot s := name_after_dot' s s.

Fixpoint fixNames (t : term) :=
  match t with
  | tRel i => tRel i
  | tEvar ev args => tEvar ev (List.map (fixNames) args)
  | tLambda na T M => tLambda na (fixNames T) (fixNames M)
  | tApp u v => tApp (fixNames u) (List.map (fixNames) v)
  | tProd na A B => tProd na (fixNames A) (fixNames B)
  | tCast C kind t => tCast (fixNames C) kind (fixNames t)
  | tLetIn na b t b' => tLetIn na (fixNames b) (fixNames t) (fixNames b')
  | tCase ind p C brs =>
    let brs' := List.map (on_snd (fixNames)) brs in
    tCase ind (fixNames p) (fixNames C) brs'
  | tProj p C => tProj p (fixNames C)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (fixNames) (fixNames)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (fixNames) (fixNames)) mfix in
    tCoFix mfix' idx
  | tConst name u => tConst (name_after_dot name) u
  | tInd (mkInd name i) u => tInd (mkInd (name_after_dot name) i)  u
  | x => x
  end.

Fixpoint replace_const (c : kername) d (t : term) :=
  match t with
  | tRel i => tRel i
  | tEvar ev args => tEvar ev (List.map (replace_const c d) args)
  | tLambda na T M => tLambda na (replace_const c d T) (replace_const c d M)
  | tApp u v => tApp (replace_const c d u) (List.map (replace_const c d) v)
  | tProd na A B => tProd na (replace_const c d A) (replace_const c d B)
  | tCast C kind t => tCast (replace_const c d C) kind (replace_const c d t)
  | tLetIn na b t b' => tLetIn na (replace_const c d b) (replace_const c d t) (replace_const c d b')
  | tCase ind p C brs =>
    let brs' := List.map (on_snd (replace_const c d)) brs in
    tCase ind (replace_const c d p) (replace_const c d C) brs'
  | tProj p C => tProj p (replace_const c d C)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (replace_const c d) (replace_const c d)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (replace_const c d) (replace_const c d)) mfix in
    tCoFix mfix' idx
  | tConst name u => if eq_string name c then d else tConst name u
  | x => x
  end.

Fixpoint remove_injs (k : nat) (u : term) {struct u} : term :=
  match u with
  | tRel n => tRel n
  | tEvar ev args => tEvar ev (map (remove_injs k) args)
  | tCast c kind ty => tCast (remove_injs k c) kind (remove_injs k ty)
  | tProd na A B => tProd na (remove_injs k A) (remove_injs (S k) B)
  | tLambda na T M => tLambda na (remove_injs k T) (remove_injs (S k) M)
  | tLetIn na b ty b' => tLetIn na (remove_injs k b) (remove_injs k ty) (remove_injs (S k) b')
  | tApp u0 v => let L := remove_injs k u0 in
                let R := map (remove_injs k) v in
                match L, R with tConst "header_extensible.retract_I" _ , [_;_;_;tRel k'] => (* if k =? k' then *) tRel k' (* else mkApps L R *)
                           | _,_ => mkApps L R end
  | tCase ind p c brs => let brs' := map (on_snd (remove_injs k)) brs in tCase ind (remove_injs k p) (remove_injs k c) brs'
  | tProj p c => tProj p (remove_injs k c)
  | tFix mfix idx => let k' := #|mfix| + k in let mfix' := map (map_def (remove_injs k) (remove_injs k')) mfix in tFix mfix' idx
  | tCoFix mfix idx =>
      let k' := #|mfix| + k in let mfix' := map (map_def (remove_injs k) (remove_injs k')) mfix in tCoFix mfix' idx
  | _ => u
  end.

Fixpoint replace_terms Repl t :=
  match Repl with
  | ((c, s) :: Repl) => replace_terms Repl (replace_term c s t)
  | _ => t
  end.

Fixpoint replace_consts Repl t :=
  match Repl with
  | ((tConst na u, s) :: Repl) => replace_consts Repl (replace_const na s t)
  | _ => t
  end.

Fixpoint replace_ext T T_ext t :=
  match t with
  | tProd na argT retT => if @eq_term config.default_checker_flags init_graph argT T_ext
                         then tProd na T (remove_injs 0 (replace_ext T T_ext retT))
                         else tProd na argT (replace_ext T T_ext retT)
  | s => s
  end.

(* todo here  *)
Definition genIH retT decl_list LT (T T_ext : term) Repl :=
  match LT with
    Some LT =>
    let IH := replace_terms Repl retT in
    let IH := (it_mkProd_or_LetIn decl_list ((tProd nAnon (tApp LT [tRel 0; tRel 1]) (lift 1 0 IH)))) in
    let IH := replace_ext T T_ext IH in
    IH
  | None =>
    let IH := replace_terms Repl retT in
    let IH := (it_mkProd_or_LetIn decl_list (IH)) in
    let IH := replace_ext T T_ext IH in
    IH
  end.

Fixpoint genStatement LT decl_list (T T_ext : term) Repl n B :=
  match n, B with
  | 0, retT => let IH := genIH retT (decl_list) (Some LT) T T_ext Repl in
                            it_mkProd_or_LetIn (decl_list) ((tProd nAnon IH (lift 1 0 retT)))
  | S n, tProd na argT retT => (genStatement LT (vass na argT :: decl_list) T T_ext Repl n retT)
  | _, _ => tVar "no"
  end.

Fixpoint genStatement_no_lt decl_list (T T_ext : term) Repl n B :=
  match n, B with
  | 0, retT => let IH := genIH retT (decl_list) None T T_ext Repl in
                            (IH, it_mkProd_or_LetIn (decl_list) ((tProd nAnon IH (lift 1 0 retT))))
  | S n, tProd na argT retT => (genStatement_no_lt (vass na argT :: decl_list) T T_ext Repl n retT)
  | _, _ => (tVar "no", tVar "no")
  end.

Fixpoint remove_suffix (a1 a2 s : string) : string :=
  match s with
  | EmptyString => a1
  | String "_"%char s =>
    remove_suffix (append a1 a2) (String "_"%char EmptyString) s
  | String c s => remove_suffix a1 (append a2 (String c EmptyString)) s
  end.

Definition mkLemma name (t : term) : TemplateMonad unit :=
  tmBind (tmUnquoteTyped Prop (fixNames t)) (fun t => tmBind (tmLemma name t) (fun _ => tmReturn tt)).

Definition mkVariable name (t : term) : TemplateMonad unit :=
  A <- tmAbout name ;;
  match A with None => 
               tmBind (tmUnquoteTyped Type (fixNames t)) (fun t => tmBind (tmVariable name t) (fun _ => tmReturn tt))
          | Some s => tmPrint "variable already exists, not defining"
  end.

Definition Forall' (name : ident) (n : nat) T T_ext Repl (A_P : term) (P : term) : TemplateMonad term :=
  match destArity nil P with (Gamma, _)=>
  match nth_error (rev Gamma) (Nat.pred n) with Some T' => let T' := fixNames (decl_type T') in
         T' <- tmUnquoteTyped Type T' ;;
         O <- tmInferInstance None (InRelC T') ;;
         match O with
         | Some Cl => let lt := @in_rel _ Cl in
                     LT <- tmQuote lt ;;
                     let St := genStatement LT [] T T_ext Repl n P in ret St
         | None => O <- tmInferInstance None (subtermC T') ;;
                    match O with
                    | Some Cl => let lt := @subterm_rel _ Cl in
                                LT <- tmQuote lt ;;
                                let St := genStatement LT [] T T_ext Repl n P in ret St
                    | None => let (IH, St) := genStatement_no_lt [] T T_ext Repl n P in
                             newname <- tmEval cbv (remove_suffix EmptyString EmptyString name) ;;
                             newname <- tmFreshName newname ;;
                             mkVariable newname (fixNames IH);;
                             ret St
                    end
         end
  | _ => tmFail "not enough arguments"
  end end.

Inductive genList : Type := genNil | genCons (A B : Type) (a : A) (b : B) : genList -> genList.

Fixpoint quote_list L1 : TemplateMonad (list (term * term)) :=
  match L1 with
  | genNil => ret []
  | genCons _ _ a b L => t <- tmQuote a ;; t' <- tmQuote b ;; L <- quote_list L ;; ret ((t,t') :: L)
  end.

Definition Forall (name : ident) (T : Type) (T_ext : Type) (n : nat) Repl {A_P : Type} (P : A_P) :=
  T <- tmQuote T ;;
  T_ext <- tmQuote T_ext ;;
  A_P <- tmQuote A_P ;;
  P <- tmQuote P ;;
  Repl <- quote_list Repl ;;
  St <- Forall' name n T T_ext Repl A_P P ;;
  (* (tmEval cbn St >>= tmPrint) ;; *)
  mkLemma name St.

Definition getName X (x : X) :=
  x <- tmEval cbv x;;
  t <- tmQuote x ;; match t with tLambda (nNamed na) _ _ => ret na | _ => ret "" end.

Definition ForallN (name : nat -> nat) (T : Type) (T_ext : Type) (n : nat) Repl {A_P : Type} (P : A_P) :=
  name <- getName name ;;
  T <- tmQuote T ;;
  T_ext <- tmQuote T_ext ;;
  A_P <- tmQuote A_P ;;
  P <- tmQuote P ;;
  Repl <- quote_list Repl ;;
  St <- Forall' name n T T_ext Repl A_P P ;;
  mkLemma name St.


Hint Extern 0 (subterm_rel _ _) => hnf.

Global Obligation Tactic := idtac.

Definition cns {X Y} '(x,y) := @genCons X Y x y.

Notation "x ~> y" := (x,y) (only parsing, at level 60).

Notation "[~ x ~]" := (cns x genNil) : list_scope.
Notation "[~ x ; y ; .. ; z ~]" := (cns x (cns y .. (cns z genNil) ..)) : list_scope.

Notation "'Modular' 'Lemma' na 'where' T_ext 'extends' T 'at' n 'with' C ':' P" := (ForallN (fun na : nat => na) T T_ext n C P) (at level 1, n at next level, C at next level, P at next level).
Notation "'Modular' 'Lemma' na 'where' T_ext 'extends' T 'with' C ':' P" := (ForallN (fun na : nat => na) T T_ext 0 C P) (at level 1, C at next level, P at next level).


Instance nat_subterm' : subtermC nat := lt.

Ltac inv H2 := inversion H2; subst; clear H2.

Definition tmMkDefinition name (t : term) : TemplateMonad unit :=
  tmBind (tmUnquote (fixNames t)) (fun t => tmBind (tmDefinitionRed name (Some hnf) t) (fun _ => tmReturn tt)).

Fixpoint split_forall_impl decls T :=
  match T with
  | tProd nAnon H1 H2 => (decls, H1, H2)
  | tProd na A B => split_forall_impl (vass na A :: decls) B
  | _ => ([], tVar "no", tVar "no")
  end.

Definition buildImp args H1 H2 :=
  it_mkProd_or_LetIn args (tApp (tConst "Imp" Instance.empty) [ H1; H2 ]).

Inductive GenList : Type := GenNil | GenCons (A : Type) (a : A) : GenList -> GenList.

Ltac apply_one L :=
  match constr:(L) with
  | GenNil => fail 1
  | GenCons ?a ?L => (now eapply a; eauto) || apply_one L
  end.

Class has_features (X : string) := features : list string.
Definition get_features X {H : has_features X} := features.

Definition tmTryInferInstance (red : option reductionStrategy) A :=
  I <-  tmInferInstance red A ;; match I with Some x => ret x | _ => tmFail "no instance found" end.

Definition get_name_of (t : term) :=
  match t with
  | tConst c u => c
  | tInd c u => inductive_mind c
  | tApp (tConst c u) _ => c
  | tApp (tInd c u) _ => inductive_mind c
  | _ => ""
  end.

Fixpoint get_name (n : nat) (P : term) : string :=
  match n, P with
  | 0, tProd na A B => get_name_of A
  | S n, tProd na A B => get_name n B
  | _ , _ => "no name found"
  end.

Definition get_lemmas (X : string) (name : string) : TemplateMonad GenList :=
  I <- tmTryInferInstance None (has_features X) ;;
  feats <- tmEval hnf (@get_features X I) ;;
  @monad_fold_left _ TemplateMonad_Monad GenList string (fun L feature => A <- tmUnquote (tConst (append (append name "_") feature) Instance.empty) ;;
                                                                       A' <- tmEval cbn (my_projT2 A);;
                                 ret (GenCons A' L)) feats GenNil.                                   

Definition get_lemmas_and_name (na : nat -> nat) (n : nat) (P : Type) :=
  na <- getName na;;
  P_syn <- tmQuote P ;;
  N <- tmEval cbv (name_after_dot (get_name n P_syn)) ;;
  get_lemmas N na.

Definition compose_fixpoint (na : nat -> nat) (P : Type) (body : P) :=
  na <- getName na;;
  tmDefinition na body.

Ltac int_dest n :=
  match constr:(n) with
  | 0 => let s := fresh "s" in intros s; destruct s
  | S ?n => let s := fresh "s" in intros s; int_dest n
  end.

Ltac int_inv n :=
  match constr:(n) with
  | 0 => let s := fresh "s" in intros s; inversion s
  | S ?n => let s := fresh "s" in intros s; int_inv n
  end.

Ltac int_ind ind n :=
  match constr:(n) with
  | 0 => let s := fresh "s" in intros s; induction s using ind; cbn
  | S ?n => let s := fresh "s" in intros s; int_ind ind n
  end.

Ltac fix_nat f n := let f := fresh "f" in
  match constr:(n) with
  | 0 => fix f 0
  | 1 => fix f 1
  | 2 => fix f 2
  | 3 => fix f 3
  | 4 => fix f 4
  | 5 => fix f 5
  | 6 => fix f 6
  | 7 => fix f 7
  | _ => fail
  end.
    
Notation "'Compose' 'Fixpoint' nm 'on' n ':' P" :=
  (let na := fun nm => nm in @compose_fixpoint na (P%type) ((ltac:(let k x := (fix_nat f (S n); int_dest n; apply_one x) in run_template_program (get_lemmas_and_name na n P) k)))) (at level 1, n at next level, P at next level).
Notation "'Compose' 'Lemma' nm 'on' n ':' P" :=
  (let na := fun nm => nm in @compose_fixpoint na (P%type) ((ltac:(let k x := (fix_nat f (S n); int_dest n; apply_one x) in run_template_program (get_lemmas_and_name na n P) k)))) (at level 1, n at next level, P at next level).
Notation "'Compose' 'Lemma' nm 'on' n 'by' 'inversion' ':' P" :=
  (let na := fun nm => nm in @compose_fixpoint na (P%type) ((ltac:(let k x := (fix_nat f (S n); int_inv n; apply_one x) in run_template_program (get_lemmas_and_name na n P) k)))) (at level 1, n at next level, P at next level).
Notation "'Compose' 'Lemma' nm 'on' n 'using' ind ':' P" :=
  (let na := fun nm => nm in @compose_fixpoint na (P%type) ((ltac:(let k x := (fix_nat f (S n); int_ind ind n; apply_one x) in run_template_program (get_lemmas_and_name na n P) k)))) (at level 1, n at next level, ind at next level, P at next level).

(* Modular Fixpoints *)

Definition genStatement_Fix (T T_ext : term) retT :=
  let IH := genIH retT [] None T T_ext [] in
    (IH, retT).

Definition mkDefinitionType name (T : Type) (t : term) : TemplateMonad unit :=
  tmBind (tmUnquoteTyped T (fixNames t)) (fun t => tmBind (tmDefinition name t) (fun _ => tmReturn tt)).

Definition ModularFixpointN (name : nat -> nat) (T : Type) (T_ext : Type) (P: Type) (A : Type) (body : A -> P) :=
  name <- getName name ;;
  T <- tmQuote T ;;
  T_ext <- tmQuote T_ext ;;
  P_syn <- tmQuote P ;;
  body_syn <- tmQuote body ;;
  let IH := genIH P_syn [] None T T_ext [] in
  newname <- tmEval cbv (remove_suffix EmptyString EmptyString name) ;;
  newname <- tmFreshName newname ;;
  mkVariable newname (fixNames IH);;
  mkDefinitionType name P (tApp body_syn [tVar newname]).

Definition ModularFixpoint2 (name : nat -> nat) (T : Type) (T_ext : Type) (P: Type) (body : P) :=
  name <- getName name ;;
  T <- tmQuote T ;;
  T_ext <- tmQuote T_ext ;;
  P_syn <- tmQuote P ;;
  body_syn <- tmQuote body ;;
  let IH := genIH P_syn [] None T T_ext [] in
  newname <- tmEval cbv (remove_suffix EmptyString EmptyString name) ;;
  newname <- tmFreshName newname ;;
  mkVariable newname (fixNames IH);;
  mkDefinitionType name P body_syn.

Notation "'Modular' 'Fixpoint' na 'where' T_ext 'extends' T 'with' c ':=' p" := (@ModularFixpointN (fun na : nat => na) T T_ext _ _ (fun c => p)) (at level 1, T_ext at next level, T at next level, c at next level, p at next level).

Notation "'Modular' 'Fixpoint' na 'where' T_ext 'extends' T ':=' p" := (@ModularFixpoint2 (fun na : nat => na) T T_ext _ p) (at level 1, T_ext at next level, T at next level, p at next level).


Hint Extern 0 => reflexivity.



(* Definition tmkAddInjection (name : ident) T := *)
(*   T_syn <- tmQuote T ;; *)
(*   let '((args, H1), H2) := split_forall_impl [] T_syn in *)
(*   mkVariable name T;;  *)
(*   let I_syn := buildImp args H1 H2 in *)
(*   I <- tmUnquoteTyped Type I_syn;; *)
(*   i <- tmUnquoteTyped I (tConst name Instance.empty)  ;; *)
(*   (tmBind (tmDefinition (append name "_inst") i) (fun _ => tmReturn tt)). *)
