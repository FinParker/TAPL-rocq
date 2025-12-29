(** * Stlc: The Simply Typed Lambda-Calculus *)

(** The simply typed lambda-calculus (STLC) formalizes functional
    abstraction with variable binding and substitution. We define
    syntax, small-step semantics, and typing rules, then prove
    type safety via progress and preservation. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
(* Set Default Goal Selector "!". *)

(* ################################################################# *)
(** * Syntax *)

Module STLC.

(** Types *)
Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(** Terms *)
Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.

Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.

Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 200,
                    x custom stlc_tm,
                    y custom stlc_tm,
                    z custom stlc_tm at level 200,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_tm at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_tm at level 0).

(** We'll write type inside of [<{{ ... }}>] brackets and terms inside [<{ .. }>] brackets.
    Examples are notations for common functions. *)

Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(** Common function abstractions *)
Notation idB :=
  <{ \x:Bool, x }>.

Notation idBB :=
  <{ \x:Bool->Bool, x }>.

Notation idBBBB :=
  <{ \x: (Bool->Bool)->(Bool->Bool), x}>.

Notation k := <{ \x:Bool, \y:Bool, x }>.

Notation notB := <{ \x:Bool, if x then false else true }>.

(* ================================================================= *)
(** * Operational Semantics *)

(** Values - abstractions and boolean constants do not step.
    Abstractions are not reduced under their binders. *)
Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Hint Constructors value : core.

(** Substitution: [x:=s]t substitutes [s] for free occurrences of [x] in [t]. *)


Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tm_var x) s
  | s_var2 : forall y,
      x <> y ->
      substi s x (tm_var y) (tm_var y)
  | s_abs1 : forall T t1,
      substi s x <{\x:T, t1}> <{\x:T, t1}>
  | s_abs2 : forall y T t1 t1',
      x <> y ->
      substi s x t1 t1' ->
      substi s x <{\y:T, t1}> <{\y:T, t1'}>
  | s_app : forall t1 t2 t1' t2',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x <{t1 t2}> <{t1' t2'}>
  | s_true :
      substi s x <{true}> <{true}>
  | s_false :
      substi s x <{false}> <{false}>
  | s_if : forall t1 t2 t3 t1' t2' t3',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x t3 t3' ->
      substi s x <{if t1 then t2 else t3}> <{if t1' then t2' else t3'}>.

Hint Constructors substi : core.

Theorem substi_correct : forall s x t t',
  <{ [x:=s]t }> = t' <-> substi s x t t'.
Proof.
  (* FILL IN HERE *) Admitted.

(** Reduction - small-step semantics of STLC *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{[x:=v2]t1}>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** Examples of evaluation *)
(* Lemma step_example1 :
  <{idBB idB}> -->* idB.
Proof. eapply multi_step. apply ST_AppAbs. apply v_abs. simpl. apply multi_refl. Qed. *)

Lemma step_example2 :
  <{idBB (idBB idB)}> -->* idB.
Proof.
  eapply multi_step. apply ST_App2. auto. apply ST_AppAbs. auto.
  eapply multi_step. apply ST_AppAbs. simpl. auto. simpl. apply multi_refl. Qed.

Lemma step_example3 :
  <{idBB notB true}> -->* <{false}>.
Proof.
  eapply multi_step. apply ST_App1. apply ST_AppAbs. auto.
  simpl. eapply multi_step. apply ST_AppAbs. auto. simpl.
  eapply multi_step. apply ST_IfTrue. apply multi_refl. Qed.

Lemma step_example4 :
  <{idBB (notB true)}> -->* <{false}>.
Proof.
  eapply multi_step. apply ST_App2; auto.
  eapply multi_step. apply ST_App2; auto. apply ST_IfTrue.
  eapply multi_step. apply ST_AppAbs. auto. simpl. apply multi_refl. Qed.

(** Using normalize from Smallstep *)
Lemma step_example1' : <{idBB idB}> -->* idB. Proof. normalize. Qed.
Lemma step_example2' : <{idBB (idBB idB)}> -->* idB. Proof. normalize. Qed.
Lemma step_example3' : <{idBB notB true}> -->* <{false}>. Proof. normalize. Qed.
Lemma step_example4' : <{idBB (notB true)}> -->* <{false}>. Proof. normalize. Qed.

Lemma step_example5 : <{idBBBB idBB idB}> -->* idB. Proof. (* FILL IN HERE *) Admitted.
Lemma step_example5_with_normalize : <{idBBBB idBB idB}> -->* idB. Proof. (* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Typing *)

(** Contexts map variables to their types *)
Definition context := partial_map ty.

(** Typing judgement: [Gamma |-- t \in T] means [t] has type [T] under context [Gamma] *)




Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x constr at level 0, v  custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := (update empty x v)
  (in custom stlc_tm at level 0, x constr at level 0, v custom stlc_ty) : stlc_scope.

Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
            (at level 0, Gamma custom stlc_tm at level 200, t custom stlc_tm, T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T1 Gamma,
       <{ Gamma |-- t1 \in Bool }> ->
       <{ Gamma |-- t2 \in T1 }> ->
       <{ Gamma |-- t3 \in T1 }> ->
       <{ Gamma |-- if t1 then t2 else t3 \in T1 }>

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T) : stlc_scope.

Hint Constructors has_type : core.

(** Typing examples *)
Example typing_example_1 :
  <{ empty |-- \x:Bool, x \in Bool -> Bool }>.
Proof. eauto. Qed.

Example typing_example_2 :
  <{ empty |--
    \x:Bool, \y:Bool->Bool, (y (y x)) \in
    Bool -> (Bool -> Bool) -> Bool }>.
Proof. eauto 20. Qed.

Example typing_example_2_full :
 <{ empty |--
    \x:Bool, \y:Bool->Bool, (y (y x)) \in
    Bool -> (Bool -> Bool) -> Bool }>.
Proof. (* FILL IN HERE *) Admitted.

Example typing_example_3 :
  exists T,
   <{ empty |--
      \x:Bool->Bool, \y:Bool->Bool, \z:Bool, (y (x z)) \in T }>.
Proof.
  exists <{{ (Bool->Bool) -> (Bool->Bool) -> Bool -> Bool }}>.
  apply T_Abs. apply T_Abs. apply T_Abs.
  apply T_App with (T2:=<{{Bool}}>). apply T_Var. reflexivity.
  apply T_App with (T2:=<{{Bool}}>). apply T_Var. reflexivity.
  apply T_Var. reflexivity.
Qed.

(** Terms that are not typable *)
Example typing_nonexample_1 :
  ~ exists T,
    <{  empty |-- \x:Bool, \y:Bool, (x y) \in T }>.
Proof.
  intros Hc. destruct Hc as [T Hc].
  inversion Hc; subst; clear Hc.
  inversion H4; subst; clear H4.
  inversion H5; subst; clear H5 H4.
  inversion H2; subst; clear H2. discriminate H1.
Qed.

Example typing_nonexample_3 :
  ~ (exists S T,
      <{ empty |-- \x:S, x x \in T }>).
Proof. (* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Type Safety Properties *)

(** Theorem [Uniqueness of Types]: In a typing context Γ, if a term t
    has type T, then it has no other type. *)
Theorem uniqueness_of_types : forall Gamma t T1 T2,
  <{ Gamma |-- t \in T1 }> ->
  <{ Gamma |-- t \in T2 }> ->
  T1 = T2.
Proof.
Admitted.


(** Lemma [Canonical Forms]: Values have restricted shapes based on type.
    1. If v is a value of type Bool, then v is either true or false.
    2. If v is a value of type T1→T2, then v = λx:T1.t2. *)
Lemma canonical_forms_bool : forall Gamma v,
  <{ Gamma |-- v \in Bool }> ->
  value v ->
  (v = <{true}> \/ v = <{false}>).
Proof. Admitted.

Lemma canonical_forms_fun : forall Gamma v T1 T2,
  <{ Gamma |-- v \in T1 -> T2 }> ->
  value v ->
  exists x t, v = <{\x:T1, t}>.
Proof. Admitted.


(** Theorem [Progress]: A closed, well-typed term is either a value or can step. *)
Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
Proof.
Admitted.

(** Lemma [Permutation]: Context permutation preserves typing. *)
Lemma permutation : forall Gamma Delta t T,
  (forall x, Gamma x = Delta x) ->
  <{ Gamma |-- t \in T }> ->
  <{ Delta |-- t \in T }>.
Proof.
Admitted.

(** Lemma [Weakening]: Adding a binding to context preserves typing. *)
Lemma weakening : forall Gamma x S t T,
  <{ Gamma |-- t \in T }> ->
  <{ (x |-> S ; Gamma) |-- t \in T }>.
Proof.
Admitted.

(** Lemma [Substitution]: Substitution preserves types.
    If Γ,x:S ⊢ t:T and Γ ⊢ s:S, then Γ ⊢ [x:=s]t:T *)
Lemma substitution : forall Gamma x S t T s,
  <{ (x |-> S ; Gamma) |-- t \in T }> ->
  <{ Gamma |-- s \in S }> ->
  <{ Gamma |-- [x:=s]t \in T }>.
Proof.
Admitted.

(** Theorem [Preservation]: Evaluation preserves types.
    If Γ ⊢ t:T and t → t', then Γ ⊢ t':T *)
Theorem preservation : forall Gamma t t' T,
  <{ Gamma |-- t \in T }> ->
  t --> t' ->
  <{ Gamma |-- t' \in T }>.
Proof.
Admitted.

End STLC.
