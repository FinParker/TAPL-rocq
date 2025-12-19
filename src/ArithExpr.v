(** * ArithExpr: The Typed Calculus of Booleans and Numbers *)
(* Left Some Theorems not proved *)

(** The system studied in this chapter is the typed calculus of booleans 
    and numbers. The corresponding OCaml implementation is `tyarith`. 
    
    This is the simplest typed language we'll study: it has no functions
    and no variables, but it does have types and type checking.
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import List Strings.String.
Import ListNotations.
From TAPL Require Import Tactics RelationProp.

Module TypedArithExpr.

(* ================================================================= *)
(** ** Types *)

(** The types of this calculus are [Bool] and [Nat]. *)

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Nat : ty.

(** Some examples of types: *)

Example example_ty1 := Ty_Bool.
Example example_ty2 := Ty_Nat.

(* ================================================================= *)
(** ** Terms *)

(** The syntax of arithmetic expressions: *)

Inductive tm : Type :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_iszero : tm -> tm.

(** Some examples of terms: *)

Example example_tm1 := tm_if tm_true tm_false tm_true.
Example example_tm2 := tm_succ (tm_succ tm_zero).
Example example_tm3 := tm_iszero (tm_pred (tm_succ tm_zero)).

(* ================================================================= *)
(** ** Values *)

(** A value is a term that has finished evaluating. In this language,
    the values are:
    - boolean constants [true] and [false]
    - numeric values (0 or a number built from 0 with [succ])
*)

(** Boolean values *)
Inductive bv: tm -> Prop :=
  | bv_true: bv tm_true
  | bv_false: bv tm_false.

(** Numeric values (natural numbers) *)
Inductive nv: tm -> Prop :=
  | nv_zero: nv tm_zero
  | nv_succ: forall t, nv t -> nv (tm_succ t).

(** All values *)
Inductive value: tm -> Prop :=
  | v_bv: forall t, bv t -> value t
  | v_nv: forall t, nv t -> value t.

Hint Constructors bv nv value : core.

(* ================================================================= *)
(** ** Small-step Operational Semantics *)

(** We define the small-step evaluation relation. The evaluation is
    deterministic and can either reduce to a value or get stuck. For
    example, [pred false] gets stuck because there's no evaluation
    rule for it. *)

(* ================================================================= *)
(** ** Small-step semantics *)
Reserved Notation "e '-->' n" (at level 90, left associativity).

(** Evaluation rules: *)
Inductive step : tm -> tm -> Prop :=
  (* If expressions *)
  | E_IfTrue (t2 t3 : tm) :
      tm_if tm_true t2 t3 --> t2
  | E_IfFalse (t2 t3 : tm) :
      tm_if tm_false t2 t3 --> t3
  | E_If (t1 t1' t2 t3 : tm) :
      t1 --> t1' ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
  (* Successor *)
  | E_Succ (t t' : tm) :
      t --> t' ->
      tm_succ t --> tm_succ t'
  (* Predecessor *)
  | E_PredZero :
      tm_pred tm_zero --> tm_zero
  | E_PredSucc (t : tm) :
      nv t ->
      tm_pred (tm_succ t) --> t
  | E_Pred (t t' : tm) :
      t --> t' ->
      tm_pred t --> tm_pred t'
  (* Iszero *)
  | E_IszeroZero :
      tm_iszero tm_zero --> tm_true
  | E_IszeroSucc (t : tm) :
      nv t ->
      tm_iszero (tm_succ t) --> tm_false
  | E_Iszero (t t' : tm) :
      t --> t' ->
      tm_iszero t --> tm_iszero t'

where "e '-->' n" := (step e n) : type_scope.

Hint Constructors step : core.

(* ================================================================= *)
(** ** Properties of Evaluation *)

(** Values do not step. *)
Lemma bvalue_is_normal_form : forall t,
  bv t -> normal_form step t.
Proof.
  intros t Hbv. unfold normal_form.
  induction Hbv.
  - (* bv_true *) intros [t' Hstep]. inv Hstep.
  - (* bv_false *) intros [t' Hstep]. inv Hstep.
Qed.

(** Natural number values do not step. *)
Lemma nvalue_is_normal_form : forall t,
  nv t -> normal_form step t.
Proof.
  intros t Hnv. unfold normal_form.
  induction Hnv.
  - (* nv_zero *) intros [t' Hstep]. inv Hstep.
  - (* nv_succ *) intros [t' Hstep]. inv Hstep.
    + apply IHHnv. exists t'0. exact H0.
    (* solve_exists_contradiction *)
Qed.

(** All values are normal forms. *)
Lemma value_is_normal_form : forall t,
  value t -> normal_form step t.
Proof.
  intros t Hval. unfold normal_form.
  destruct Hval as [t Hbv | t Hnv].
  - apply bvalue_is_normal_form. exact Hbv.
  - apply nvalue_is_normal_form. exact Hnv.
Qed.

(** Evaluation is deterministic: if a term can step to two different terms,
    they must be the same. *)
Theorem step_deterministic : deterministic step.
Proof with auto.
  unfold deterministic.
  intros t t1 t2 Hstep1 Hstep2.
  generalize dependent t2.
  induction Hstep1; intros t_ Hstep_; inv Hstep_; try (solve_by_invert)...
  - (* E_If *)
    f_equal. apply IHHstep1. exact H3.
  - (* E_Succ *)
    f_equal. apply IHHstep1. exact H0.
  - (* E_Pred *)
    inv H1. apply nvalue_is_normal_form in H. unfold normal_form in H. solve_exists_contradiction.
  - (* E_Iszero *)
    inv Hstep1. apply nvalue_is_normal_form in H0. unfold normal_form in H0. solve_exists_contradiction.
  - (* E_Iszero *)
    f_equal. apply IHHstep1. exact H0.
  - (* E_Iszero *)
    inv H1. apply nvalue_is_normal_form in H. unfold normal_form in H. solve_exists_contradiction.
  - (* E_Iszero *)
    inv Hstep1. apply nvalue_is_normal_form in H0. unfold normal_form in H0. solve_exists_contradiction.
  - (* E_Iszero *)
    f_equal. apply IHHstep1. exact H0.
Qed.
(* ================================================================= *)
(** ** Multi-step Evaluation *)

(* ================================================================= *)
(** ** Multi-step Evaluation *)

(** The reflexive-transitive closure of [step] *)
Notation "t '-->*' t'" := (multi step t t') (at level 40).

(** Example: multiple evaluation steps *)
Example test_multi_step :
  tm_if (tm_if tm_true tm_false tm_true) tm_true tm_false -->* tm_false.
Proof.
  apply multi_step with (y := tm_if tm_false tm_true tm_false).
  - apply E_If. apply E_IfTrue.
  - apply multi_step with (y := tm_false).
    + apply E_IfFalse.
    + apply multi_refl.
Qed.

(** Another example *)
Example test_multi_step2 :
  tm_succ (tm_succ tm_zero) -->* tm_succ (tm_succ tm_zero).
Proof.
  apply multi_refl.
Qed.

(* ================================================================= *)
(** ** Big-step Evaluation *)

(** An alternative to small-step evaluation is big-step or natural
    semantics. In big-step evaluation, we define what it means for a
    term to evaluate to a final value directly, without necessarily
    going through intermediate steps.
*)

Reserved Notation "t '==>' v" (at level 90, left associativity).

(** Big-step evaluation rules: *)
Inductive eval : tm -> tm -> Prop :=
  (* A value evaluates to itself *)
  | B_Value (v : tm) :
      value v ->
      v ==> v
  (* If-then-else with true condition *)
  | B_IfTrue (t1 t2 t3 v : tm) :
      t1 ==> tm_true ->
      t2 ==> v ->
      tm_if t1 t2 t3 ==> v
  (* If-then-else with false condition *)
  | B_IfFalse (t1 t2 t3 v : tm) :
      t1 ==> tm_false ->
      t3 ==> v ->
      tm_if t1 t2 t3 ==> v
  (* Successor of a value *)
  | B_Succ (t v : tm) :
      t ==> v ->
      nv v ->
      tm_succ t ==> tm_succ v
  (* Predecessor: zero case *)
  | B_PredZero (t : tm) :
      t ==> tm_zero ->
      tm_pred t ==> tm_zero
  (* Predecessor: successor case *)
  | B_PredSucc (t v : tm) :
      t ==> tm_succ v ->
      nv v ->
      tm_pred t ==> v
  (* Iszero: zero case *)
  | B_IszeroZero (t : tm) :
      t ==> tm_zero ->
      tm_iszero t ==> tm_true
  (* Iszero: successor case *)
  | B_IszeroSucc (t v : tm) :
      t ==> tm_succ v ->
      nv v ->
      tm_iszero t ==> tm_false

where "t '==>' v" := (eval t v) : type_scope.

Hint Constructors eval : core.

(* ================================================================= *)
(** ** Relationship between Big-step and Small-step *)

(** Small-step evaluation reaches a value if and only if big-step evaluation
    produces that value. *)

Lemma eval_one_step: forall x y z,
  value z ->
  x --> y ->
  y ==> z ->
  x ==> z.
Proof with auto.
  intros x y z Hval Hstep Heval.
  generalize dependent z.
  induction Hstep; intros z Hval Heval; (try solve_by_invert)...


Lemma eval_from_steps : forall t v,
  t -->* v ->
  value v ->
  t ==> v.
Proof with auto.
  intros t v Hmulti Hval.
  induction Hmulti.
  - (* multi_refl *)
    apply B_Value. exact Hval.
  - (* multi_step *)
    apply IHHmulti in Hval.
    

Admitted.

Theorem eval_iff_steps : forall t v,
  value v ->
  (t ==> v) <-> (t -->* v).
Proof.

Admitted.

Lemma nf_multi_step: forall t v,
  normal_form step t ->
  t -->* v ->
  t = v.
Proof.
Admitted.

(* ================================================================= *)
(** ** Type Checking *)

(** Now we add typing to this language. *)
Declare Custom Entry arith_tm.
Declare Custom Entry arith_ty.

Notation "<{ e }>" := e (e custom arith_tm at level 200) : type_scope.
Notation "t" := t (in custom arith_tm at level 0, t constr) : type_scope.
Notation "T" := T (in custom arith_ty at level 0, T constr) : type_scope.

Notation "'Bool'" := Ty_Bool (in custom arith_ty at level 0) : type_scope.
Notation "'Nat'"  := Ty_Nat (in custom arith_ty at level 0) : type_scope.

(* Conservative Typing Rules*)
(** Typing rules:
    - [true] and [false] have type [Ty_Bool]
    - [if] expressions have type [T] if condition is [Ty_Bool]
      and both branches have type [T]
    - [zero] has type [Ty_Nat]
    - [succ] and [pred] work on [Ty_Nat]
    - [iszero] produces [Ty_Bool]
*)

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
      has_type tm_true Ty_Bool
  | T_False :
      has_type tm_false Ty_Bool
  | T_If (t1 t2 t3 : tm) (T : ty) :
      has_type t1 Ty_Bool ->
      has_type t2 T ->
      has_type t3 T ->
      has_type (tm_if t1 t2 t3) T
  | T_Zero :
      has_type tm_zero Ty_Nat
  | T_Succ (t : tm) :
      has_type t Ty_Nat ->
      has_type (tm_succ t) Ty_Nat
  | T_Pred (t : tm) :
      has_type t Ty_Nat ->
      has_type (tm_pred t) Ty_Nat
  | T_Iszero (t : tm) :
      has_type t Ty_Nat ->
      has_type (tm_iszero t) Ty_Bool.

Notation "t '\in' T" := (has_type t T) 
  (in custom arith_tm at level 100, t custom arith_tm, T custom arith_ty) : type_scope.

Hint Constructors has_type : core.

(* Check <{ tm_true \in Bool }>. *)

(* Deterministic of has_type *)
(* if <{t \in T1}> /\ <{t \in T2}> then T1 = T2 *)
(* Each term t has at most one type. That is, if t is typable, then its type is unique. *)
Theorem has_type_deterministic:
  deterministic has_type.
Proof.
  unfold deterministic.
  intros t T1 T2 H1 H2.
  generalize dependent T2.
  induction H1; intros T2 H2; inv H2; try reflexivity.
  - (* T_If *)
    apply IHhas_type2. exact H5.
Qed.

(* ================================================================= *)
(** ** Type Safety: Type Preservation and Progress *)

(** Type preservation: if a well-typed term takes a step, the result is also well-typed with the same type. *)

(* In most of the type systems we will consider, evaluation preserves not only well-typedness but the exact types of terms. In some systems, however, types can change during evaluation. For example, in systems with subtyping (Chapter 15), types can become smaller (more informative) during evaluation. *)
(* Subject Reduction*)
Theorem preservation : forall t t' T,
  <{ t \in T }> ->
  t --> t' ->
  <{ t' \in T }>.
Proof.
  intros t t' T HT Hstep.
  generalize dependent T.
  induction Hstep; intros T HT; inv HT.
  - (* E_IfTrue *) exact H4.
  - (* E_IfFalse *) exact H5.
  - (* E_If *) apply T_If.
    + exact (IHHstep _ H2).
    + exact H4.
    + exact H5.
  - (* E_Succ *) apply T_Succ. apply IHHstep. assumption. 
  - (* E_PredZero *) apply T_Zero.
  - (* E_PredSucc *) inv H1. assumption.
  - (* E_Pred *) apply T_Pred. apply IHHstep. assumption.
  - (* E_IszeroZero *) apply T_True.
  - (* E_IszeroSucc *) apply T_False.
  - (* E_Iszero *) apply T_Iszero. apply IHHstep. assumption.
Qed.

(* Lemma [Canonical Forms]: 
1. If v is a value of type Bool, then v is either true or false.  
2. If v is a value of type Nat, then v is a numeric value *)

Lemma canonical_forms_bool : forall v,
  <{ v \in Bool }> ->
  value v ->
  bv v.
Proof.
  intros v HT Hval.
  inv Hval.
  - (* v_bv *) exact H.
  - (* v_nv *) inv HT; inv H.
Qed.

Lemma canonical_forms_nat : forall v,
  <{ v \in Nat }> ->
  value v ->
  nv v.
Proof.
  intros v HT Hval.
  inv Hval.
  - (* v_bv *) inv HT; inv H.
  - (* v_nv *) exact H.
Qed.

(** Progress: every well-typed term either is a value or can take a step. *)

(* proof version with auto *)
Theorem progress_auto : forall t T,
  <{t \in T}> ->
  value t \/ exists t', t --> t'.
Proof with auto.
  intros t T HT.
  induction HT...
  - (* T_If *)
    destruct IHHT1 as [Hval | [t1' Hstep]].
    + apply canonical_forms_bool in Hval...
      destruct Hval...
        -- right. exists t2...
        -- right. exists t3...
    + right. exists (tm_if t1' t2 t3)...
  - (* T_Succ *)
    destruct IHHT as [Hval | [t' Hstep]]...
    + apply canonical_forms_nat in Hval...
    + right. exists (tm_succ t')... 
  - (* T_Pred *)
    destruct IHHT as [Hval | [t' Hstep]]...
    + apply canonical_forms_nat in Hval...
      * destruct Hval...
        -- right. exists tm_zero... 
        -- right. exists t... 
    + right. exists (tm_pred t')... 
  - (* T_Iszero *)
    destruct IHHT as [Hval | [t' Hstep]]...
    + apply canonical_forms_nat in Hval...
      * destruct Hval...
        -- right. exists tm_true... 
        -- right. exists tm_false... 
    + right. exists (tm_iszero t')...
Qed.

(* full proof version *)
Theorem progress : forall t T,
  <{t \in T}> ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T HT.
  induction HT.
  - (* T_True *) 
    left. apply v_bv. apply bv_true.
  - (* T_False *) 
    left. apply v_bv. apply bv_false.
  - (* T_If *)
    right. destruct IHHT1 as [Hval | [t1' Hstep]].
    (* t1 is value *)
    + apply canonical_forms_bool in Hval.
      * destruct Hval.
        -- exists t2. apply E_IfTrue.
        -- exists t3. apply E_IfFalse.
      * exact HT1.  
    (* t1 can step *)
    + exists (tm_if t1' t2 t3). apply E_If. exact Hstep.
  - (* T_Zero *) 
    left. apply v_nv. apply nv_zero.
  - (* T_Succ *)
    destruct IHHT as [Hval | [t' Hstep]].
    (* t1 is value *)
    + apply canonical_forms_nat in Hval.
      * destruct Hval.
        -- left. apply v_nv. apply nv_succ. apply nv_zero.
        -- left. apply v_nv. apply nv_succ. apply nv_succ. exact Hval.
      * exact HT.
    (* t1 can step *)
    + right. exists (tm_succ t'). apply E_Succ. exact Hstep.
  - (* T_Pred *)
    destruct IHHT as [Hval | [t' Hstep]].
    (* t1 is value *)
    + apply canonical_forms_nat in Hval.
      * destruct Hval.
        -- right. exists tm_zero. apply E_PredZero.
        -- right. exists t. apply E_PredSucc. exact Hval.
      * exact HT.
    (* t1 can step *)
    + right. exists (tm_pred t'). apply E_Pred. exact Hstep.
  - (* T_Iszero *)
    destruct IHHT as [Hval | [t' Hstep]].
    (* t1 is value *)
    + apply canonical_forms_nat in Hval.
      * destruct Hval.
        -- right. exists tm_true. apply E_IszeroZero.
        -- right. exists tm_false. apply E_IszeroSucc. exact Hval.
      * exact HT.
    (* t1 can step *)
    + right. exists (tm_iszero t'). apply E_Iszero. exact Hstep.
Qed.

End TypedArithExpr.