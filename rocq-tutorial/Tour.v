From Stdlib Require Import Arith String.
(* A Tour of Rocq *)

(* The Rocq Prover is an interactive theorem prover. It means that it is designed to develop mathematical proofs, and especially to write formal specifications, programs and proofs that programs comply to their specifications. An interesting additional feature of Rocq is that it can automatically extract executable programs from specifications, as either OCaml or Haskell source code. *)

(* Properties, programs and proofs are formalized in the same language called the Calculus of Inductive Constructions (CIC). Then, all logical judgments in Rocq are typing judgments: the very heart of Rocq is in fact a type-checking algorithm.
The language of Rocq *)

(* Rocq objects are sorted into three categories: "the Prop sort, the SProp sort and the Type sort": *)

(* Prop is the sort for propositions, i.e. well-formed propositions are of type Prop. Typical propositions are: *)

(* ∀ A B : Prop, A /\ B -> B \/ B *)
Example begin_1:
  forall A B : Prop, A /\ B -> B \/ B.
Proof.
  intros A B H.
  destruct H.
  - left. exact H0.
Qed.

(* ∀ x y : nat, x * y = 0 -> x = 0 \/ y = 0 *)
Example begin_2:
  forall x y : nat, x * y = 0 -> x = 0 \/ y = 0.
Proof.
  intros x y H.
  destruct x.
  - left. reflexivity.
  - right. destruct y.
    + reflexivity.
    + discriminate H.
Qed.

(* and new predicates can be defined either inductively, e.g.: *)

Module EvenOdd.
Inductive even : nat -> Prop :=
| even_0 : even 0
| even_S n : odd n -> even (n + 1)
with odd : nat -> Prop :=
| odd_S n : even n -> odd (n + 1).
End EvenOdd.

(* or by abstracting over other existing propositions, e.g.: *)

Definition divide (x y: nat) := exists z, x * z = y.
Definition prime x := forall y, divide y x -> y = 1 \/ y = x.

(* Type is the sort for datatypes and mathematical structures, i.e. well-formed types or structures are of type Type. Here is e.g. a basic example of type: Z -> Z * Z *)

(* Types can be inductive structures, e.g.: *)

Module Monoid.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Inductive list (A:Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

(* or types for tuples, e.g.: *)

Structure monoid := { 
  dom : Type ; 
  op : dom -> dom -> dom where "x * y" := (op x y); 
  id : dom where "1" := id; 
  assoc : forall x y z, x * (y * z) = (x * y) * z ; 
  left_neutral : forall x, 1 * x = x ;
  right_neutral : forall x, x * 1 = x 
}.

End Monoid.

(* or a form of subset types called Σ-types, e.g. the type of even natural numbers: *)

Inductive even : nat -> Prop :=
| even_O : even 0
| even_SS : forall n, even n -> even (S (S n)).

Check {n : nat | even n}.

(* 定义提取函数 *)
Definition get_value (p : {n : nat | even n}) : nat :=
  proj1_sig p.

Definition get_proof (p : {n : nat | even n}) : even (get_value p) :=
  proj2_sig p.

(* 创建一些具体的偶数实例 *)

(* 0 是偶数 *)
Example zero_even : {n : nat | even n} :=
  exist _ 0 even_O.

(* 2 是偶数 *)
Example two_even : {n : nat | even n} :=
  exist _ 2 (even_SS 0 even_O).

(* 4 是偶数 *)
Example four_even : {n : nat | even n} :=
  exist _ 4 (even_SS 2 (even_SS 0 even_O)).

(* 现在让我们使用这些函数 *)

(* 测试 get_value *)
Compute get_value zero_even.   (* = 0 *)
Compute get_value two_even.    (* = 2 *) 
Compute get_value four_even.   (* = 4 *)

(* 测试 get_proof - 注意我们不能直接 Compute 证明，但可以检查类型 *)
Check get_proof zero_even.   (* : even (get_value zero_even) *)
Check get_proof two_even.    (* : even (get_value two_even) *)
Check get_proof four_even.   (* : even (get_value four_even) *)

(* 由于 get_value zero_even 计算为 0，get_proof zero_even 的类型就是 even 0 *)
Lemma zero_proof_type : even 0.
Proof. exact (get_proof zero_even). Qed.

(* 实际应用示例：安全的偶数运算 *)
(* 注意：我们需要先证明 even_plus 定理 *)
Lemma even_plus : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [|n' Hn' IH].
  - simpl. apply Hm.                    (* 0 + m = m *)
  - simpl. apply even_SS.              (* S (S n') + m = S (S (n' + m)) *)
    apply IH.
Qed.

(* 安全的偶数加法：结果仍然是偶数 *)
Definition even_add (p1 p2 : {n : nat | even n}) : {n : nat | even n} :=
  let n1 := get_value p1 in
  let n2 := get_value p2 in
  let sum := n1 + n2 in
  let proof1 := get_proof p1 in
  let proof2 := get_proof p2 in
  (* 我们需要证明两个偶数的和是偶数 *)
  exist _ sum (even_plus n1 n2 proof1 proof2).

(* 现在使用 even_add *)
Example add_example : {n : nat | even n} :=
  even_add two_even four_even.

Compute get_value add_example.  (* = 6 *)

(* 另一个例子：提取信息用于证明 *)

Lemma example_usage : exists n, even n.
Proof.
  (* 我们可以使用 Sigma 类型中的值作为存在证明 *)
  exists (get_value two_even).
  exact (get_proof two_even).
Qed.

(* 更复杂的例子：模式匹配处理 Sigma 类型 *)

Definition is_zero_even (p : {n : nat | even n}) : bool :=
  match p with
  | exist _ 0 _ => true
  | exist _ _ _ => false
  end.

Compute is_zero_even zero_even.  (* = true *)
Compute is_zero_even two_even.   (* = false *)

(* 提取特定信息 *)
Open Scope string_scope.
Definition get_even_number_details (p : {n : nat | even n}) : nat * string :=
  let n := get_value p in
  let proof := get_proof p in
  (n, "this number is even").

(* Rocq implements a functional programming language supporting these types. For instance, the pairing function of type Z -> Z * Z is written fun x => (x,x) and cons (S (S O)) (cons (S O) nil) (shortened to 2::1::nil in Rocq) denotes a list of type list nat made of the two elements 2 and 1. Using Σ-types, a sorting function over lists of natural numbers can be given the type: *)


(* sort : ∀ (l : list nat), {l' : list nat | sorted l' /\ same_elements l l'} *)

(* Such a type (specification) enforces the user to write the proofs of predicates sorted l' and same_elements l l' when writing a implementation for the function sort. *)

(* Then, functions over inductive types are expressed using a case analysis: *)

Fixpoint plus (n m:nat) {struct n} : nat :=
match n with
| O => m
| S p => S (plus p m)
end.

(* The Rocq Prover can now be used as an interactive evaluator. Issuing the command *)

Eval compute in (plus 43 55).
Compute (plus 43 55).

(* (where 43 and 55 denote the natural numbers with respectively 43 and 55 successors) returns *)

(* 98 : nat *)

(* Proving in Rocq *)

(* Proof development in Rocq is done through a language of tactics that allows a user-guided proof process. At the end, the curious user can check that tactics build lambda-terms. For example the tactic intro n, where n is of type nat, builds the term (with a hole): *)

(* fun (n:nat) => _  *)

(* where _ represents a term that will be constructed after, using other tactics. *)

(* Here is an example of a proof in the Rocq Prover: *)

Inductive seq : nat -> Set :=
| niln : seq 0
| consn : forall n : nat, nat -> seq n -> seq (S n).

(* 空列表 *)
Example empty : seq 0 := niln.

(* 单元素列表 [5] *)
Example single : seq 1 := 
  consn 0 5 niln.

(* 两元素列表 [3, 7] *)  
Example two_elem : seq 2 :=
  consn 1 3 (consn 0 7 niln).

(* 三元素列表 [1, 2, 3] *)
Example three_elem : seq 3 :=
  consn 2 1 (consn 1 2 (consn 0 3 niln)).

Fixpoint length (n : nat) (s : seq n) {struct s} : nat :=
match s with
| niln => 0
| consn i _ s' => S (length i s')
end.

Theorem length_corr : forall (n : nat) (s : seq n), length n s = n.
Proof.
intros n s.

(* reasoning by induction over s. Then, we have two new goals
  corresponding on the case analysis about s (either it is
  niln or some consn *)
induction s.

(* We are in the case where s is void. We can reduce the
    term: length 0 niln *)
simpl.

(* We obtain the goal 0 = 0. *)
trivial.

(* now, we treat the case s = consn n e s with induction
    hypothesis IHs *)
simpl.

(* The induction hypothesis has type length n s = n.
    So we can use it to perform some rewriting in the goal: *)
rewrite IHs.

(* Now the goal is the trivial equality: S n = S n *)
trivial.

(* Now all sub cases are closed, we perform the ultimate
  step: typing the term built using tactics and save it as
  a witness of the theorem. *)
Qed.

(* Using the Print command, the user can look at the proof-term generated using the tactics: *)
Print length_corr.



