## Coq Makefile生成与编译

要生成Makefile，可以使用以下命令：

```sh
coq_makefile -f _CoqProject *.v -o Makefile
```

```sh
make
```

```sh
make clean
```

```sh
# clean *.aux and *.timing
make cleanall 
```

编译单个文件的方法有两种：

```sh
make <rocq_file>.vo
```

或者直接使用`coqc`命令进行编译：

```sh
coqc -Q . LF <rocq_file>.v
```

---

## Using coqdoc

```sh
coqdoc <source_file>.v -g
```

---

## attributes

```
(** The [update_eq] lemma is used very often in proofs.  Adding it to
    Coq's global "hint database" allows proof-automation tactics such
    as [auto] to find it. *)
#[global] Hint Resolve update_eq : core.
```

---

## Topics

- [`Poly`](#poly)
- [`Functions`](#functions)
  - [`Anonymous Functions`](#anonymous-functions)

## HELP

- `Set Printing Parentheses.` 显示完整括号 (`Unset Printing Parentheses.`)

- `Fail <Command>` 显式表明命令应当error.

在Coq中，可以使用如下命令来获取帮助信息：

- `Check negb`
- `Locate "+"`: 查找符号`+`的定义。
  - `Locate "!->"`.
- `Print "+"`: 显示符号`+`的具体定义内容。
- `Search eqb`: 搜索关于`eqb`的相关信息。
- `Search (_ + _ = _ + _).` 模糊搜索
- `Search (_ + _ = _ + _) inside Induction.`
- `Search (?x + ?y = ?y + ?x).`

---

## Tech

**"Generalizing Statements"**

> 命题变强了, 假设也会变强, 更容易证明

In some situations, it can be necessary to generalize a
    statement in order to prove it by induction.  Intuitively, the
    reason is that a more general statement also yields a more general
    (stronger) inductive hypothesis.  If you find yourself stuck in a
    proof, it may help to step back and see whether you can prove a
    stronger statement.

```coq
Set Printing Parentheses.

Theorem repeat_double_firsttry : forall c n: nat,
  repeat n c ++ repeat n c = repeat n (c + c).
Proof.
  intros c. induction c as [| c' IHc'].
  - (* c = 0 *)
    intros n. simpl. reflexivity.
  - (* c = S c' *)
    intros n. simpl. rewrite <- plus_n_Sm. simpl. rewrite <- IHc'. 
    replace (repeat n c' ++ n :: repeat n c') with (n :: repeat n c' ++ repeat n c'). { reflexivity. }

    (*  Now we seem to be stuck.  The IH cannot be used to
        rewrite [repeat n (c' + S c')]: it only works
        for [repeat n (c' + c')]. If the IH were more liberal here
        (e.g., if it worked for an arbitrary second summand),
        the proof would go through. *)
Abort.

(** To get a more general inductive hypothesis, we can generalize
    the statement as follows: *)

Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof.
  intros c1 c2 n.
  induction c1 as [| c1' IHc1'].
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHc1'.
    reflexivity.
  Qed.
```

## Tactics

• clear H: 删除假设H
• subst x: 如果存在x=e或者e=x的假设，则删除该
假设并把x替换成e
• subst: 对所有变量应用上述策略
• rename... into...: 对变量/假设改名
• assumption: 寻找和目标一样的假设并应用
• contradiction: 寻找和False等价的假设并推出矛盾
• constructor: 寻找一个可以匹配目标的归纳定义
构造函数c，并执行apply c。

- [`clear H`]: Delete hypothesis [H] from the context.

- [`subst x`]: Given a variable [x], find an assumption [x = e] or
[e = x] in the context, replace [x] with [e] throughout the
context and current goal, and clear the assumption.

- [subst]: Substitute away _all_ assumptions of the form [x = e]
or [e = x] (where [x] is a variable).

- [rename... into...]: Change the name of a hypothesis in the
proof context.  For example, if the context includes a variable
named [x], then [rename x into y] will change all occurrences
of [x] to [y].

- [assumption]: Try to find a hypothesis [H] in the context that
exactly matches the goal; if one is found, solve the goal.

- [contradiction]: Try to find a hypothesis [H] in the context
that is logically equivalent to [False].  If one is found,
solve the goal.

- [constructor]: Try to find a constructor [c] (from some
[Inductive] definition in the current environment) that can be
applied to solve the current goal.  If one is found, behave
like [apply c].


下面列出了几种常用的证明战术：

- [`apply`](#apply)
  - 直接应用假设 (exact H.)
  - 应用P->Q形式的假设把结论从Q变成P (会自动替换全称量词)
  - apply策略应用时假设和结论必须能完全匹配
  - 如果定理前提中有自由变量，apply策略会失败, 可以使用apply with指定自由变量的值

- [`assert`](#assert) 
  - [assert (H: e)] (or [assert (e) as H]): introduce a "local lemma" [e] and call it [H]
  - 用于声明一个中间结论以便于证明。

- [`destruct`](#destruct) 
  - pattern matching destruct: `intros [Hn Hm].`
  - `destruct n as [|n'] eqn: H.`：对值`n`进行模式匹配，并将结果命名为`H`。
  - destruct can be used on expressions: `destruct (n =? 3) eqn: H.`
  - [destruct... as...]: case analysis on values of inductively defined types
  - [destruct... eqn:...]: specify the name of an equation to be added to the context, recording the result of the case analysis
  - [destruct (eqb_spec x y) as [Hxy | Hxy].]


- [`discriminate`](#discriminate)  
  - reason by disjointness of constructors on equalities between values of inductively defined types
  - 检查假设或者目标中的构造是否匹配

- [`exact`](#exact)
  匹配结论与假设.

- [`f_equal`](#f_equal)
  - change a goal of the form [f x = f y] into [x = y]
  - Goal: f n1 n2 ... = g m1 m2 ...
  - f_equal
  - Goal: f = g | n1 = m1 | n2 = m2 ...
  - `injection`的逆 

- [`generalize dependent`]
  - first `intros` then re`generalize` to help to proof
  - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula

- [`induction`](#induction) 
  - induction on values of inductively defined types
  - 对归纳类型进行归纳假设。

- [`injection`](#injection)
  - reason by injectivity on equalities between values of inductively defined types
  - 利用某个contructor的injective来简化H `injection H as H'.`

- [`intros`](#intros)
  - 引入自由变量。
  - move hypotheses/variables from goal to context

- [`reflexivity.`](#reflexivity)
  - 若两边相等，则自动完成证明。会自动使用`simpl`, `unfold`
  - finish the proof (when the goal looks like [e = e])

- [`rewrite`](#rewrite) 
  - use an equality hypothesis (or lemma) to rewrite the goal
  - rewrite (<-)(->) H. 可以标识替换方向
  - H应当是一个等式或者P->Q(Q是等式)
  - 匹配结论中出现的结构, 把H的某一边替换为另一边

- [`repeat`](#repeat)

- [`replace`](#replace) 
  可以更精确地替换变量。

- [`simpl.`](#simpl)
  - 尝试简化目标表达式。
  - simplify computations in the goal

- [`specialize`](#specialize)
  (** Note:
    - We can [specialize] facts in the global context, not just
      local hypotheses.
    - The [as...] clause at the end tells [specialize] how to name
      the new hypothesis in this case. *)

- [`symmetry`](#symmetry)
  - changes a goal of the form [t=u] into [u=t]
  - symmetry策略用于交换目标等式的左右两边

- [`transitivity`](#transitivity)
  - [transitivity y]: prove a goal [x=z] by proving two new subgoals, [x=y] and [y=z]

- [`try`](#try)
  - [try reflexivity.]: try some tactics.

- [`unfold`](#unfold)
  - replace a defined constant by its right-hand side in the goal
  - 用于展开定义。

### Logic tactics

- [`split`]
  - To prove a conjunction, use the [split] tactic.  This will generate two subgoals, one for each part of the statement

- [`left`][`right`]
  - To prove a disjunction, it suffices to show that one of its sides holds.

- [`destruct`](#destruct)
  - When conjunction appears in H, then `destruct H as [Hl Hr]`.
  - When disjunction appears in H, then `destruct H as [Hl | Hr]`. It will generate two subgoals.
  - Use `intros [Hl Hr]` or `intros [Hl | Hr]` can
  implicitly apply `destruct`

- [`destruct (H: False)`] Since [False] is a contradictory proposition, the principle of explosion also applies to it. If we can get [False] into the context, we can use [destruct] on it to complete any goal

example: 
```coq
  Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. destruct HP.  Qed.
```

---

## Ideas

如果你熟悉Coq，你可能能够在脑海中一步步走过这些策略，并想象每一步的状态和目标栈的情况。但如果证明更加复杂一些，这样做几乎是不可能的。这说明了对于更复杂的证明，仅靠手动跟踪每一步是不够的，还需要其他方法或工具来辅助理解和管理证明过程。

---

## Poly

**Summary of Knowledge Points:**

1. **Polymorphism:**
   - Polymorphism allows functions to abstract over data types, enabling code reuse across different types.
   - Polymorphic lists are defined using `Inductive list (X:Type) : Type := nil | cons (x : X) (l : list X)`, which generalizes lists to any element type.
   - Type inference reduces the need for explicit type annotations (e.g., `repeat' X x count` infers types from usage).
   - Implicit arguments (using `Arguments` or curly braces in definitions) allow omitting type parameters (e.g., `nil` instead of `nil nat`).
   - Notation (e.g., `x :: y`, `[ ]`, `[x; y; z]`) simplifies list expressions.

2. **Polymorphic Pairs (Products):**
   - Defined as `Inductive prod (X Y : Type) : Type := pair (x : X) (y : Y)`.
   - Notation `(x, y)` for pairs and `X * Y` for product types.
   - Projection functions `fst` and `snd` extract components.
   - `combine` (zip) and `split` (unzip) functions transform between lists of pairs and pairs of lists.

3. **Polymorphic Options:**
   - Defined as `Inductive option (X:Type) : Type := Some (x : X) | None`.
   - Used for partial functions (e.g., `nth_error` and `hd_error` return `Some value` or `None`).

4. **Higher-Order Functions:**
   - Functions can take other functions as arguments or return them (e.g., `doit3times` applies a function three times).
   - `filter` selects list elements satisfying a predicate.
   - Anonymous functions (`fun x => ...`) allow inline function definitions without naming.
   - `map` applies a function to every element of a list.
   - `fold` reduces a list to a value using a binary function and initial accumulator.

5. **Functions as Data:**
   - Partial application (e.g., `plus3 := plus 3`) creates new functions by fixing some arguments.
   - Currying (`prod_curry`) converts a function taking a pair into a chain of single-argument functions, while uncurrying (`prod_uncurry`) does the reverse.

6. **Advanced Topics:**
   - Church numerals represent natural numbers as functions (`cnat := forall X, (X->X)->X->X`), with operations like `scc` (successor), `plus`, `mult`, and `exp` defined functionally.

**Key Concepts:**
- Polymorphism and higher-order functions enable generic and reusable code.
- Implicit arguments and type inference reduce syntactic overhead.
- Functions are first-class citizens, supporting powerful abstractions like mapping, filtering, and folding.
- Notation and implicit arguments improve readability.

## functions

### Anonymous Functions

```coq
Definition doit3times {X : Type} (f : X->X) (x : X) : X :=
  f (f (f x)).

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.
```

### function as results

```coq
Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Theorem ftrue_always_true: forall (n: nat),
  ftrue n = true.
Proof.
  intros. unfold ftrue. unfold constfun. reflexivity.
Qed.

Theorem constfun_always_const: forall {X: Type} (x: X) (n: nat),
  (constfun x) n = x.
Proof.
  intros. unfold constfun. reflexivity.
Qed.
```

`Check plus : nat -> nat -> nat.`

(** Each [->] in this expression is actually a _binary_ operator
    on types.  This operator is _right-associative_, so the type of
    [plus] is really a shorthand for [nat -> (nat -> nat)] -- i.e., it
    can be read as saying that "[plus] is a one-argument function that
    takes a [nat] and returns a one-argument function that takes
    another [nat] and returns a [nat]."  In the examples above, we
    have always applied [plus] to both of its arguments at once, but
    if we like we can supply just the first.  This is called _partial
    application_. *)

## tactics details

### apply

- [apply]: prove goal using a hypothesis, lemma, or constructor

- [apply... in H]: apply a hypothesis, lemma, or constructor to
  a hypothesis in the context (forward reasoning)

- [apply... with...]: explicitly specify values for variables
  that cannot be determined by pattern matching

```coq
(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved.

    [apply] also works with _conditional_ hypotheses: *)

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.
```

```coq
Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.
```

```coq
Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.

  (** Here we cannot use [apply] directly... *)

  Fail apply H.

  (** but we can use the [symmetry] tactic, which switches the left
      and right sides of an equality in the goal. *)

  symmetry. apply H.  Qed.
```



### exact

### injection

```coq
Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.

(** By writing [injection H as Hmn] at this point, we are asking Coq
    to generate all equations that it can infer from [H] using the
    injectivity of constructors (in the present example, the equation
    [n = m]). Each such equation is added as a hypothesis (called
    [Hmn] in this case) into the context. *)

  injection H as Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.
```

### destruct

#### pattern match

```coq
Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
```

#### destruct on natlist

```coq
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Theorem add_inc_count : forall (n: nat) (s: bag),
  count n (add n s) = count n s + 1.
Proof.
  intros.
  destruct s as [|n l'].
  - simpl. rewrite eqb_refl. reflexivity.
  - simpl. rewrite eqb_refl. reflexivity.
Qed.
```

#### destruct on expressions

```coq
Goal:----------------------
match v =? n with
| true => S (count v (sum s1 s2))
| false => count v (sum s1 s2)
end =
(match v =? n with
| true => S (count v s1)
| false => count v s1
end + (count v s2))

We can use `destruct (v =? n)` to solve.
```

#### destruct with String.eqb_spec

destruct (eqb_spec x y) as [Hxy | Hxy].

### discriminiate

The [discriminate] tactic embodies this principle: It is used
    on a hypothesis involving an equality between different
    constructors (e.g., [false = true]), and it solves the current
    goal immediately.

```coq
X : Type
x : X
l : list X
H : S (length l) = 0
IHl : length l = 0 -> nth_error l 0 =
None
(1 / 1)

discriminate H.
```

### intros

### induction

```coq
induction n as [|n' IHn'].
(* 
- Goal: P(0)
- n': nat
  IHn': P(n')
  Goal: P(S n')
*)
```

#### induction on List

证明关于数据类型（如[natlist]）的归纳是一种比标准自然数归纳稍微不那么熟悉的技巧，但其理念同样简单。每个[Inductive]声明都定义了一组可以用所声明的构造函数构建的数据值。例如，布尔值可以是[true]或[false];数字可以是[O]或者是[S]应用于另一个数字；列表可以是[nil]或者是[cons]应用于某个数字和其他列表。此外，对声明的构造函数的应用彼此之间是构成这类归纳定义集元素的唯一可能形状。

这一事实直接引出了一种关于归纳定义集推理的方法：一个数字要么是[O]，要么是[S]应用于某个“较小”的数字;

---

**列表要么是[nil]，要么是[cons]应用于某个数字和某个“较小”的列表**

- 首先，证明[l]为[nil]时[P]成立。

- 然后，证明当[l]为[cons n l']时，其中[n]是一个数字且[l']是一个较小的列表，在假设[P]对[l']成立的情况下，[P]对[l]也成立。

```coq
(* right associtivity *)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

```
(* Notice that, as we saw with induction on natural numbers,
    the [as...] clause provided to the [induction] tactic gives a name
    to the induction hypothesis corresponding to the smaller list
    [l1'] in the [cons] case. *)


### assert

```coq
Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.
```


### reflexivity

reflexivity 会自动尝试 simpl 和 unfold

### rewrite

使用`rewrite`时，例如：

```coq
rewrite -> negb_involutive.
```

该战术利用了$\text{negb}$函数的自反性，即对于任意布尔值$b$，有$ \text{negb} (\text{negb} b) = b $。

然而，[rewrite]战术在应用重写的地方并不总是很智能。

这里有三个加法运算符`+`，执行`rewrite -> add_comm`会影响最外层的那个...

如果假设具有形式[H: P -> a = b]，那么`rewrite H`将在目标中把`a`重写为`b`，并将`P`作为一个新子目标添加。可以在练习的归纳步骤中使用这个特性。

### replace

[replace]战术允许您指定要重写的特定子项以及希望将其重写成的内容：`replace (t) with (u)`将表达式[t]在目标中的所有副本替换为表达式[u]，并生成[t = u]作为额外的子目标。当简单的`rewrite`作用于错误的目标部分时，这通常很有用。

使用`replace`战术来进行`add_shuffle3'`的证明，就像`add_shuffle3`但无需使用`assert`。

```coq
(* 示例代码 *)
```

### simpl

### specialize

```coq
(** * Specializing Hypotheses *)

(** Another handy tactic for fiddling with"摆弄, 调试" hypotheses is [specialize].
    It is essentially just a combination of [assert] and [apply], but
    it often provides a pleasingly smooth way to nail down overly
    general assumptions.  It works like this:

    If [H] is a quantified hypothesis in the current context -- i.e.,
    [H : forall (x:T), P] -- then [specialize H with (x := e)] will
    change [H] so that it looks like [[x:=e]P], that is, [P] with [x]
    replaced by [e].

    For example: *)

Theorem specialize_example: forall n,
     (forall m, m*n = 0)
  -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  simpl in H.
  rewrite add_comm in H.
  simpl in H.
  apply H. Qed.
```

### transitivity

```coq
Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2.   Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  transitivity m.
  exact H0.
  exact H.
Qed.
```

### unfold

```coq
Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
  unfold countoddmembers.
  simpl.
  reflexivity.
Qed.
```

We can unfold multiple definitions once a time.

```coq
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  unfold prod_uncurry, prod_curry.
  simpl.
  reflexivity.
Qed.
```

[Click Here to go Back to All Tactics](#tactics)

### try

```coq
Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* [destruct] the current goal *)
  destruct n;
  (* then [simpl] each resulting subgoal *)
  simpl;
  (* and do [reflexivity] on each resulting subgoal *)
  reflexivity.
Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.
```

[Click Here to go Back to All Tactics](#tactics)

### repeat

```coq
Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  simpl.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.
```

[Click Here to go Back to All Tactics](#tactics)