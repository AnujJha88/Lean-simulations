# Lean = Functional Programming: The Complete Explainer

> **TL;DR:** Every Lean tactic is a pure function — one input (proof state), one output (new proof state). A proof is just function composition. We simulate this in Python with 14 proofs across Addition, Multiplication, and Inequality worlds from the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4).

---

## Part 1: The Big Idea

Your professor says functional programming is **"one input, one output per function."** Lean's proof system is exactly this:

```
tactic : ProofState → ProofState
```

A proof is a **pipeline** of these functions:

```
proof = rfl ∘ rw ∘ rw ∘ rw ∘ rw ∘ rw ∘ rw ∘ nth_rewrite
```

Eight functions composed. Each takes one goal, returns one goal. That's it.

This works because of the **Curry-Howard Correspondence**:

| Math / Logic | Programming |
|---|---|
| A proposition (statement) | A type |
| A proof | A value of that type |
| A tactic | A function that builds the value |
| QED | The type-checker accepting the program |

When Lean "checks your proof," it's literally type-checking a program. When it says "goals accomplished 🎉", it means the program compiled.

---

## Part 2: Is This Actually How Lean Works?

**Yes.** Our tagged tuples are remarkably close to Lean's actual kernel representation.

### Lean's Internal Expression Type

Lean 4's kernel (written in C++) represents ALL expressions as a recursive data type called `Expr`:

```lean
-- Lean 4 kernel (simplified from lean4/src/kernel/expr.h)
inductive Expr where
  | bvar   : Nat → Expr                  -- bound variable (de Bruijn index)
  | fvar   : FVarId → Expr               -- free variable
  | const  : Name → List Level → Expr    -- named constant like `Nat.add`
  | app    : Expr → Expr → Expr          -- function application
  | lam    : Name → Expr → Expr → Expr   -- lambda abstraction
  | sort   : Level → Expr                -- type universe (Type, Prop, etc.)
  ...
```

**This is exactly a tagged tree** — just like our tuples! When Lean sees `2 + 2 = 4`, it internally stores:

```
Expr.app (Expr.app (Expr.const `Eq _)
  (Expr.app (Expr.app (Expr.const `HAdd.hAdd _)
    (Expr.app (Expr.const `OfNat.ofNat _) (Expr.lit 2)))
    (Expr.app (Expr.const `OfNat.ofNat _) (Expr.lit 2))))
  (Expr.app (Expr.const `OfNat.ofNat _) (Expr.lit 4))
```

That's a tree of tagged nodes — `app`, `const`, `lit` — exactly like our `("eq", ("add", ("two",), ("two",)), ("four",))`.

### What `rw` Actually Does Inside Lean

When you write `rw [add_succ]`, the elaborator:

1. **Looks up** `add_succ` → gets a proof of `∀ a b, a + succ b = succ (a + b)`
2. **Unifies** the LHS pattern `?a + succ ?b` against the goal tree (DFS traversal!)
3. **Finds a match** — assigns `?a := two()`, `?b := one()`
4. **Constructs a new `Expr` tree** with the matched sub-expression replaced
5. **Returns** the modified goal

This is **exactly** what our `apply_first(goal, rule)` does.

### What `rfl` Actually Does

`rfl` calls the kernel's **definitional equality checker** (`is_def_eq` in C++). It walks both `Expr` trees simultaneously, checking that every node matches. This is `==` on nested tuples.

> Our simulation isn't an analogy — it's a faithful model of how Lean's kernel actually works.

---

## Part 3: Data Representation — Tagged Tuples = Algebraic Data Types

In Haskell or Lean, you'd write:

```haskell
data Nat = Zero | Succ Nat
data Expr = Add Nat Nat | Mul Nat Nat | Eq Expr Expr | Le Expr Expr
```

We use **tagged tuples** instead (no classes allowed!):

```python
# Constructors (each is a function: inputs → tuple)
zero()     → ("zero",)                    # 0
succ(n)    → ("succ", n)                  # S(n)  — the successor function
one()      → ("one",)                     # named shorthand for S(0)
two()      → ("two",)                     # named shorthand for S(S(0))
add(a, b)  → ("add", a, b)               # a + b
mul(a, b)  → ("mul", a, b)               # a * b
eq(a, b)   → ("eq", a, b)                # a = b  (equality proposition)
le(a, b)   → ("le", a, b)                # a ≤ b  (inequality proposition)
```

The tag (first element) tells us what kind of node it is. The rest are children.

### Pattern Matching = Destructuring Tuples

```python
def is_succ(t):  return t[0] == "succ"     # check the tag
def pred_of(t):  return t[1]               # extract the child
def is_add(t):   return t[0] == "add"
def left_of(t):  return t[1]               # left child
def right_of(t): return t[2]               # right child
```

This is how functional languages do pattern matching — check the constructor tag, extract fields.

---

## Part 4: Rewrite Rules Are Pattern-Matching Functions

Each rewrite rule is a function `term → term | None`:

### Addition Rules

```python
def add_zero_rule(term):
    """(a + 0) → a"""
    if is_add(term) and is_zero(right_of(term)):
        return left_of(term)           # just return a
    return None                        # no match

def add_succ_rule(term):
    """(a + S(b)) → S(a + b)"""
    if is_add(term) and is_succ(right_of(term)):
        a = left_of(term)              # extract a
        b = pred_of(right_of(term))    # extract b from S(b)
        return succ(add(a, b))         # build S(a + b)
    return None
```

**These ARE the Peano axioms.** Every call to `add_succ_rule` "peels" one `S` off the right operand. You call it as many times as the value of the right operand.

### Multiplication Rules

```python
def mul_succ_rule(term):
    """(a * S(b)) → (a * b) + a"""
    if is_mul(term) and is_succ(right_of(term)):
        a = left_of(term)
        b = pred_of(right_of(term))
        return add(mul(a, b), a)       # mul becomes add!
    return None
```

**Key insight:** `mul_succ` REDUCES multiplication to addition.

---

## Part 5: Tactics Are Higher-Order Functions

### `rw` — Takes a function, returns a function

```python
def rw(rule, name):                # input: a rewrite rule (function)
    def tactic(goal):              # output: a tactic (also a function!)
        return apply_first(goal, rule)  # DFS traversal + pattern match
    tactic._lean = f"rw [{name}]"
    return tactic                  # ← this is a CLOSURE
```

`rw(add_succ_rule, "add_succ")` returns a **new function** that DFS-traverses the goal tree, finds the first matching sub-expression, and replaces it.

**This is a higher-order function** — takes a function, returns a function. The returned function is a **closure** — it captures `rule` and `name` from the enclosing scope.

### `nth_rewrite` — Skips to the Nth match

Why needed? `rw` always hits the FIRST DFS match. In `(2 + 2) = 4`, the first `("two",)` is the LEFT operand. To target the RIGHT one, use `nth_rewrite 2`.

### `use` — The Existential Witness Provider

```python
def use(witness, name):
    """NNG4: a ≤ b  :=  ∃ c, b = a + c
    `use c` transforms the ≤ goal into an = goal"""
    def tactic(goal):
        a, b = left_of(goal), right_of(goal)
        return eq(b, add(a, witness))   # b = a + witness
    tactic._lean = f"use {name}"
    return tactic
```

This is the bridge between ≤ and =. It turns `a ≤ b` into `b = a + c`.

---

## Part 6: Addition World — Complete Walkthrough (2+2=4)

### Starting Goal

```
Human:  (2 + 2) = 4
Tuple:  ("eq", ("add", ("two",), ("two",)),  ("four",))
```

---

**Step 1: `nth_rewrite 2 [two_eq_succ_one]`**

Find the 2nd `("two",)` in DFS order:

```
DFS traversal of ("eq", ("add", ("two",), ("two",)), ("four",)):
  eq → add → ("two",) [1st, SKIP] → ("two",) [2nd, MATCH!] → ("four",)
```

Replace with `("succ", ("one",))`:

```
BEFORE: (2 + 2) = 4
AFTER:  (2 + S(1)) = 4
Tuple:  ("eq", ("add", ("two",), ("succ", ("one",))), ("four",))
```

Why the 2nd? Because we want `add_succ` to fire: it needs `(a + S(b))`.

---

**Step 2: `rw [add_succ]`**

`add_succ_rule` scans the tree for `("add", a, ("succ", b))`:

```
Finds: ("add", ("two",), ("succ", ("one",)))
Match: a = ("two",),  b = ("one",)
Build: ("succ", ("add", ("two",), ("one",)))  =  S(2 + 1)
```

```
BEFORE: (2 + S(1)) = 4
AFTER:  S(2 + 1) = 4
```

The key: `a + S(b) → S(a + b)`. One `S` peeled off the right, wrapped around the whole `add`.

---

**Step 3: `rw [one_eq_succ_zero]`** → unfold `1` to `S(0)`

```
BEFORE: S(2 + 1) = 4    →    AFTER: S(2 + S(0)) = 4
```

---

**Step 4: `rw [add_succ]`** (again!)

```
Matches: ("add", ("two",), ("succ", ("zero",)))
Result:  S(S(2 + 0)) = 4
```

Second peel — that's why `2 + 2` needs TWO `add_succ` applications.

---

**Step 5: `rw [add_zero]`** → `(2 + 0) → 2`

```
BEFORE: S(S(2 + 0)) = 4    →    AFTER: S(S(2)) = 4
```

LHS is now fully simplified!

---

**Steps 6-7: Unfold the RHS `4 → S(3) → S(S(2))`**

```
Step 6: S(S(2)) = S(3)      (four_eq_succ_three)
Step 7: S(S(2)) = S(S(2))   (three_eq_succ_two)
```

---

**Step 8: `rfl`**

```python
lhs = ("succ", ("succ", ("two",)))
rhs = ("succ", ("succ", ("two",)))
lhs == rhs  →  True  ✓   # deep structural comparison
```

**QED. ∎**

### The Whole Proof As Function Composition

```python
proof = compose(
    nth_rewrite(2, two_eq_succ_one, "..."),   # function
    rw(add_succ_rule, "add_succ"),            # function
    rw(one_eq_succ_zero, "..."),              # function
    rw(add_succ_rule, "add_succ"),            # function
    rw(add_zero_rule, "add_zero"),            # function
    rw(four_eq_succ_three, "..."),            # function
    rw(three_eq_succ_two, "..."),             # function
)

goal = eq(add(two(), two()), four())     # one input
result = proof(goal)                     # one output
rfl(result)                              # ✓
```

**Seven functions composed into one. One input, one output. Function composition.**

---

## Part 7: Multiplication World — Why 2×2=4 Takes 19 Steps

### The Decomposition

Multiplication is defined by recursion on the right operand:
- `a * 0 = 0`
- `a * S(b) = (a * b) + a`

So `2 * 2` unfolds as:

```
2 * 2
= 2 * S(1)           (unfold 2)
= (2 * 1) + 2        (mul_succ: a*S(b) → a*b + a)
= (2 * S(0)) + 2     (unfold 1)
= ((2*0) + 2) + 2    (mul_succ again)
= (0 + 2) + 2        (mul_zero: a*0 → 0)
```

Now we have TWO addition subproblems: `(0 + 2)` and `result + 2`. Each `a + 2` takes ~5 rewrites (two `add_succ`, one `add_zero`, plus unfolding). That's why 2×2 takes 19 steps!

### Why 2×1 Takes 10 Steps But 1×2 Takes 13

`mul_succ` recurses on the **right** operand:
- `2 * 1`: one `mul_succ` → one addition → 10 steps
- `1 * 2`: two `mul_succ`s → two additions → 13 steps

Same answer, different proof structure. **Commutativity is not free** — it's a theorem you have to prove!

---

## Part 8: Inequality World — The NNG4 Definition

### How `≤` Is Defined (from the NNG4 repo)

```lean
-- From NNG4/Game/MyNat/LE.lean
a ≤ b  :=  ∃ c, b = a + c
```

In English: `a ≤ b` means "there EXISTS some gap `c` such that `b = a + c`."

This naturally works for natural numbers (no negatives!). To **prove** `a ≤ b`, you must:
1. **Find** the gap `c` (the "witness")
2. **Prove** that `b = a + c`

The `use` tactic handles step 1. Then `rw` + `rfl` handles step 2.

### Proof 8: le_refl — `x ≤ x` (NNG4 Level 1)

```lean
theorem le_refl (x) : x ≤ x := by
  use 0        -- witness: gap is 0
  rw [add_zero]
  rfl
```

Walkthrough with `x = 1`:

```
Goal:  1 ≤ 1
Tuple: ("le", ("one",), ("one",))

Step 1: use 0
  -- le(1, 1) becomes eq(1, add(1, 0))
  => 1 = (1 + 0)
  Tuple: ("eq", ("one",), ("add", ("one",), ("zero",)))

Step 2: rw [add_zero]
  -- add_zero_rule matches ("add", ("one",), ("zero",)) → ("one",)
  => 1 = 1
  Tuple: ("eq", ("one",), ("one",))

Step 3: rfl
  ("one",) == ("one",)  →  True ✓
```

**Why it works:** The gap from `x` to `x` is 0, and `x + 0 = x`.

### Proof 9: zero_le — `0 ≤ x` (NNG4 Level 2)

```lean
theorem zero_le (x) : 0 ≤ x := by
  use x        -- witness: gap is x itself!
  rw [zero_add]
  rfl
```

Walkthrough with `x = 2`:

```
Goal:  0 ≤ 2

Step 1: use 2      =>  2 = (0 + 2)    -- witness is x itself
Step 2: rw [zero_add]  =>  2 = 2      -- 0 + a = a
Step 3: rfl         =>  ✓
```

**Why it works:** The gap from 0 to `x` is `x`, and `0 + x = x`.

### Proof 10: le_succ_self — `x ≤ succ(x)` (NNG4 Level 3)

```lean
theorem le_succ_self (x) : x ≤ succ(x) := by
  use 1
  rw [succ_eq_add_one]
  rfl
```

Walkthrough with `x = 2`:

```
Goal:  2 ≤ 3

Step 1: use 1                    =>  3 = (2 + 1)
Step 2: rw [one_eq_succ_zero]    =>  3 = (2 + S(0))
Step 3: rw [add_succ]            =>  3 = S(2 + 0)
Step 4: rw [add_zero]            =>  3 = S(2)
Step 5: rw [three_eq_succ_two]   =>  S(2) = S(2)
Step 6: rfl                      =>  ✓
```

---

## Part 9: le_trans — The Flagship Proof (Hypotheses!)

This is **NNG4 Level 4** and introduces the most important new concept: **hypotheses** in the proof context.

### The Theorem

```lean
-- From NNG4/Game/Levels/LessOrEqual/L04le_trans.lean
theorem le_trans (x y z) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  cases hxy with a ha
  cases hyz with b hb
  use a + b
  rw [hb, ha]
  exact add_assoc x a b
```

### What Are Hypotheses?

Until now, every proof was just a goal with no assumptions. `le_trans` is different — it takes **inputs**:
- `hxy : x ≤ y` — we're GIVEN that x ≤ y
- `hyz : y ≤ z` — we're GIVEN that y ≤ z

These are like function parameters. The whole theorem is a **function**:

```
le_trans : (x ≤ y) → (y ≤ z) → (x ≤ z)
```

### What Does `cases` Do?

`cases hxy with a ha` **destructs** the existential. Remember, `x ≤ y` means `∃ c, y = x + c`. The `cases` tactic:

1. Takes the hypothesis `hxy : x ≤ y` (which is `∃ c, y = x + c`)
2. **Extracts** the witness `a` (the gap) and the equation `ha : y = x + a`
3. **Removes** the original `hxy` from the context

This is **pattern matching on a proof** — a fundamentally functional operation!

### Walkthrough: 1 ≤ 2, 2 ≤ 4 ⟹ 1 ≤ 4

```
INITIAL STATE:
  Goal:   1 ≤ 4
  Hypotheses:
    hxy : 1 ≤ 2
    hyz : 2 ≤ 4

Step 1: cases hxy with a ha
  -- Destructs "1 ≤ 2" into:
  --   a = 1  (the gap from 1 to 2)
  --   ha : 2 = 1 + 1  (the equation)
  Goal:   1 ≤ 4
  Context:
    a  : 1
    ha : 2 = (1 + 1)
    hyz : 2 ≤ 4

Step 2: cases hyz with b hb
  -- Destructs "2 ≤ 4" into:
  --   b = 2  (the gap from 2 to 4)
  --   hb : 4 = 2 + 2  (the equation)
  Goal:   1 ≤ 4
  Context:
    a  : 1
    ha : 2 = (1 + 1)
    b  : 2
    hb : 4 = (2 + 2)

Step 3: use a + b  (witness: 1 + 2 = 3)
  -- Since 1 ≤ 4 means ∃ c, 4 = 1 + c
  -- We provide c = a + b = 1 + 2
  Goal:   4 = 1 + (1 + 2)

Step 4: rw [hb]  — rewrite 4 using hb: 4 = 2+2
  Goal:   (2 + 2) = 1 + (1 + 2)

Step 5: rw [ha]  — rewrite leftmost 2 using ha: 2 = 1+1
  Goal:   ((1+1) + 2) = 1 + (1 + 2)

Step 6: exact add_assoc  — apply the associativity theorem
  -- add_assoc says: (a + b) + c = a + (b + c)
  -- So (1+1)+2 = 1+(1+2) is EXACTLY associativity!
  Goal:   (1 + (1 + 2)) = (1 + (1 + 2))

Step 7: rfl  =>  ✓
  -- Both sides are structurally identical!
```

### The FP Concepts in le_trans

| Concept | How It Appears |
|---|---|
| **Function inputs** | `hxy` and `hyz` are hypothesis parameters |
| **Pattern matching** | `cases` destructs `∃` into (witness, equation) |
| **Rewriting with data** | `rw [hb]` uses hypothesis as a rewrite rule |
| **Theorem application** | `exact add_assoc` treats a theorem as a function |
| **Pure state** | Every step transforms `(goal, hyps)` purely |

---

## Part 10: All FP Concepts in One Table

| Concept | Where It Appears | Example |
|---|---|---|
| **Pure functions** | Every tactic | `goal → goal`, no side effects |
| **Composition** | Every proof | `proof = compose(t1, t2, ..., tn)` |
| **Higher-order functions** | `rw(rule)` | Takes function, returns function |
| **Closures** | Inside `rw` | Captures `rule` from enclosing scope |
| **Tagged tuples (ADTs)** | All data | `("succ", ("zero",))` = S(0) |
| **Pattern matching** | All rules | `add_succ_rule` matches `("add", a, ("succ", b))` |
| **Immutability** | All steps | Creates NEW tuples, never mutates old |
| **Structural recursion** | `apply_first` | Recurses over the term tree |
| **Existential types** | `a ≤ b` | `∃ c, b = a + c` — destructured by `cases` |
| **Currying** | `use(witness)` | Takes value, returns tactic function |

---

## Part 11: What to Tell Your Professor

> "I've built Python simulations of Lean 4's proof system using only functional programming — no classes, just functions and tagged tuples.
>
> There are 14 proofs across three 'worlds' from the Natural Number Game:
> - **Addition World (4 proofs):** 2+2=4, 1+1=2, 3+1=4, 1+2=3
> - **Multiplication World (3 proofs):** 2*1=2, 1*2=2, 2*2=4 (19 rewrites!)
> - **Inequality World (7 proofs):** le_refl, zero_le (×3), le_succ_self (×2), and **le_trans** with hypotheses
>
> Every rewrite rule is a pure function that pattern matches a tagged tuple. The `rw` tactic is a higher-order function that takes a rule function and returns a tactic function — a closure. The `use` tactic turns existential propositions into equalities.
>
> The le_trans proof is especially interesting: `cases` destructs hypotheses (pattern matching on proofs!), `rw [h]` rewrites using hypothesis-provided equations, and `exact add_assoc` applies a theorem as a function. Every step transforms the proof state purely — no mutation, no side effects.
>
> This isn't just an analogy — Lean's kernel actually works this way. Its internal `Expr` type is a tagged tree, `rw` does DFS traversal + pattern matching, and `rfl` does deep structural comparison. Proofs ARE programs. Lean's proof-checking IS type-checking of a functional program."

---

## Part 12: How the Lean Compiler Actually Works

This section covers Lean's internals — what happens when you write `theorem : 2+2=4 := by rw [...]; rfl` and hit enter.

### The Full Pipeline

```
Source Code (.lean file)
    │
    ▼
┌──────────┐
│  PARSER  │   Converts text → Syntax tree (concrete syntax tree)
└──────────┘
    │
    ▼
┌──────────────┐
│  ELABORATOR  │   Converts Syntax → Expr (core expression tree)
│              │   This is where tactics run!
│              │   Infers types, resolves names, expands macros
└──────────────┘
    │
    ▼
┌──────────┐
│  KERNEL  │   The TRUSTED core. Type-checks the Expr.
│          │   ~5000 lines of C++. Tiny on purpose.
│          │   If the kernel accepts it, the proof is VALID.
└──────────┘
    │
    ▼
┌──────────────┐
│ ENVIRONMENT  │   Stores all accepted definitions + theorems
│              │   Used by future proofs
└──────────────┘
```

### Stage 1: Parsing

The parser reads `.lean` source code and produces a **concrete syntax tree** (CST). This is purely textual — no type information yet.

```
Input:  "theorem : 2 + 2 = 4 := by rw [add_succ]; rfl"

CST:    (declaration
          (theorem
            (type (eq (add (num 2) (num 2)) (num 4)))
            (tactic_block
              (rw (ident "add_succ"))
              (rfl))))
```

At this point Lean doesn't know what `2`, `+`, or `=` mean — they're just tokens.

### Stage 2: Elaboration (Where Tactics Run!)

The elaborator is the big engine. It converts the syntax tree into a **core expression** (`Expr`) — Lean's internal representation. Here's what it does:

1. **Name resolution:** Looks up `2` → `@OfNat.ofNat Nat 2 _`, looks up `+` → `@HAdd.hAdd Nat Nat Nat _`
2. **Type inference:** Figures out that `2 + 2` has type `Nat`, so `=` means `@Eq Nat`
3. **Tactic execution:** When it sees `by`, it enters **tactic mode**

#### Tactic Mode — This Is What We Simulate!

In tactic mode, the elaborator maintains a **proof state**:

```
ProofState = {
  goals: [Goal],           -- list of remaining goals
  metavars: [MetaVar],     -- "holes" in the proof term being built
}

Goal = {
  target: Expr,            -- what you need to prove (the ⊢ line)
  context: [LocalDecl],    -- hypotheses (the stuff above ⊢)
}
```

Each tactic is a function `ProofState → ProofState`:

```
rw [add_succ]:
  Input:   { goals: [⊢ (2 + 2) = 4], metavars: [?m1] }
  Output:  { goals: [⊢ S(2 + 1) = 4], metavars: [?m1, ?m2] }
```

The tactic also builds a **proof term** behind the scenes — a lambda calculus expression that WITNESSES the proof. You never see it in tactic mode, but it's what gets sent to the kernel.

When all goals are closed (no remaining `?metavars`), the elaborator has a complete proof term.

#### What the Proof Term Looks Like

When you write:
```lean
theorem : 2 + 2 = 4 := by rw [two_eq_succ_one]; rfl
```

The elaborator produces something like:
```lean
-- Actual proof TERM (what the kernel sees):
theorem : 2 + 2 = 4 :=
  @Eq.mpr Nat (2 + succ 1) 4
    (@congrArg Nat Nat 2 (succ 1) (fun x => x + 2 = 4) (two_eq_succ_one))
    (@Eq.refl Nat 4)
```

This is a **functional program** — `Eq.mpr`, `congrArg`, `Eq.refl` are all functions. The proof is a composition of these functions. **Proofs ARE programs.**

### Stage 3: The Kernel (The Trusted Core)

The kernel is deliberately tiny (~5000 lines of C++) and does ONE thing: **type-check `Expr` trees**.

When the elaborator gives the kernel a proof term, the kernel:

1. **Checks that the term has the right type.** For a theorem `P`, the proof term must have type `P`. This is the Curry-Howard correspondence in action — proving `P` = constructing a value of type `P`.

2. **Checks definitional equality (`is_def_eq`).** This is our `rfl` — deep structural comparison of `Expr` trees. But the kernel can also unfold definitions, do beta reduction (lambda application), and reduce recursors. So it's smarter than raw `==`.

3. **Checks universe consistency.** Makes sure types don't refer to themselves paradoxically (prevents Russell's paradox).

```
Kernel check for "2 + 2 = 4":

1. Type of proof term = @Eq Nat (2+2) 4 ?  
2. Unfold 2+2:
   2 + 2
   = Nat.add (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))
   -- Nat.add is defined by recursion on the 2nd arg:
   = Nat.succ (Nat.add (succ (succ zero)) (succ zero))
   = Nat.succ (Nat.succ (Nat.add (succ (succ zero)) zero))
   = Nat.succ (Nat.succ (Nat.succ (Nat.succ zero)))
   = 4 ✓
3. is_def_eq(2+2, 4) = true
4. Type checks. QED.
```

#### Why Is the Kernel So Small?

This is the **de Bruijn criterion**: the trusted core should be tiny enough for a human to audit. All the complex machinery (tactics, elaboration, macros) lives OUTSIDE the kernel. If there's a bug in a tactic, the worst that happens is the tactic generates a wrong proof term — but the kernel will REJECT it.

```
         ┌─────────────────────────┐
         │    UNTRUSTED ZONE       │
         │  ┌─────────────────┐    │
         │  │   Tactics       │    │   Can have bugs — kernel catches them
         │  │   Macros        │    │
         │  │   Elaborator    │    │
         │  │   Parser        │    │
         │  └────────┬────────┘    │
         └───────────┼─────────────┘
                     │ proof term
                     ▼
         ┌─────────────────────────┐
         │    TRUSTED KERNEL       │   ~5000 lines of C++
         │                         │   Type-checks the term
         │    Accept ✓ or Reject ✗ │   If ✓, the proof is VALID
         └─────────────────────────┘
```

### Stage 4: The Environment

Once the kernel accepts a theorem, it's added to the **environment** — a persistent store of all definitions and theorems. Future proofs can reference it.

```
Environment = Map<Name, Declaration>

After "theorem add_zero (a : Nat) : a + 0 = a":
  env["add_zero"] = {
    type:  ∀ (a : Nat),  a + 0 = a
    value: <proof term>
  }
```

When a later proof writes `rw [add_zero]`, the elaborator looks up `add_zero` in the environment, gets its type (which tells it what to rewrite), and applies it.

### How Our Simulation Maps to Lean's Architecture

| Lean Component | Our Simulation |
|---|---|
| `Expr` (tagged tree) | Tagged tuples: `("add", ("two",), ("two",))` |
| Tactic `rw` | `rw(rule, name)` — higher-order function |
| Tactic `rfl` | `rfl(goal)` — deep structural `==` |
| Tactic `use` | `use(witness, name)` — transforms `le → eq` |
| Tactic `cases` | Step functions that destruct hypotheses |
| DFS rewrite traversal | `apply_first(goal, rule)` |
| Definitional equality | Python's `==` on nested tuples |
| Proof state (goal) | Single tuple (`eq(...)` or `le(...)`) |
| Proof state (context) | `hyps` dict in `run_hyp_proof` |
| Rewrite rules | Functions `term → term \| None` |

The main things we DON'T simulate:
- **Type inference** (we hardcode the types)
- **Universe checking** (not relevant for Nat)
- **Proof term generation** (we show tactics directly, not the lambda calculus witness)
- **Definitional unfolding** (our kernel doesn't auto-unfold — we do it manually with `rw`)

But the CORE mechanism — tactics as functions transforming expression trees — is faithfully reproduced.

---

## Running the Demos

```bash
python lean_proof_sim.py     # All 14 proofs (addition, multiplication, inequality)
python hk_proof_sim.py       # Hohenberg-Kohn theorem (DFT)
python janak_proof_sim.py    # Janak's theorem
```
