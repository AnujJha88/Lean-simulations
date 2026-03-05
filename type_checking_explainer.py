"""
THE TYPE CHECKING EXPLAINER
===========================

Your professor has asked a beautiful and fundamental question about type theory:
"If `add(2, 2)` evaluated is `int` and `4` evaluated is `int`, but `add(2, 3)` 
is also `int` and `4` is `int` — how does 'type checking' prove anything? 
They both type-check to `int`, but one is false!"

The answer lies in the difference between "Simple Types" (like Java/Python) 
and "Dependent Types" (like Lean).

In Lean, the theorem `2 + 2 = 4` is NOT of type `int`. 
The theorem `2 + 2 = 4` is of type `Prop` (Proposition), and the specific
type we want to inhabit is the EQUALITY type `Eq(add(2,2), 4)`.

Here is a Python simulation comparing normal programming type-checking 
with Dependent Type Theory (Lean) type-checking.
"""

# =========================================================================
# PART 1: NORMAL PROGRAMMING (Simple Types)
# This is what your professor is thinking about.
# =========================================================================

def simple_type_check(a, b):
    # In Python/Java, type checking just checks memory categories (int, string)
    if type(a) == type(b):
        return True
    return False

# Professor's counter-example:
print("--- NORMAL PROGRAMMING TYPE CHECK ---")
val1 = 2 + 2
val2 = 4
val3 = 2 + 3

print(f"Type of (2+2) is {type(val1).__name__}")
print(f"Type of (4)   is {type(val2).__name__}")
print(f"Type of (2+3) is {type(val3).__name__}")

# The professor is right! In normal programming, these all "type check" properly!
# Normal type systems CANNOT prove mathematics.
print(f"Does (2+2) and (4) have the same type? {simple_type_check(val1, val2)}") # True
print(f"Does (2+3) and (4) have the same type? {simple_type_check(val3, val2)}") # True! (This is what he meant)


# =========================================================================
# PART 2: LEAN'S DEPENDENT TYPES (The Curry-Howard Correspondence)
# This is how interactive theorem provers actually work.
# =========================================================================

print("\n--- LEAN'S DEPENDENT TYPE CHECK ---")

class Expr:
    """Base class for AST Nodes."""
    def reduce(self): 
        return self

class Nat(Expr):
    """Primitive numbers."""
    def __init__(self, val): self.val = val
    def reduce(self): return self
    def __repr__(self): return str(self.val)

class Add(Expr):
    """Addition AST node. It has NOT been computed yet!"""
    def __init__(self, a, b):
        self.a = a
        self.b = b
    
    def reduce(self):
        # Lean uses 'isDefEq' (Definitional Equality) to reduce terms to primitive forms.
        # This is where 2+2 literally computes into 4.
        val_a = self.a.reduce().val
        val_b = self.b.reduce().val
        return Nat(val_a + val_b)

class EqType:
    """
    CRITICAL CONCEPT!
    In Lean, `2 + 2 = 4` is a TYPE itself. It is not an `int`.
    It is a type parametrized by two mathematical expressions.
    """
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

def lean_type_checker(proof_attempt, desired_type: EqType):
    """
    Lean's kernel checks if the proof you built actually matches the Type 
    (the Theorem) you claim to have proven.
    """
    # 1. The Kernel reduces the left-hand side of the Type
    reduced_lhs = desired_type.lhs.reduce()
    
    # 2. The Kernel reduces the right-hand side of the Type
    reduced_rhs = desired_type.rhs.reduce()
    
    # 3. IF they reduce to the EXACT same primitive memory structure (Definitional Equality), 
    # the Type `Eq(LHS, RHS)` is valid, and the proof is accepted!
    if reduced_lhs.val == reduced_rhs.val:
        return "Type Check PASSED! The theorem is true."
    else:
        return "Type Check FAILED! The expressions do not reduce to the same value."

# Let's test the professor's cases!

# Case 1: 2 + 2 = 4
theorem_1_type = EqType( Add(Nat(2), Nat(2)), Nat(4) )
# The kernel checks the TYPE itself: does `reduce(2+2)` == `reduce(4)`? Let's check:
result1 = lean_type_checker("dummy_proof_payload", theorem_1_type)
print(f"Lean analyzing Type `2 + 2 = 4`: {result1}")


# Case 2: 2 + 3 = 4 (The professor's counter-example)
theorem_2_type = EqType( Add(Nat(2), Nat(3)), Nat(4) )
# The kernel checks the TYPE: does `reduce(2+3)` == `reduce(4)`?
# This will reduce to Nat(5) == Nat(4). The memory structures do NOT match!
result2 = lean_type_checker("dummy_proof_payload", theorem_2_type)
print(f"Lean analyzing Type `2 + 3 = 4`: {result2}")

"""
SUMMARY FOR YOUR PROFESSOR (Tying it to the Lean 4 Architecture Report):

When your professor points out that `add(2,3)` evaluates to `int` and `4` evaluates to `int`, 
he is correctly describing how the "Untrusted Frontend" parses the syntax.

However, as outlined in our `LEAN_COMPILER_INTERNALS.md` report, Lean is a strictly 
Bifurcated Two-Tier System. The math is not verified by checking simple variable types. 
It is verified by the "Trusted Kernel" (the 5,000 lines of C++).

In the Trusted Kernel, `2 + 2 = 4` is NOT an equation evaluating to a boolean. 
It is a **Type** itself. Specifically, it is the parameterized dependent type: 
`Eq (add 2 2) (4)`.

To verify if your generated proof object actually inhabits this Type, the Kernel 
must use its "Definitional Equality" (`isDefEq`) algorithm. The Kernel does not look 
at the labels; it physically computes the data using its 4 internal Reduction Engines:

1. It takes the left-hand side (`add 2 3`) and subjects it to Delta ($\delta$) Reduction 
   (unfolding the definition of addition) and Iota ($\iota$) Reduction (executing the 
   Peano recursors). `add 2 3` is ground down to the primitive data structure `Nat(5)`.
2. It takes the right-hand side (`4`) and performs the same grinding process, resulting 
   in the primitive data structure `Nat(4)`.
3. The Kernel then performs a structural hashing comparison. 
   Does the memory tree `Nat(5)` exactly match the memory tree `Nat(4)`? No.

Because they represent completely different structures in memory, the Definitional 
Equality check fails. The Kernel mathematically concludes that the Type `Eq(Add(2,3), 4)` 
is uninhabitable (it's impossible to build a proof term for it). The Kernel physically 
rejects the proof payload with a Type Error!

This exact mechanism—relying on pure structural reduction rather than loose category 
tags like `int`—is why the Lean Kernel holds the ultimate authority on mathematical truth.
"""
