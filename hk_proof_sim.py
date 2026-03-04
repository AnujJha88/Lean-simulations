"""
════════════════════════════════════════════════════════════════════════
  Hohenberg-Kohn Theorem (HK1) — Full Symbolic Proof Simulation
  ==============================================================

  This simulation ACTUALLY performs the proof:
    • Expressions are trees of nested tuples
    • substitute() walks trees and replaces subexpressions
    • Axioms are functions that BUILD propositions from expressions
    • Rewriting ACTUALLY transforms the expression trees
    • The contradiction is DETECTED, not asserted
    • Every step is verifiable — check the tuples yourself

  No classes. Only functions, tuples, and closures.
════════════════════════════════════════════════════════════════════════
"""


# ════════════════════════════════════════════════════════════════════
# PART 1: EXPRESSION CONSTRUCTORS — functions that build tuples
# ════════════════════════════════════════════════════════════════════

def var(name):          return ("var", name)
def app(fn, *args):     return ("app", fn, args)
def plus(a, b):         return ("binop", "+", a, b)
def minus(a, b):        return ("binop", "-", a, b)

# Display: expr → string
def show(e):
    t = e[0]
    if t == "var":    return e[1]
    if t == "app":
        fn, args = e[1], e[2]
        if not args: return fn
        return f"{fn}({', '.join(show(a) for a in args)})"
    if t == "binop":  return f"({show(e[2])} {e[1]} {show(e[3])})"
    return str(e)


# ════════════════════════════════════════════════════════════════════
# PART 2: SUBSTITUTE — the core operation (walks the tuple tree)
# ════════════════════════════════════════════════════════════════════
#
# substitute : (expr, old_expr, new_expr) → expr
#
# This is THE key function. It walks the expression tree and
# replaces every occurrence of `old` with `new`.
# Python's == on tuples does deep structural comparison, so this
# is clean and correct.

def substitute(expr, old, new):
    """
    Replace all occurrences of `old` with `new` inside `expr`.

    Pure function: expr → expr  (never mutates the input)
    Uses structural recursion over the tagged tuple tree.

    Example:
      substitute( ("binop", "+", T_ψ2, ∫v1_ρψ2), ρ(ψ2), n )
      →          ("binop", "+", T_ψ2, ∫v1_n)
    """
    # Base case: exact structural match
    if expr == old:
        return new

    tag = expr[0]
    if tag == "var":
        return expr  # leaf node — no children to recurse into

    if tag == "app":
        fn, args = expr[1], expr[2]
        new_args = tuple(substitute(a, old, new) for a in args)
        return ("app", fn, new_args)

    if tag == "binop":
        op, left, right = expr[1], expr[2], expr[3]
        return ("binop", op,
                substitute(left, old, new),
                substitute(right, old, new))

    return expr


# ════════════════════════════════════════════════════════════════════
# PART 3: PROPOSITIONS & OPERATIONS ON THEM
# ════════════════════════════════════════════════════════════════════

def prop_eq(a, b):    return ("eq", a, b)
def prop_gt(a, b):    return ("gt", a, b)
def prop_neq(a, b):   return ("neq", a, b)
def prop_false():     return ("false",)

def show_prop(p):
    t = p[0]
    if t == "eq":    return f"{show(p[1])} = {show(p[2])}"
    if t == "gt":    return f"{show(p[1])} > {show(p[2])}"
    if t == "neq":   return f"{show(p[1])} ≠ {show(p[2])}"
    if t == "false": return "False"
    return str(p)


def sub_in_prop(prop, old, new):
    """
    Rewrite inside a proposition: replace `old` with `new`.
    prop → prop  (pure function)
    """
    tag = prop[0]
    if tag == "eq":
        return ("eq", substitute(prop[1], old, new),
                      substitute(prop[2], old, new))
    if tag == "gt":
        return ("gt", substitute(prop[1], old, new),
                      substitute(prop[2], old, new))
    return prop


def rewrite_gt_with_eqs(gt_prop, lhs_eq, rhs_eq):
    """
    Given:  A > B           (gt_prop)
            A = A'          (lhs_eq)
            B = B'          (rhs_eq)
    Derive: A' > B'

    This is the key derivation step: substitute equal expressions
    into an inequality. Pure function: (prop, prop, prop) → prop
    """
    A, B = gt_prop[1], gt_prop[2]
    # Verify the equations match
    assert lhs_eq[1] == A, f"LHS mismatch: {show(lhs_eq[1])} ≠ {show(A)}"
    assert rhs_eq[1] == B, f"RHS mismatch: {show(rhs_eq[1])} ≠ {show(B)}"
    A_prime = lhs_eq[2]
    B_prime = rhs_eq[2]
    return ("gt", A_prime, B_prime)


def cancel_common_addend(gt_prop):
    """
    Given:  (X + C) > (Y + C)
    Derive: X > Y

    Cancels a common addend from both sides of an inequality.
    Pure function: prop → prop
    """
    lhs, rhs = gt_prop[1], gt_prop[2]
    # Check both sides are (something + something)
    if (lhs[0] == "binop" and lhs[1] == "+"
        and rhs[0] == "binop" and rhs[1] == "+"):
        C_left = lhs[3]   # right operand of lhs sum
        C_right = rhs[3]  # right operand of rhs sum
        if C_left == C_right:
            return ("gt", lhs[2], rhs[2])
    raise ValueError(f"Cannot cancel: {show_prop(gt_prop)}")


def detect_contradiction(gt1, gt2):
    """
    Given:  X > Y   (gt1)
            Y > X   (gt2)
    Return True if these are contradictory.

    Pure function: (prop, prop) → bool
    """
    return gt1[1] == gt2[2] and gt1[2] == gt2[1]


# ════════════════════════════════════════════════════════════════════
# PART 4: AXIOMS — functions that produce propositions from terms
# ════════════════════════════════════════════════════════════════════
#
# In Lean, axioms are declared types. Here, each axiom is a FUNCTION
# that takes expressions and constructs a proposition.
# These are the PRIMITIVES — the building blocks everything derives from.

def density_of(psi):            return app("ρ", psi)
def kinetic_interaction(psi):   return app("T", psi)
def integral(v, n):             return app("∫v·n", v, n)
def energy_expectation(psi, v): return app("⟨ψ|H|ψ⟩", psi, v)
def ground_state(v):            return app("Ψ_gs", v)
def ground_energy(v):           return app("E_gs", v)


def axiom_energy_def(psi, v):
    """
    Lean:  axiom energy_def (ψ : Wavefunc) (v : Potential) :
             energy_expectation ψ v = kinetic_interaction ψ + integral v (density_of ψ)

    A function: (ψ, v) → proposition
    """
    lhs = energy_expectation(psi, v)
    rhs = plus(kinetic_interaction(psi), integral(v, density_of(psi)))
    return prop_eq(lhs, rhs)


def axiom_ground_energy_def(v):
    """
    Lean:  axiom ground_energy_def (v : Potential) :
             ground_energy v = energy_expectation (ground_state v) v

    A function: v → proposition
    """
    return prop_eq(ground_energy(v), energy_expectation(ground_state(v), v))


def axiom_rayleigh_ritz(v, psi):
    """
    Lean:  axiom rayleigh_ritz_strict (v : Potential) (ψ : Wavefunc) :
             ψ ≠ ground_state v → energy_expectation ψ v > ground_energy v

    A function: (v, ψ) → proposition  (given ψ ≠ ground_state v)
    """
    return prop_gt(energy_expectation(psi, v), ground_energy(v))


def axiom_distinct_states(v1, v2):
    """
    Lean:  axiom distinct_potentials_distinct_states (v₁ v₂ : Potential) :
             (¬ ∃ c, ∀ x, v₁ x = v₂ x + c) → ground_state v₁ ≠ ground_state v₂

    A function: (v₁, v₂) → proposition
    """
    return prop_neq(ground_state(v1), ground_state(v2))


# ════════════════════════════════════════════════════════════════════
# PART 5: PROOF STATE — immutable dict, updated by pure functions
# ════════════════════════════════════════════════════════════════════

def make_state(goal, hyps=None):
    return {"goal": goal, "hyps": dict(hyps or {})}

def add_hyp(state, name, prop):
    """Add hypothesis → NEW state. Never mutates original."""
    new_hyps = dict(state["hyps"])
    new_hyps[name] = prop
    return {"goal": state["goal"], "hyps": new_hyps}

def replace_hyp(state, name, prop):
    """Replace hypothesis → NEW state."""
    new_hyps = dict(state["hyps"])
    new_hyps[name] = prop
    return {"goal": state["goal"], "hyps": new_hyps}

def show_state(state, colors):
    """Display full proof state."""
    D, Y, R, BOLD = colors["D"], colors["Y"], colors["R"], colors["BOLD"]
    print(f"  {D}┌─ Proof State ──────────────────────────────────────────────{R}")
    print(f"  {D}│ Goal: {show_prop(state['goal'])}{R}")
    for name, prop in state["hyps"].items():
        print(f"  {D}│ {name:20s}: {show_prop(prop)}{R}")
    print(f"  {D}└────────────────────────────────────────────────────────────{R}")


# ════════════════════════════════════════════════════════════════════
# PART 6: THE PROOF
# ════════════════════════════════════════════════════════════════════

def run_hk_proof():

    B = "\033[94m"; G = "\033[92m"; Y = "\033[93m"; C = "\033[96m"
    M = "\033[95m"; RED = "\033[91m"; D = "\033[2m"; BOLD = "\033[1m"; R = "\033[0m"
    colors = {"B":B, "G":G, "Y":Y, "C":C, "M":M, "RED":RED, "D":D, "BOLD":BOLD, "R":R}

    step_num = [0]
    def step(lean_code, description, derived=None, verify=None):
        step_num[0] += 1
        print(f"\n  {BOLD}Step {step_num[0]}:{R} {C}{lean_code}{R}")
        print(f"  {D}  ↳ {description}{R}")
        if derived:
            print(f"  {Y}  ⊢ {derived}{R}")
        if verify:
            print(f"  {G}  ✓ {verify}{R}")

    # ── Title ──
    print(f"\n{BOLD}{B}{'═' * 72}")
    print(f"  HOHENBERG-KOHN THEOREM 1 — Full Symbolic Proof Simulation")
    print(f"  (Real expression manipulation — substitution, derivation, verification)")
    print(f"{'═' * 72}{R}")
    print(f"""
  {BOLD}Theorem:{R} v₁ ≢ v₂  →  ρ(Ψ_gs(v₁)) ≠ ρ(Ψ_gs(v₂))
  {D}(Different potentials cannot produce the same ground-state density){R}

  {BOLD}Proof:{R} Contradiction — assume ρ₁ = ρ₂, derive X > Y AND Y > X.
""")

    # ── Axioms ──
    print(f"{BOLD}{C}  ── AXIOMS (primitive functions of the system) ────────────────{R}")
    print(f"    {M}energy_def(ψ,v){R}      : ⟨ψ|H|ψ⟩(ψ,v) = T(ψ) + ∫v·ρ(ψ)")
    print(f"    {M}ground_energy_def(v){R} : E_gs(v)      = ⟨ψ|H|ψ⟩(Ψ_gs(v), v)")
    print(f"    {M}rayleigh_ritz(v,ψ){R}   : ψ≠Ψ_gs(v) → ⟨ψ|H|ψ⟩(ψ,v) > E_gs(v)")
    print(f"    {M}distinct_states(v₁,v₂){R}: v₁≢v₂ → Ψ_gs(v₁) ≠ Ψ_gs(v₂)")

    # ── Symbolic setup ──
    v1, v2 = var("v₁"), var("v₂")
    psi1 = ground_state(v1)   # Ψ_gs(v₁)
    psi2 = ground_state(v2)   # Ψ_gs(v₂)
    rho1 = density_of(psi1)   # ρ(Ψ_gs(v₁))
    rho2 = density_of(psi2)   # ρ(Ψ_gs(v₂))

    # ── Initial state ──
    state = make_state(
        goal=("false",),
        hyps={
            "h_distinct":  prop_neq(v1, v2),
            "h_same_dens": prop_eq(rho1, rho2),
        }
    )

    print(f"\n{BOLD}{C}  ── PROOF ─────────────────────────────────────────────────────{R}")
    show_state(state, colors)

    # ══════════════════════════════════════════════════════════════
    # Step 1: Ground states are distinct
    # ══════════════════════════════════════════════════════════════
    states_dist = axiom_distinct_states(v1, v2)  # ← FUNCTION CALL: axiom applied
    state = add_hyp(state, "states_distinct", states_dist)
    step("have states_distinct := distinct_potentials_distinct_states v₁ v₂ h_distinct",
         "APPLY AXIOM: distinct potentials → distinct ground states",
         show_prop(states_dist),
         "axiom_distinct_states(v₁, v₂) returned this proposition")

    # ══════════════════════════════════════════════════════════════
    # Step 2: Rayleigh-Ritz for ψ₂ under v₁
    # ══════════════════════════════════════════════════════════════
    rr1 = axiom_rayleigh_ritz(v1, psi2)  # ← FUNCTION CALL
    state = add_hyp(state, "rr₁", rr1)
    step("have rr₁ := rayleigh_ritz_strict v₁ ψ₂ (ψ₂ ≠ Ψ_gs(v₁))",
         "APPLY AXIOM: ψ₂ is not the ground state of v₁ → higher energy",
         show_prop(rr1),
         "axiom_rayleigh_ritz(v₁, Ψ_gs(v₂)) returned this proposition")

    # ══════════════════════════════════════════════════════════════
    # Step 3: Rayleigh-Ritz for ψ₁ under v₂
    # ══════════════════════════════════════════════════════════════
    rr2 = axiom_rayleigh_ritz(v2, psi1)  # ← FUNCTION CALL
    state = add_hyp(state, "rr₂", rr2)
    step("have rr₂ := rayleigh_ritz_strict v₂ ψ₁ (ψ₁ ≠ Ψ_gs(v₂))",
         "APPLY AXIOM: ψ₁ is not the ground state of v₂ → higher energy",
         show_prop(rr2))

    # ══════════════════════════════════════════════════════════════
    # Step 4: Expand ⟨ψ₂|H₁|ψ₂⟩ via energy_def
    # ══════════════════════════════════════════════════════════════
    exp1 = axiom_energy_def(psi2, v1)   # ← FUNCTION CALL
    state = add_hyp(state, "exp₁", exp1)
    step("have exp₁ := energy_def ψ₂ v₁",
         "APPLY AXIOM: expand energy into kinetic + potential pieces",
         show_prop(exp1),
         f"axiom_energy_def(Ψ_gs(v₂), v₁) built this equation")

    # ══════════════════════════════════════════════════════════════
    # Step 5: Expand ⟨ψ₁|H₂|ψ₁⟩ via energy_def
    # ══════════════════════════════════════════════════════════════
    exp2 = axiom_energy_def(psi1, v2)   # ← FUNCTION CALL
    state = add_hyp(state, "exp₂", exp2)
    step("have exp₂ := energy_def ψ₁ v₂",
         "APPLY AXIOM: same expansion for the other direction",
         show_prop(exp2))

    # ══════════════════════════════════════════════════════════════
    # Step 6-7: Expand ground energies (two-step rewrite)
    # ══════════════════════════════════════════════════════════════
    # First unfold: E_gs(v₁) = ⟨ψ|H|ψ⟩(Ψ_gs(v₁), v₁)
    ge1_step1 = axiom_ground_energy_def(v1)
    # Then apply energy_def: ⟨ψ|H|ψ⟩(Ψ_gs(v₁), v₁) = T(ψ₁) + ∫v₁·ρ(ψ₁)
    ge1_step2 = axiom_energy_def(psi1, v1)
    # Chain: E_gs(v₁) = T(ψ₁) + ∫v₁·ρ(ψ₁)
    #   by transitivity: if A = B and B = C, then A = C
    e1 = prop_eq(ge1_step1[1], ge1_step2[2])
    state = add_hyp(state, "e₁", e1)
    step("have e₁ : E_gs(v₁) = T(ψ₁) + ∫v₁·ρ(ψ₁)   [rw ground_energy_def, energy_def]",
         f"CHAIN 2 AXIOMS: ground_energy_def then energy_def (function composition!)",
         show_prop(e1),
         f"Step A: {show_prop(ge1_step1)}\n"
         f"  {G}  ✓ Step B: {show_prop(ge1_step2)}\n"
         f"  {G}  ✓ Chain:  {show_prop(e1)}")

    ge2_step1 = axiom_ground_energy_def(v2)
    ge2_step2 = axiom_energy_def(psi2, v2)
    e2 = prop_eq(ge2_step1[1], ge2_step2[2])
    state = add_hyp(state, "e₂", e2)
    step("have e₂ : E_gs(v₂) = T(ψ₂) + ∫v₂·ρ(ψ₂)   [rw ground_energy_def, energy_def]",
         "CHAIN 2 AXIOMS again for v₂",
         show_prop(e2))

    # ══════════════════════════════════════════════════════════════
    # Step 8: Use common density — THE KEY REWRITE
    # ══════════════════════════════════════════════════════════════
    # h_same_dens says ρ(ψ₁) = ρ(ψ₂), so define n := ρ(ψ₁) and rewrite ρ(ψ₂) → n
    n = rho1  # n IS ρ(ψ₁) — we use rho1 directly as the common density

    # Rewrite exp₁: substitute ρ(ψ₂) → n in exp₁
    exp1_rw = sub_in_prop(exp1, rho2, n)
    state = replace_hyp(state, "exp₁", exp1_rw)
    step("rw [h_same_dens.symm] at exp₁   — substitute ρ(Ψ_gs(v₂)) → ρ(Ψ_gs(v₁))",
         f"SUBSTITUTE: sub_in_prop(exp₁, ρ(ψ₂), n) — actual tree walk!",
         f"exp₁ becomes: {show_prop(exp1_rw)}",
         f"substitute() walked the tuple tree and replaced ρ(Ψ_gs(v₂)) with ρ(Ψ_gs(v₁))")

    # Rewrite e₂: substitute ρ(ψ₂) → n in e₂
    e2_rw = sub_in_prop(e2, rho2, n)
    state = replace_hyp(state, "e₂", e2_rw)
    step("rw [h_same_dens.symm] at e₂     — substitute ρ(Ψ_gs(v₂)) → ρ(Ψ_gs(v₁))",
         f"SUBSTITUTE again in e₂",
         f"e₂ becomes: {show_prop(e2_rw)}")

    # ══════════════════════════════════════════════════════════════
    # Step 9: Derive ineq₁ — T(ψ₂) > T(ψ₁)
    # ══════════════════════════════════════════════════════════════
    # rr₁:   ⟨ψ₂|H₁|ψ₂⟩ > E_gs(v₁)
    # exp₁:  ⟨ψ₂|H₁|ψ₂⟩ = T(ψ₂) + ∫v₁·n
    # e₁:    E_gs(v₁)     = T(ψ₁) + ∫v₁·n
    # Step A: rewrite: T(ψ₂) + ∫v₁·n > T(ψ₁) + ∫v₁·n
    ineq1_expanded = rewrite_gt_with_eqs(rr1, exp1_rw, e1)
    # Step B: cancel ∫v₁·n from both sides
    ineq1 = cancel_common_addend(ineq1_expanded)
    state = add_hyp(state, "ineq₁", ineq1)
    step("have ineq₁ (from rr₁ + exp₁ + e₁, cancel common term)",
         f"DERIVE: rewrite_gt_with_eqs(rr₁, exp₁, e₁) then cancel_common_addend()",
         show_prop(ineq1),
         f"Expanded: {show_prop(ineq1_expanded)}\n"
         f"  {G}  ✓ Cancel ∫v₁·ρ(Ψ_gs(v₁)) from both sides → {show_prop(ineq1)}")

    # ══════════════════════════════════════════════════════════════
    # Step 10: Derive ineq₂ — T(ψ₁) > T(ψ₂)
    # ══════════════════════════════════════════════════════════════
    # Same reasoning with v₂
    # exp₂ uses ρ(ψ₁) = n already (ρ(ψ₁) IS n)
    ineq2_expanded = rewrite_gt_with_eqs(rr2, exp2, e2_rw)
    ineq2 = cancel_common_addend(ineq2_expanded)
    state = add_hyp(state, "ineq₂", ineq2)
    step("have ineq₂ (from rr₂ + exp₂ + e₂, cancel common term)",
         f"DERIVE: same derivation for v₂ side",
         show_prop(ineq2),
         f"Expanded: {show_prop(ineq2_expanded)}\n"
         f"  {G}  ✓ Cancel ∫v₂·ρ(Ψ_gs(v₁)) from both sides → {show_prop(ineq2)}")

    # ══════════════════════════════════════════════════════════════
    # Step 11: DETECT CONTRADICTION
    # ══════════════════════════════════════════════════════════════
    is_contradiction = detect_contradiction(ineq1, ineq2)
    step("linarith  — detect_contradiction(ineq₁, ineq₂)",
         f"CHECK: is ineq₁ the reverse of ineq₂?",
         None,
         f"detect_contradiction returned: {is_contradiction}")

    assert is_contradiction, "Proof failed — no contradiction found!"

    # ── Show final state ──
    print(f"\n")
    show_state(state, colors)

    # ── Contradiction Box ──
    print(f"\n{RED}{BOLD}  ╔═══════════════════════════════════════════════════════════════╗")
    print(f"  ║  CONTRADICTION DETECTED!                                     ║")
    print(f"  ║                                                              ║")
    print(f"  ║  ineq₁:  {show_prop(ineq1):50s}  ║")
    print(f"  ║  ineq₂:  {show_prop(ineq2):50s}  ║")
    print(f"  ║                                                              ║")
    print(f"  ║  X > Y  AND  Y > X  is impossible.                          ║")
    print(f"  ║                                                              ║")
    print(f"  ║  Our assumption (same density) was wrong.                    ║")
    print(f"  ║  ∎  Hohenberg-Kohn Theorem 1 proved. ∎                      ║")
    print(f"  ╚═══════════════════════════════════════════════════════════════╝{R}")

    # ── What actually happened ──
    print(f"\n{BOLD}{C}  ── WHAT THE SIMULATION ACTUALLY DID ──────────────────────────{R}")
    print(f"""
  This was NOT a narration — every step performed real computation:

  {BOLD}1. axiom_energy_def(ψ, v){R} — BUILT the equation by constructing tuples:
     ("eq",
       ("app", "⟨ψ|H|ψ⟩", (ψ, v)),
       ("binop", "+", ("app", "T", (ψ,)), ("app", "∫v·n", (v, ("app","ρ",(ψ,))))))

  {BOLD}2. substitute(expr, old, new){R} — WALKED the tuple tree:
     Found ("app", "ρ", (Ψ_gs(v₂),)) inside the expression
     Replaced it with ("app", "ρ", (Ψ_gs(v₁),))

  {BOLD}3. rewrite_gt_with_eqs(gt, eq_l, eq_r){R} — DERIVED a new inequality:
     Verified the LHS/RHS of the equations match the inequality
     Substituted the RHS of each equation in

  {BOLD}4. cancel_common_addend(gt){R} — SIMPLIFIED:
     Checked both sides are (X + C) and (Y + C) with C equal
     Returned (X > Y)

  {BOLD}5. detect_contradiction(gt1, gt2){R} — VERIFIED:
     Checked gt1 = (X > Y) and gt2 = (Y > X)
     Confirmed: True → CONTRADICTION

  {D}Every function: tuples in → tuples out. Pure, verifiable, no magic.{R}
""")

    print(f"{BOLD}{C}  ── FUNCTIONAL PROGRAMMING CONCEPTS ──────────────────────────{R}")
    print(f"""
  {BOLD}1. PURE FUNCTIONS{R}            substitute(expr, old, new) → new_expr
  {BOLD}2. STRUCTURAL RECURSION{R}      substitute walks the tagged tuple tree
  {BOLD}3. HIGHER-ORDER FUNCTIONS{R}    axioms are functions that return propositions
  {BOLD}4. FUNCTION COMPOSITION{R}      proof = detect ∘ cancel ∘ rewrite ∘ sub ∘ axiom ∘ ...
  {BOLD}5. TAGGED TUPLES{R}            ("app", "T", (("app", "Ψ_gs", (("var","v₁"),)),))
  {BOLD}6. PATTERN MATCHING{R}         cancel_common_addend checks tuple structure
  {BOLD}7. IMMUTABILITY{R}             add_hyp returns new dict, original untouched
  {BOLD}8. DEEP EQUALITY{R}            Python's == on tuples = structural comparison
""")
    print(f"{BOLD}{B}{'═' * 72}")
    print(f"  QED ∎")
    print(f"{'═' * 72}{R}\n")


if __name__ == "__main__":
    run_hk_proof()
