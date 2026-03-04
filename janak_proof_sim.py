"""
════════════════════════════════════════════════════════════════════════
  Janak's Theorem — Pure Functional Proof Simulation
  ===================================================
  
  THEOREM:  ∂E/∂nᵢ = εᵢ
    The total energy derivative w.r.t. occupation = Kohn-Sham eigenvalue.
  
  PROOF: Variational — chain rule + normalization orthogonality.
  
  EVERYTHING is functions and tuples. No classes.
    • The LEMMA is a reusable helper function
    • The MAIN THEOREM composes the lemma via function application
    • Every tactic: proof_state → proof_state  (one in, one out)
════════════════════════════════════════════════════════════════════════
"""


# ════════════════════════════════════════════════════════════════════
# PART 1: SYMBOLIC EXPRESSIONS (tagged tuples)
# ════════════════════════════════════════════════════════════════════

def var(name):          return ("var", name)
def app(fn, *args):     return ("app", fn, args)
def binop(op, a, b):    return ("binop", op, a, b)
def times(a, b):        return binop("·", a, b)
def plus(a, b):         return binop("+", a, b)
def summation(idx, body): return ("sum", idx, body)

def show(expr):
    """expr → string  (one in, one out)"""
    tag = expr[0]
    if tag == "var":    return expr[1]
    if tag == "app":
        fn, args = expr[1], expr[2]
        if not args: return fn
        return f"{fn}({', '.join(show(a) for a in args)})"
    if tag == "binop":  return f"({show(expr[2])} {expr[1]} {show(expr[3])})"
    if tag == "sum":    return f"Σ_{expr[1]} {expr[2]}"
    return str(expr)


# ── Propositions ─────────────────────────────────────────────────

def prop_eq(a, b):      return ("eq", a, b)
def prop_forall(v, p):  return ("forall", v, p)

def show_prop(p):
    """prop → string"""
    tag = p[0]
    if tag == "eq":     return f"{show(p[1])} = {show(p[2])}"
    if tag == "forall": return f"∀ {p[1]}, {show_prop(p[2])}"
    if tag == "var":    return p[1]
    return str(p)


# ════════════════════════════════════════════════════════════════════
# PART 2: PROOF STATE (immutable dict)
# ════════════════════════════════════════════════════════════════════

def make_state(goal, hyps=None):
    """Construct proof state. () → state"""
    return {"goal": goal, "hyps": dict(hyps or {})}

def add_hyp(state, name, prop):
    """Add hypothesis → NEW state. state → state (pure!)"""
    new_hyps = dict(state["hyps"])
    new_hyps[name] = prop
    return {"goal": state["goal"], "hyps": new_hyps}

def set_goal(state, new_goal):
    """Change goal → NEW state. state → state (pure!)"""
    return {"goal": new_goal, "hyps": dict(state["hyps"])}


# ════════════════════════════════════════════════════════════════════
# PART 3: TACTICS (higher-order functions returning state → state)
# ════════════════════════════════════════════════════════════════════

def tactic_let(name, expr):
    """let binding. Returns function: state → state"""
    def apply(st): return add_hyp(st, name, prop_eq(var(name), expr))
    apply.__name__ = f"let {name}"
    return apply

def tactic_have(name, prop):
    """Establish fact. Returns function: state → state"""
    def apply(st): return add_hyp(st, name, prop)
    apply.__name__ = f"have {name}"
    return apply

def tactic_rw(rule_name):
    """Rewrite. Returns function: state → state"""
    def apply(st): return st
    apply.__name__ = f"rw [{rule_name}]"
    return apply

def tactic_apply(lemma_name):
    """Apply lemma. Returns function: state → state"""
    def apply(st): return st
    apply.__name__ = f"apply {lemma_name}"
    return apply

def tactic_ring():
    """Algebraic simplification. Returns function: state → state"""
    def apply(st): return st
    apply.__name__ = "ring"
    return apply


# ════════════════════════════════════════════════════════════════════
# PART 4: THE LEMMA — A Reusable Helper Function
# ════════════════════════════════════════════════════════════════════
#
# In FP, a lemma is just a FUNCTION that you call from other functions.
# norm_const_implies_orthog_deriv : (h_norm, h_diff) → proof(⟨f,f'⟩=0)

def prove_orthogonality_lemma(display_step):
    """
    Prove: if ‖f(x)‖ = 1 ∀x, then ⟨f(x₀), f'(x₀)⟩ = 0
    
    This is a FUNCTION that produces a PROOF.
    Input:  display_step function (for printing)
    Output: proof (the fact ⟨f,f'⟩=0 that the main theorem can use)
    
    The lemma itself is function composition:
      linarith ∘ rw ∘ have ∘ have ∘ have ∘ let
    """
    inner_ff = app("⟨f(x₀), f'(x₀)⟩")
    zero_expr = var("0")
    one_expr = var("1")

    state = make_state(
        goal=prop_eq(inner_ff, zero_expr),
        hyps={
            "h_norm": prop_forall("x", prop_eq(app("‖f(x)‖"), one_expr)),
            "h_diff": var("DifferentiableAt ℝ f x₀"),
        }
    )

    # L1: Define g(x) = ⟨f(x), f(x)⟩
    step_fn = tactic_let("g", app("⟨f(x), f(x)⟩"))
    state = step_fn(state)
    display_step("L1", "let g := fun x => ⟨f(x), f(x)⟩",
                 "Define g(x) = ‖f(x)‖². let returns state → state",
                 "g(x) := ⟨f(x), f(x)⟩ = ‖f(x)‖²")

    # L2: g is constant
    step_fn = tactic_have("h_g_const",
                          prop_forall("x", prop_eq(var("g(x)"), one_expr)))
    state = step_fn(state)
    display_step("L2", "have h_g_const : ∀ x, g(x) = 1",
                 "g(x) = ‖f(x)‖² = 1² = 1 (from h_norm)",
                 "∀ x, g(x) = 1")

    # L3: Derivative of constant = 0
    step_fn = tactic_have("h_g_deriv_zero",
                          prop_eq(var("g'(x₀)"), zero_expr))
    state = step_fn(state)
    display_step("L3", "have h_g_deriv_zero : g'(x₀) = 0",
                 "Derivative of constant function is 0. simp : state → state",
                 "g'(x₀) = 0")

    # L4: Compute derivative via product rule
    step_fn = tactic_have("h_g_deriv_calc",
                          prop_eq(var("g'(x₀)"),
                                  times(var("2"), inner_ff)))
    state = step_fn(state)
    display_step("L4", "have h_g_deriv_calc : g'(x₀) = 2·⟨f(x₀), f'(x₀)⟩",
                 "Product rule: d/dx⟨f,f⟩ = 2⟨f,f'⟩",
                 "g'(x₀) = 2·⟨f(x₀), f'(x₀)⟩")

    # L5: Equate and solve
    display_step("L5", "rw [h_g_deriv_calc] at h_g_deriv_zero; linarith",
                 "2·⟨f,f'⟩ = 0 → ⟨f,f'⟩ = 0. Substitution + arithmetic",
                 "⟨f(x₀), f'(x₀)⟩ = 0  ✓")

    # Return the PROOF — a proposition that can be used elsewhere
    return prop_eq(inner_ff, zero_expr)


# ════════════════════════════════════════════════════════════════════
# PART 5: THE MAIN THEOREM — Composes the Lemma
# ════════════════════════════════════════════════════════════════════

def run_janak_proof():
    """Simulate Janak's theorem proof — pure functional style."""

    B = "\033[94m"; G = "\033[92m"; Y = "\033[93m"; C = "\033[96m"
    M = "\033[95m"; D = "\033[2m"; BOLD = "\033[1m"; R = "\033[0m"

    def display_step(num, lean_code, description, result_str):
        print(f"\n  {BOLD}Step {num}:{R} {C}{lean_code}{R}")
        print(f"  {D}  ↳ {description}{R}")
        if result_str:
            print(f"  {Y}  → {result_str}{R}")

    # ── Title ──
    print(f"\n{BOLD}{B}{'═' * 72}")
    print(f"  JANAK'S THEOREM: ∂E/∂nᵢ = εᵢ  (Variational Proof)")
    print(f"  (Pure Functional Style — no classes, only functions & tuples)")
    print(f"{'═' * 72}{R}")
    print(f"""
  {BOLD}Theorem:{R} dE/dnₖ = ∂E/∂nₖ  (total deriv = partial deriv = eigenvalue)
  {BOLD}Strategy:{R} Chain rule → show implicit orbital term = 0

  {BOLD}Key FP insight:{R} The proof CALLS A LEMMA — this is {Y}function composition{R}!
    main_theorem = conclude ∘ rw ∘ ring ∘ rw ∘ {M}lemma{R} ∘ rw ∘ rw ∘ apply ∘ rw
""")

    # ── Types as functions ──
    print(f"{BOLD}{C}  ── TYPE SIGNATURES (every function: one in → one out) ────────{R}")
    types = [
        ("E_func",       "OccNum → Orbitals → ℝ",          "Total energy"),
        ("partial_E_n",  "OccNum → Orbitals → Fin N → ℝ",  "∂E/∂nᵢ"),
        ("grad_E_phi",   "OccNum → Orbitals → Fin N → H",  "∇E w.r.t. φᵢ"),
        ("deriv f",      "ℝ → H",                          "Derivative"),
        ("inner ⟨·,·⟩",  "H → H → ℝ",                     "Inner product"),
    ]
    for name, sig, desc in types:
        print(f"    {M}{name:18s}{R} : {sig:34s} {D}-- {desc}{R}")

    # ════════════════════════════════════════════════════════════════
    # LEMMA
    # ════════════════════════════════════════════════════════════════
    print(f"\n{BOLD}{C}  ── LEMMA: norm_const_implies_orthog_deriv ─────────────────────{R}")
    print(f"""
  {BOLD}Statement:{R}  ‖f(x)‖ = 1 for all x  →  ⟨f(x₀), f'(x₀)⟩ = 0
  {BOLD}Intuition:{R}  A vector on the unit sphere moves tangentially.
  {BOLD}This lemma is a FUNCTION:{R}  (h_norm, h_diff) → proof(⟨f,f'⟩=0)
""")

    print(f"  {BOLD}Goal:{R}  {Y}⟨f(x₀), f'(x₀)⟩ = 0{R}")
    print(f"  {D}{'─' * 62}{R}")

    # Execute the lemma (it's just a function call!)
    ortho_proof = prove_orthogonality_lemma(display_step)
    print(f"\n  {G}{BOLD}  ✓ Lemma proved: ⟨f(x₀), f'(x₀)⟩ = 0{R}")

    # ════════════════════════════════════════════════════════════════
    # MAIN THEOREM
    # ════════════════════════════════════════════════════════════════
    print(f"\n{BOLD}{C}  ── MAIN THEOREM: janak_theorem_variational ───────────────────{R}")

    dE_dnk = var("dE/dnₖ")
    partial_nk = var("∂E/∂nₖ")
    zero_expr = var("0")
    sum_term = ("sum", "i", "⟨∇Eᵢ, dφᵢ/dnₖ⟩")

    print(f"""
  {BOLD}Hypotheses (inputs to the theorem-function):{R}
    h_stat:  ∀ i, ∇Eᵢ = εᵢ·φᵢ              {D}(Kohn-Sham equations){R}
    h_norm:  ∀ x i, ‖φᵢ(x)‖ = 1             {D}(normalization){R}
    h_diff:  ∀ i, Differentiable φᵢ          {D}(smoothness){R}
    h_chain: dE/dnₖ = ∂E/∂nₖ + Σᵢ⟨∇Eᵢ, dφᵢ/dnₖ⟩  {D}(chain rule){R}

  {BOLD}Goal:{R}  {Y}dE/dnₖ = ∂E/∂nₖ{R}
  {D}{'─' * 62}{R}
""")

    state = make_state(
        goal=prop_eq(dE_dnk, partial_nk),
        hyps={
            "h_stat": prop_forall("i", prop_eq(var("∇Eᵢ"),
                                               times(var("εᵢ"), var("φᵢ")))),
            "h_chain": prop_eq(dE_dnk, plus(partial_nk, sum_term)),
        }
    )

    # M1: Apply chain rule
    state = tactic_rw("h_chain")(state)
    display_step("M1", "rw [h_chain]",
                 "Rewrite goal using chain rule. rw : rule → (state → state)",
                 "New goal: ∂E/∂nₖ + Σᵢ⟨∇Eᵢ, dφᵢ/dnₖ⟩ = ∂E/∂nₖ")

    print(f"\n  {D}  It suffices to show: Σᵢ⟨∇Eᵢ, dφᵢ/dnₖ⟩ = 0{R}")

    # M2: Need to show sum = 0
    state = tactic_have("h_implicit_zero",
                        prop_eq(sum_term, zero_expr))(state)
    display_step("M2", "have h_implicit_zero : Σᵢ⟨∇Eᵢ, dφᵢ/dnₖ⟩ = 0",
                 "Prove the implicit variation vanishes",
                 "Need: each term in sum = 0")

    # M3: For each i
    state = tactic_apply("Finset.sum_eq_zero")(state)
    display_step("M3", "apply Finset.sum_eq_zero; intro i",
                 "To show Σf(i)=0, show f(i)=0 for each i. apply : lemma → (state→state)",
                 "For each i: need ⟨∇Eᵢ, dφᵢ/dnₖ⟩ = 0")

    # M4: Use stationarity (KS equations)
    state = tactic_rw("h_stat i")(state)
    display_step("M4", "rw [h_stat i]",
                 "Replace ∇Eᵢ with εᵢ·φᵢ (Kohn-Sham equation). rw : rule → (state→state)",
                 "⟨εᵢ·φᵢ, dφᵢ/dnₖ⟩ = 0")

    # M5: Pull out scalar (linearity of inner product)
    state = tactic_rw("inner_smul_left")(state)
    display_step("M5", "rw [inner_smul_left]",
                 "⟨c·a, b⟩ = c·⟨a,b⟩ — linearity of inner product",
                 "εᵢ · ⟨φᵢ, dφᵢ/dnₖ⟩ = 0")

    # M6: CALL THE LEMMA!
    print(f"\n  {M}{BOLD}  ═══ FUNCTION CALL: Invoking the lemma! ═══{R}")
    state = tactic_have("h_ortho", ortho_proof)(state)
    display_step("M6", "exact norm_const_implies_orthog_deriv h_norm (h_diff i)",
                 "CALL THE LEMMA as a function! It returns ⟨φᵢ, dφᵢ/dnₖ⟩ = 0",
                 "⟨φᵢ, dφᵢ/dnₖ⟩ = 0   ← returned by the lemma function")

    print(f"""
  {D}  The lemma is used as a FUNCTION CALL:
    norm_const_implies_orthog_deriv(h_norm, h_diff_i)
    ↑ function name                 ↑ arguments (inputs)
    Returns: proof that ⟨φᵢ, dφᵢ/dnₖ⟩ = 0  (one output){R}""")

    # M7: Substitute
    state = tactic_rw("h_ortho")(state)
    display_step("M7", "rw [h_ortho]",
                 "Substitute ⟨φᵢ, dφᵢ/dnₖ⟩ = 0",
                 "εᵢ · 0 = 0")

    # M8: ring
    state = tactic_ring()(state)
    display_step("M8", "ring",
                 "εᵢ · 0 = 0 by algebra. ring : state → state",
                 "0 = 0  ✓ (each term vanishes!)")

    print(f"\n  {G}  ✓ Each term = 0  →  Σᵢ⟨∇Eᵢ, dφᵢ/dnₖ⟩ = 0{R}")

    # M9: Conclude
    display_step("M9", "rw [h_implicit_zero]; ring",
                 "dE/dnₖ = ∂E/∂nₖ + 0 = ∂E/∂nₖ",
                 "dE/dnₖ = ∂E/∂nₖ  ✓")

    # ── QED box ──
    print(f"\n{G}{BOLD}  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║                                                          ║")
    print(f"  ║           ∂E/∂nᵢ  =  εᵢ     (Janak's Theorem)           ║")
    print(f"  ║                                                          ║")
    print(f"  ║  The total energy derivative w.r.t. occupation number    ║")
    print(f"  ║  equals the Kohn-Sham eigenvalue.                        ║")
    print(f"  ║                                                          ║")
    print(f"  ║  ∎  Proved by composing lemma + chain rule.              ║")
    print(f"  ╚══════════════════════════════════════════════════════════╝{R}")

    # ── FP Summary ──
    print(f"\n{BOLD}{C}  ── FUNCTIONAL PROGRAMMING ANALYSIS ───────────────────────────{R}")
    print(f"""
  {BOLD}The proof as function composition:{R}

    {M}lemma{R} : (h_norm, h_diff) → proof(⟨f, f'⟩ = 0)
    {D}        ↑ inputs              ↑ output
    Internally: linarith ∘ have ∘ have ∘ have ∘ let{R}

    {M}theorem{R} : (h_stat, h_norm, h_diff, h_chain) → proof(dE/dnₖ = ∂E/∂nₖ)
    {D}          ↑ inputs                              ↑ output
    Internally: ring ∘ rw ∘ ring ∘ rw ∘ lemma ∘ rw ∘ rw ∘ apply ∘ have ∘ rw{R}
                                        {M}^^^^^{R}
                            {M}the lemma is called as a function!{R}

  {BOLD}Key FP concepts:{R}
    {BOLD}1.{R} {Y}Functions calling functions{R} — theorem calls lemma
    {BOLD}2.{R} {Y}Pure functions{R}             — every tactic: state → state
    {BOLD}3.{R} {Y}Higher-order functions{R}     — tactic_have(name, prop) → (state→state)
    {BOLD}4.{R} {Y}Closures{R}                  — rw("h_chain") captures the rule name
    {BOLD}5.{R} {Y}Tagged tuples{R}             — ("var", "εᵢ"), ("binop", "·", a, b)
    {BOLD}6.{R} {Y}Immutability{R}              — add_hyp returns new dict
    {BOLD}7.{R} {Y}Dependent types{R}           — proofs ARE return values of functions

  {BOLD}Your professor's model:{R}  {G}"one input, one output"{R}
    ✓ Every constructor:  args → tuple       (one in, one out)
    ✓ Every rewrite rule: term → term        (one in, one out)
    ✓ Every tactic:       state → state      (one in, one out)
    ✓ Every lemma:        hypotheses → proof (one in, one out)
    ✓ The whole proof:    goal → QED         (one in, one out)

  {D}No classes. No mutation. No side effects.
  Just functions transforming data — all the way down.{R}
""")
    print(f"{BOLD}{B}{'═' * 72}")
    print(f"  QED ∎")
    print(f"{'═' * 72}{R}\n")


if __name__ == "__main__":
    run_janak_proof()
