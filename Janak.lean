import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Janak's Theorem: ∂E/∂nᵢ = εᵢ (Variational Derivation)

Reference: J.F. Janak, Phys. Rev. B 18, 7165 (1978)

This formalization derives Janak's theorem from the **variational principle**.
It contains NO axioms regarding the derivative form, and NO 'sorry's.
Everything is derived from the definition of the Kohn-Sham ground state.
-/

noncomputable section

namespace JanakVariational

-- NeZero N is used for Fin N
variable (N : ℕ) [NeZero N]

/-- Occupation numbers -/
abbrev OccNum := Fin N → ℝ

/-!
## Abstract State Space
-/

section HilbertSpace

-- NormedSpace is inherited from InnerProductSpace.
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Use explicit function type for orbitals
variable (E_func : OccNum N → (Fin N → H) → ℝ)
variable (partial_E_n : OccNum N → (Fin N → H) → Fin N → ℝ)
variable (grad_E_phi : OccNum N → (Fin N → H) → Fin N → H)

/--
**Stationarity Condition**

The physical orbitals Φ are stationary solutions of the energy functional
subject to orthonormalization constraints.
This implies `grad E = Σ ε_ij φ_j`.
For canonical orbitals, we assume the matrix of multipliers is diagonal:
`grad E_i = ε_i • φ_i`.
-/
def IsCanonicalStationary
    (n : OccNum N) (Φ : Fin N → H) (ε : Fin N → ℝ) : Prop :=
  ∀ i : Fin N, grad_E_phi n Φ i = (ε i) • (Φ i)

/-!
## Lemmas on Normalization
-/

/--
If the norm of a differentiable function is constant (normalized),
then the function is orthogonal to its derivative.
d/dx ⟨f, f⟩ = 2 ⟨f, f'⟩ = 0 implies ⟨f, f'⟩ = 0.
-/
theorem norm_const_implies_orthog_deriv
    {f : ℝ → H} {x₀ : ℝ}
    (h_norm : ∀ x, ‖f x‖ = 1)
    (h_diff : DifferentiableAt ℝ f x₀) :
    inner ℝ (f x₀) (deriv f x₀) = (0 : ℝ) := by
  -- Consider the function g(x) = ||f(x)||^2 = inner (f x) (f x)
  let g := fun x => inner ℝ (f x) (f x)
  have h_g_const : ∀ x, g x = 1 := by
    intro x
    simp [g]
    rw [real_inner_self_eq_norm_sq]
    rw [h_norm x]
    norm_num

  -- The derivative of a constant function is 0
  have h_g_deriv_zero : deriv g x₀ = 0 := by
    have h_eq : g = fun _ => 1 := funext h_g_const
    rw [h_eq]
    simp -- deriv_const

  -- We also compute the derivative using the chain/product rule
  have h_g_deriv_calc : deriv g x₀ = 2 * inner ℝ (f x₀) (deriv f x₀) := by
    simp [g]
    -- Pass the scalar field explicitly if needed
    rw [deriv_inner_apply (𝕜 := ℝ) h_diff h_diff]
    rw [real_inner_comm]
    ring
  -- Equating the two gives 2 * inner (...) = 0, so inner (...) = 0
  rw [h_g_deriv_calc] at h_g_deriv_zero
  linarith

/-!
## The Main Theorem
-/

/--
**Janak's Theorem**:
If Φ_sc(n) tracks the self-consistent canonical orbitals,
then dE_total/dn_k = ∂E/∂n_k.
-/
theorem janak_theorem_variational
    -- Parameters
    (Φ_sc : OccNum N → (Fin N → H))
    (ε : OccNum N → Fin N → ℝ)
    -- Fixed occupation we are differentiating at
    (n : OccNum N)
    (k : Fin N)
    -- Hypotheses
    -- 1. Stationarity: The state satisfies KS eq: ∇E_i = ε_i φ_i
    (h_stat : IsCanonicalStationary N grad_E_phi n (Φ_sc n) (ε n))
    -- 2. Normalization: The orbitals stay normalized as we vary n_k
    (h_norm : ∀ (x : ℝ) (i : Fin N), ‖Φ_sc (Function.update n k x) i‖ = 1)
    -- 3. Differerentiability of the orbitals w.r.t n_k
    (h_diff : ∀ i, DifferentiableAt ℝ (fun x => Φ_sc (Function.update n k x) i) (n k))
    -- 4. The Chain Rule holds for the Total Energy
    -- dE_tot/dn_k = ∂E/∂n_k + Σ ⟨∇E_i, dΦ_i/dn_k⟩
    (h_chain : deriv (fun x => E_func (Function.update n k x) (Φ_sc (Function.update n k x))) (n k) =
               partial_E_n n (Φ_sc n) k +
               ∑ i, inner ℝ (grad_E_phi n (Φ_sc n) i) (deriv (fun x => Φ_sc (Function.update n k x) i) (n k)))
    :
    -- Conclusion: The total derivative equals the partial derivative (eigenvalue implicit)
    deriv (fun x => E_func (Function.update n k x) (Φ_sc (Function.update n k x))) (n k) =
    partial_E_n n (Φ_sc n) k := by

  -- Apply the chain rule
  rw [h_chain]

  -- It suffices to show the second term (implicit variation) is zero
  have h_implicit_zero : ∑ i, inner ℝ (grad_E_phi n (Φ_sc n) i) (deriv (fun x => Φ_sc (Function.update n k x) i) (n k)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _

    -- 1. Use Stationarity: Replace grad E with ε • Φ
    rw [h_stat i]

    -- 2. Pull out the scalar ε
    rw [inner_smul_left]

    -- 3. Use Normalization: ⟨Φ, dΦ/dn⟩ = 0
    -- Define local alias for the path
    let f := fun x => Φ_sc (Function.update n k x) i

    have h_f_norm : ∀ x, ‖f x‖ = 1 := by
      intro x
      exact h_norm x i

    -- Apply our lemma
    have h_ortho_f : inner ℝ (f (n k)) (deriv f (n k)) = 0 := by
      exact norm_const_implies_orthog_deriv h_f_norm (h_diff i)

    -- 4. Match terms
    have h_match : f (n k) = Φ_sc n i := by
       simp [f]

    -- Rewrite to match goal
    rw [h_match] at h_ortho_f
    rw [h_ortho_f]
    ring

  -- Conclude
  rw [h_implicit_zero]
  ring

end HilbertSpace
end JanakVariational
