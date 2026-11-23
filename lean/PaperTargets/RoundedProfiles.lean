import PaperTargets.ExactProfiles
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Fin

/-! Separately frozen CF16/CF17 numerical rounding bridge. Mathematical source:
corrected v3 review/ANALYTIC.md A07–A08. The actual CF11 determinant estimate,
CF09/CF10 valuation and source/prime assignment remain independent obligations.
The uniform starting height precedes every profile, error index and prime. -/

namespace P0365Subquarter

noncomputable section

set_option autoImplicit false

def roundedHeight (x ψ δ : ℝ) : ℕ :=
  Nat.ceil (x ^ ((1 + δ) * profileM0 ψ))

def roundedScale (x ψ δ : ℝ) : ℝ :=
  x ^ (profileTheta + δ) / (roundedHeight x ψ δ : ℝ)

/-- Same five mixed-error terms, with actual integer height in the denominator.
`Real.rpow_natCast` gives correspondence to ordinary integral powers. -/
def roundedMixedTerm (x ψ δ : ℝ) (k : Fin 5) : ℝ :=
  x ^ (profileW ψ - (k.val : ℝ)) /
    (roundedHeight x ψ δ : ℝ) ^ (profileErrorWeight k : ℝ)

def CF16RoundedHeightBounds : Prop :=
  ∀ x ψ δ : ℝ, 1 ≤ x → 0 ≤ ψ → ψ ≤ 2 / 3 → 0 ≤ δ →
    let m := (1 + δ) * profileM0 ψ
    1 ≤ (roundedHeight x ψ δ : ℝ) ∧
      x ^ m ≤ (roundedHeight x ψ δ : ℝ) ∧
      (roundedHeight x ψ δ : ℝ) ≤ 2 * x ^ m

def CF17RoundedPrimeScale : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ x₀ : ℝ, 1 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ ψ : ℝ, 0 ≤ ψ → ψ ≤ 2 / 3 →
      x ^ profileRho ≤ roundedScale x ψ δ

/-- Uniform quantitative bound before absorbing any fixed determinant constant. -/
def CF17RoundedMixedTermBound : Prop :=
  ∀ x ψ δ : ℝ, 1 ≤ x → 0 ≤ ψ → ψ ≤ 2 / 3 → 0 < δ →
    ∀ k : Fin 5,
      roundedMixedTerm x ψ δ k ≤
        (2 : ℝ) ^ 16 * x ^ (-(25 * δ)) * roundedScale x ψ δ ^ (28 : ℕ)

/-- All five error terms, one height depending only on fixed slack and constant.
This does not assert that an actual determinant satisfies the CF11 estimate. -/
def CF17RoundedErrorAbsorption : Prop :=
  ∀ δ C : ℝ, 0 < δ → 0 ≤ C → ∃ x₀ : ℝ, 1 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ ψ : ℝ, 0 ≤ ψ → ψ ≤ 2 / 3 →
      C * (∑ k : Fin 5, roundedMixedTerm x ψ δ k) <
        roundedScale x ψ δ ^ (28 : ℕ)

end

end P0365Subquarter
