import PaperTargets.FactorDispatch
import Mathlib.Analysis.SpecificLimits.Normed

/-! CF15 standard divisor subpower estimates are proved locally, not added
as external inputs. Source ALGEBRA AR10 and the actual720X^90 resultant height. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def CF15PolynomialExponentialBound : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, 1 ≤ C ∧ ∀ e : ℕ, (e+1)^k ≤ C*2^e

/-- An integer-power version avoids analytic products over valuations.
The constant is uniform in n, including the unit and k=0. -/
def CF15DivisorPowerGrowth : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → (divisorCount n)^k ≤ C*n

def CF15DivisorSubpower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
    (divisorCount n:ℝ) ≤ C*(n:ℝ)^ε

def CF15PolynomialHeightDivisorGrowth : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 32 ≤ X →
    ∀ R : ℕ, R ≠ 0 → (R:ℝ) ≤ 720*X^(90:ℕ) →
      (divisorCount R:ℝ)^8 ≤ C*X^ε

/-- The actual graph supplies the nonzero full resultant and polynomial
height. Neither an arbitrary divisor budget nor a count conclusion is given. -/
def CF15ActualGraphDivisorGrowth : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (X : ℝ) (D A B : Polynomial ℤ), 32 ≤ X → boundedGraphData X D A B →
      1 ≤ graphDegree A B →
        (fullGraphResultant A B).natAbs ≠ 0 ∧
        (divisorCount (fullGraphResultant A B).natAbs:ℝ)^8 ≤ C*X^ε

end
end P0365Subquarter
