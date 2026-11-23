import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! CF04 finite lattice-weight ingredient for the remaining generic determinant
extension. Distinct exponent pairs are retained; numerical weight ties are
allowed. No determinant, covering or counting theorem is a premise. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Finite positive-part sums satisfy the triangular cubic bound by telescoping,
including empty rectangles. This is the lattice estimate, without integration. -/
def CF04PositivePartRectangle : Prop :=
  ∀ a b T : ℝ, 0<a → 0<b → 0≤T → ∀ N M : ℕ,
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
      max 0 (T-a*(i:ℝ)-b*(j:ℝ)))≤(T+a+b)^3/(6*a*b)

/-- Every finite set of exponent pairs obeys the unoptimized moment bound.
The finite rectangle is constructed internally; no sorted-weight premise. -/
def CF04FiniteWeightMoment : Prop :=
  ∀ a b : ℝ, 0<a → 0<b → ∀ S : Finset (ℕ×ℕ), ∀ T : ℝ, 0≤T →
    (S.card:ℝ)*T-(T+a+b)^3/(6*a*b)≤
      ∑ e ∈ S, (a*(e.1:ℝ)+b*(e.2:ℝ))

/-- Optimization gives the sharp leading constant with a retained linear
boundary error. The second conclusion bounds that error when a<=b, as needed
for a=log M,b=log X. Empty sets and numerical weight ties are included. -/
def CF04OptimizedWeightMoment : Prop :=
  ∀ a b : ℝ, 0<a → 0<b → ∀ S : Finset (ℕ×ℕ),
    (2/3)*(S.card:ℝ)*Real.sqrt (2*a*b*(S.card:ℝ))-(S.card:ℝ)*(a+b)≤
      (∑ e ∈ S, (a*(e.1:ℝ)+b*(e.2:ℝ))) ∧
    (a≤b → (2/3)*(S.card:ℝ)*Real.sqrt (2*a*b*(S.card:ℝ))-2*(S.card:ℝ)*b≤
      ∑ e ∈ S, (a*(e.1:ℝ)+b*(e.2:ℝ)))

end
end P0365Subquarter
