import PaperTargets.RootDeterminants
import PaperTargets.UpperHeightSources

/-! CF04 actual upper-height determinant cancellation. The scaled upper
heights retain the required ratio coupling, rather than individual prescribed
scale identities. Degree/slack selection and integer vanishing remain separate. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def rectangularHeightExponent (A C : ℕ) (B E U V : ℝ) : ℝ :=
  (Fintype.card (RectangularIndex A C):ℝ)/2*
    ((A:ℝ)*Real.log (B*E)+(C:ℝ)*Real.log (U*V))

/-- Positive row and column scale products have the symmetric leading height.
One fixed constant precedes all coordinates and scales, including unit sources. -/
def CF04RectangularScaleProducts : Prop :=
  ∀ A C : ℕ, ∃ K : ℝ, 1≤K ∧ ∀ B E U V t : ℝ,
    0<B → 0<E → 0<U → 0<V → 0<t → t≤2*(B/E) →
    V/U=(B/E)^(3/2:ℝ) → ∀ d u : RectangularIndex A C → ℕ,
      (∀ i, 0<d i ∧ 0<u i ∧ (d i:ℝ)≤E ∧ (u i:ℝ)≤U) →
        (∏ i, rectangularRowScale A C (d i) (u i))*
          (∏ j : RectangularIndex A C, rectangularColumnScale t j)≤
            K*Real.exp (rectangularHeightExponent A C B E U V)

/-- Original sources and boxes derive all four upper heights, the interval
cap and the ratio coupling, before applying the proved integer determinant bound. -/
def CF04ActualHeightDeterminant : Prop :=
  ∀ A C : ℕ, ∃ K : ℝ, 1≤K ∧ ∀ X M B E t : ℝ,
    1≤X → 1<M → M≤X → 0<B → 0<E → 0<t →
    ∀ n b d u v : RectangularIndex A C → ℕ,
      (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
      (∀ i, actualRealBox X B E (n i) (b i) (d i)) →
      (∀ i, actualDirectInterval t M (b i) (d i)) →
        |((rectangularSourceMatrix A C b d u v).det:ℝ)|≤K*Real.exp
          (rectangularHeightExponent A C (4*B) (4*E)
            (4*reussMultiplierScale X B) (4*reussMultiplierScale X E)-
          latticeDeterminantLower (Fintype.card (RectangularIndex A C))
            (Real.log M) (Real.log X))

end
end P0365Subquarter
