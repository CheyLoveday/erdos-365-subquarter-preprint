import PaperTargets.DivisorGrowth
import Mathlib.FieldTheory.Perfect

/-! CF15 precise external Thue specialization, ALGEBRA AR10 and the retained
Stewart1991 primary pages795–796. The external statement remains a Prop premise.
For a form homogenized at its full affine degree, separability of the rational
affine section is the nonzero-discriminant condition. Signs/axes remain included. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- The adopted Stewart bound specialized to full-degree homogenizations.
Content1, characteristic-zero separability/nonzero discriminant, degree3..11,
nonzero signed level, primitive signed integer pairs and constant2800 are explicit.
This is the authorized external Thue input, always an explicit premise. -/
def StewartPrimitiveThue : Prop :=
  ∀ f : Polynomial ℤ, binaryContent (f.homogenize f.natDegree)=1 →
    (rationalPolynomial f).Separable → 3 ≤ f.natDegree → f.natDegree ≤ 11 →
    ∀ h : ℤ, h ≠ 0 → ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z (f.homogenize f.natDegree)=h) →
      S.card ≤ 2800*f.natDegree^(1+primeSupportCount h.natAbs)

/-- The fixed high factor selected by CF15 has the precise external-input
admissibility properties; they are derived from primitivity and irreducibility. -/
def CF15HighFactorThueAdmissibility : Prop :=
  ∀ f : Polynomial ℤ, f.IsPrimitive → Irreducible (rationalPolynomial f) → 3 ≤ f.natDegree →
    binaryContent (f.homogenize f.natDegree)=1 ∧
      (f.homogenize f.natDegree).IsHomogeneous f.natDegree ∧
      f.homogenize f.natDegree ≠ 0 ∧
      (f.homogenize f.natDegree).totalDegree=f.natDegree ∧
      (rationalPolynomial f).Separable

def CF15IrreducibleThueLevel : Prop :=
  StewartPrimitiveThue → ∀ f : Polynomial ℤ, f.IsPrimitive →
    Irreducible (rationalPolynomial f) → 3 ≤ f.natDegree → f.natDegree ≤ 11 →
    ∀ h : ℤ, h ≠ 0 → ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z (f.homogenize f.natDegree)=h) →
      S.card ≤ 2800*f.natDegree*f.natDegree^(primeSupportCount h.natAbs)

/-- A fixed high factor's nonzero signed value divides the admitted level.
Both signs and all divisor labels are charged; the form is not enumerated. -/
def CF15HighFactorLevelBudget : Prop :=
  StewartPrimitiveThue → ∀ (Q : SourcePolynomial) (f : Polynomial ℤ),
    f.IsPrimitive → Irreducible (rationalPolynomial f) → 3 ≤ f.natDegree →
    f.natDegree ≤ 11 → f.homogenize f.natDegree ∣ Q →
    ∀ h : ℤ, h ≠ 0 → ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z Q=h) →
      S.card ≤ 61600*divisorCount h.natAbs*f.natDegree^(primeSupportCount h.natAbs)

/-- A uniform fixed-level envelope for the two EXHAUSTIVELY selected factor
branches. The extra sum retains a single simple expression for later fixed-c
signed-gcd aggregation; no factor-selection/count conclusion is a premise. -/
def CF15SelectedFactorLevelBudget : Prop :=
  StewartPrimitiveThue → ∀ Q : SourcePolynomial, binaryFactorDispatch Q →
    ∀ h : ℤ, h ≠ 0 → ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z Q=h) →
      S.card ≤ 16*(divisorCount h.natAbs)^2+
        61600*divisorCount h.natAbs*11^(primeSupportCount h.natAbs)

/-- Select factors from the actual bounded graph before all nonzero signed
levels. The external theorem is the only premise beyond actual graph data. -/
def CF15ActualGraphLevelBudget : Prop :=
  StewartPrimitiveThue → ∀ (X : ℝ) (D A B : Polynomial ℤ), 32 ≤ X →
    boundedGraphData X D A B → 1 ≤ graphDegree A B → ∀ inverse : Bool,
      let Q := binaryPrimitivePart (graphPullback inverse A B)
      ∀ h : ℤ, h ≠ 0 → ∀ S : Finset (Fin 2 → ℤ),
        (∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z Q=h) →
        S.card ≤ 16*(divisorCount h.natAbs)^2+
          61600*divisorCount h.natAbs*11^(primeSupportCount h.natAbs)

end
end P0365Subquarter
