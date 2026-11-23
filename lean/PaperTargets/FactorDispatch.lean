import PaperTargets.PrimitiveFactors
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-! CF15 fixed-factor selection, ALGEBRA AR10. Factors are selected once for
the constructed class polynomial before any primitive source/level labels. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def binaryFactorDispatch (Q : SourcePolynomial) : Prop :=
  (∃ G H : SourcePolynomial, lowBinaryFactorPair G H ∧ G ∣ Q ∧ H ∣ Q) ∨
    ∃ f : Polynomial ℤ, f.IsPrimitive ∧ Irreducible (rationalPolynomial f) ∧
      3 ≤ f.natDegree ∧ f.natDegree ≤ 11 ∧ f.homogenize f.natDegree ∣ Q

def CF15PrimitiveIrreducibleFactor : Prop :=
  ∀ P f : Polynomial ℤ, P.IsPrimitive → Irreducible f → f ∣ P →
    f.IsPrimitive ∧ 1 ≤ f.natDegree ∧ Irreducible (rationalPolynomial f)

/-- Distinct integral primitive irreducibles give the exact rational
nonproportionality predicates of LowFactorLevels, including unequal degrees. -/
def CF15DistinctLowFactorPair : Prop :=
  ∀ f g : Polynomial ℤ, f.IsPrimitive → g.IsPrimitive →
    Irreducible f → Irreducible g → ¬ Associated f g →
    (f.natDegree=1 ∨ f.natDegree=2) → (g.natDegree=1 ∨ g.natDegree=2) →
      lowBinaryFactorPair (f.homogenize f.natDegree) (g.homogenize g.natDegree)

/-- Full affine degree distinguishes every positive-degree lift from the
infinity axis, including its squared comparison against a quadratic lift. -/
def CF15InfinityLowFactorPair : Prop :=
  ∀ f : Polynomial ℤ, (f.natDegree=1 ∨ f.natDegree=2) →
    lowBinaryFactorPair (MvPolynomial.X 1) (f.homogenize f.natDegree)

/-- The factor alternatives follow from unique factorization and the proved
small-power exclusion. No factor-selection or count conclusion is a premise. -/
def CF15PrimitiveFactorDispatch : Prop :=
  ∀ (Q : SourcePolynomial) (N : ℕ), Q.IsHomogeneous N → binaryContent Q=1 → N ≤ 11 →
    (∀ (G : SourcePolynomial) (d k : ℕ) (a : ℤ), G.IsHomogeneous d →
      (d=1 ∨ d=2) → Q ≠ MvPolynomial.C a*G^k) → binaryFactorDispatch Q

/-- Select fixed factors of the actual primitive graph pullback in both
charts; sources, nonzero signed levels and the precise Thue bound follow later. -/
def CF15ActualGraphFactorDispatch : Prop :=
  ∀ (X : ℝ) (D A B : Polynomial ℤ), 32 ≤ X → boundedGraphData X D A B →
    1 ≤ graphDegree A B → ∀ inverse : Bool,
      binaryFactorDispatch (binaryPrimitivePart (graphPullback inverse A B))

end
end P0365Subquarter
