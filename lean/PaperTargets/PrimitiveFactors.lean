import PaperTargets.ResultantDivisors
import Mathlib.RingTheory.Polynomial.Content

/-! CF15 preparation of the actual primitive homogeneous pullback for fixed
factor selection, ALGEBRA AR10. No factor inventory or Thue bound is assumed. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def CF15HomogeneousScalarCancellation : Prop :=
  ∀ (H Q : SourcePolynomial) (c : ℤ) (N : ℕ), c ≠ 0 →
    H=MvPolynomial.C c*Q → H.IsHomogeneous N → Q.IsHomogeneous N

/-- Homogeneous reconstruction preserves the coefficient gcd, including
forms carrying the infinity axis and homogeneous degree-zero forms. -/
def CF15PrimitiveDehomogenization : Prop :=
  ∀ (Q : SourcePolynomial) (N : ℕ), Q.IsHomogeneous N → binaryContent Q=1 →
    Q ≠ 0 ∧ (binaryDehomogenize Q).IsPrimitive ∧ binaryDehomogenize Q ≠ 0 ∧
      (binaryDehomogenize Q).natDegree ≤ N ∧ (binaryDehomogenize Q).homogenize N=Q

/-- Pad the affine homogenization by exactly the missing infinity degree.
This keeps repeated axis factors, instead of dropping them before dispatch. -/
def CF15HomogenizationPadding : Prop :=
  ∀ (P : Polynomial ℤ) (N : ℕ), P.natDegree ≤ N →
    P.homogenize N=P.homogenize P.natDegree*MvPolynomial.X 1^(N-P.natDegree)

/-- Every fixed integral affine factor of the primitive section lifts to an
actual homogeneous divisor, at its own full degree. -/
def CF15HomogeneousFactorLift : Prop :=
  ∀ (P f : Polynomial ℤ) (N : ℕ), P.IsPrimitive → f ∣ P → P.natDegree ≤ N →
    f.IsPrimitive ∧ f ≠ 0 ∧ f.natDegree ≤ N ∧
      (f.homogenize f.natDegree).IsHomogeneous f.natDegree ∧
      f.homogenize f.natDegree ∣ P.homogenize N

/-- Non-power exclusion descends through the actual integral content factor.
No irreducibility or unit-content hypothesis on the tested small form. -/
def CF15PrimitiveSmallPowerTransfer : Prop :=
  ∀ (H Q : SourcePolynomial) (c : ℤ), H=MvPolynomial.C c*Q →
    (∀ (G : SourcePolynomial) (d k : ℕ) (a : ℤ), G.IsHomogeneous d →
      (d=1 ∨ d=2) → H ≠ MvPolynomial.C a*G^k) →
    ∀ (G : SourcePolynomial) (d k : ℕ) (a : ℤ), G.IsHomogeneous d →
      (d=1 ∨ d=2) → Q ≠ MvPolynomial.C a*G^k

/-- Derive the constructed primitive section, all its fixed affine factor
lifts, degree at most11 and small-power exclusion from the ACTUAL graph.
Factor selection/irreducibility, precise Thue and point counts remain later. -/
def CF15ActualPrimitiveGraphFactors : Prop :=
  ∀ (X : ℝ) (D A B : Polynomial ℤ), 32 ≤ X → boundedGraphData X D A B →
    1 ≤ graphDegree A B → ∀ inverse : Bool,
      let H := graphPullback inverse A B
      let Q := binaryPrimitivePart H
      let N := graphPullbackDegree inverse (graphDegree A B)
      let P := binaryDehomogenize Q
      Q ≠ 0 ∧ binaryContent Q=1 ∧ Q.IsHomogeneous N ∧ 5 ≤ N ∧ N ≤ 11 ∧
        P.IsPrimitive ∧ P ≠ 0 ∧ P.natDegree ≤ N ∧ P.homogenize N=Q ∧
        (∀ (G : SourcePolynomial) (d k : ℕ) (a : ℤ), G.IsHomogeneous d →
          (d=1 ∨ d=2) → Q ≠ MvPolynomial.C a*G^k) ∧
        ∀ f : Polynomial ℤ, f ∣ P → f.IsPrimitive ∧ f ≠ 0 ∧ f.natDegree ≤ N ∧
          (f.homogenize f.natDegree).IsHomogeneous f.natDegree ∧
          f.homogenize f.natDegree ∣ Q

end
end P0365Subquarter
