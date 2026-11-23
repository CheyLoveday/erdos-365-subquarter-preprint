import PaperTargets.GraphRulings
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! CF13 homogeneous-resultant stage, corrected v3 ALGEBRA AR07.
The full Sylvester degrees are both the actual common graph degree. Both
homogeneous adjugate identities retain the axis parameters. Signed recovery
and corrected admitted-level polynomial content are the following stage. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def graphDegree (A B : Polynomial ℤ) : ℕ := max A.natDegree B.natDegree

def homogeneousGraphValue (P : Polynomial ℤ) (r : ℕ) (x y : ℤ) : ℤ :=
  MvPolynomial.eval ![x,y] (P.homogenize r)

def fullGraphResultant (A B : Polynomial ℤ) : ℤ :=
  Polynomial.resultant A B (graphDegree A B) (graphDegree A B)

def CF13HomogeneousForm : Prop :=
  ∀ (P : Polynomial ℤ) (r : ℕ), P.natDegree ≤ r →
    (P.homogenize r).IsHomogeneous r ∧
    (∀ x y : ℚ, y ≠ 0 → polynomialValue (P.homogenize r) ![x,y] =
      integerPolynomialValue P (x/y)*y^r) ∧
    ∀ x : ℚ, polynomialValue (P.homogenize r) ![x,0] = (P.coeff r : ℚ)*x^r

/-- Actual maximum degree is explicit; padding two constants to degree one
would give a common root at infinity and a zero resultant. -/
def CF13FullResultantNonzero : Prop :=
  ∀ A B : Polynomial ℤ, 1 ≤ graphDegree A B →
    IsCoprime (rationalPolynomial A) (rationalPolynomial B) → fullGraphResultant A B ≠ 0

/-- Integral homogeneous adjugate identities. No coprimality or nonzero
resultant is needed to construct the identities themselves. -/
def CF13HomogeneousBezout : Prop :=
  ∀ (A B : Polynomial ℤ) (r : ℕ), 1 ≤ r → A.natDegree ≤ r → B.natDegree ≤ r →
    ∃ L₁ L₂ L₃ L₄ : SourcePolynomial,
      L₁.IsHomogeneous (r-1) ∧ L₂.IsHomogeneous (r-1) ∧
      L₃.IsHomogeneous (r-1) ∧ L₄.IsHomogeneous (r-1) ∧
      MvPolynomial.C (Polynomial.resultant A B r r)*MvPolynomial.X 0^(2*r-1) =
        L₁*A.homogenize r+L₂*B.homogenize r ∧
      MvPolynomial.C (Polynomial.resultant A B r r)*MvPolynomial.X 1^(2*r-1) =
        L₃*A.homogenize r+L₄*B.homogenize r

/-- Primitive signed parameters, including both axes, and the signed full
resultant. The gcd uses absolute values through Int.gcd. -/
def CF13EvaluatedGCD : Prop :=
  ∀ (A B : Polynomial ℤ) (r : ℕ), 1 ≤ r → A.natDegree ≤ r → B.natDegree ≤ r →
    ∀ x y : ℤ, IsCoprime x y →
      (Int.gcd (homogeneousGraphValue A r x y) (homogeneousGraphValue B r x y) : ℤ) ∣
        Polynomial.resultant A B r r

def CF13ResultantHeight : Prop :=
  ∀ (A B : Polynomial ℤ) (r : ℕ) (H : ℝ), 0 ≤ H →
    (∀ k, |(A.coeff k : ℝ)| ≤ H) → (∀ k, |(B.coeff k : ℝ)| ≤ H) →
    |((Polynomial.resultant A B r r : ℤ) : ℝ)| ≤ ((2*r).factorial : ℝ)*H^(2*r)

/-- The resultant is fixed by the one actual graph, before all primitive
parameters. Its polynomial height follows from the proved graph coefficient
bound; no resultant, gcd or height premise is supplied. -/
def CF13ActualMixedResultant : Prop :=
  ∀ (X : ℝ) (D A B : Polynomial ℤ), 32 ≤ X → boundedGraphData X D A B →
    1 ≤ graphDegree A B → fullGraphResultant A B ≠ 0 ∧
      |(fullGraphResultant A B : ℝ)| ≤ 720*X^(90:ℕ) ∧
      ∀ x y : ℤ, IsCoprime x y →
        (Int.gcd (homogeneousGraphValue A (graphDegree A B) x y)
          (homogeneousGraphValue B (graphDegree A B) x y) : ℤ) ∣ fullGraphResultant A B

end
end P0365Subquarter
