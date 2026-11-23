import PaperTargets.PullbackGeometry
import Mathlib.NumberTheory.FLT.MasonStothers

/-! CF14 remaining stage, ALGEBRA AR09: prove the axis support screen before
using Mathlib's proved polynomial abc theorem. No new external abc input.
The exclusion below is stronger than needed: ANY homogeneous degree-one or
degree-two pure power is excluded, without an irreducibility hypothesis. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def binaryDehomogenize (G : SourcePolynomial) : Polynomial ℤ :=
  MvPolynomial.aeval ![(Polynomial.X:Polynomial ℤ),1] G

def mixedPullbackNonpowers (inverse : Bool) (A B : Polynomial ℤ) : Prop :=
  pullbackAxisGeometry inverse A B ∧
    ∀ (G : SourcePolynomial) (d k : ℕ) (c : ℤ), G.IsHomogeneous d → (d=1 ∨ d=2) →
      graphPullback inverse A B ≠ MvPolynomial.C c*G^k

/-- Full homogeneous degree is an upper bound for the affine section; exact
rehomogenization and nonvanishing are proved, including degree-zero/zero forms. -/
def CF14BinaryDehomogenization : Prop :=
  ∀ (G : SourcePolynomial) (d : ℕ), G.IsHomogeneous d →
    (binaryDehomogenize G).natDegree ≤ d ∧
    (binaryDehomogenize G).homogenize d=G ∧
    (G ≠ 0 → binaryDehomogenize G ≠ 0)

/-- A supposed small-degree pure power cannot carry an axis factor: its
multiplicity k exceeds the already proved actual axis bounds. This is derived
from the actual pullback identity, never assumed before abc. -/
def CF14SmallPowerAxisScreen : Prop :=
  ∀ A B : Polynomial ℤ, 1 ≤ graphDegree A B →
    IsCoprime (rationalPolynomial A) (rationalPolynomial B) →
    ∀ (inverse : Bool) (G : SourcePolynomial) (d k : ℕ) (c : ℤ),
      G.IsHomogeneous d → (d=1 ∨ d=2) → graphPullback inverse A B=MvPolynomial.C c*G^k →
      graphPullbackDegree inverse (graphDegree A B)=d*k ∧ c ≠ 0 ∧ G ≠ 0 ∧
      (if inverse then 2 else 3) < k ∧ (binaryDehomogenize G).natDegree=d ∧
      (binaryDehomogenize G).coeff 0 ≠ 0 ∧
      affineGraphPullback inverse A B=Polynomial.C c*(binaryDehomogenize G)^k

/-- Product/power radicals count each section and the coordinate at most once.
This is a proved upper bound for arbitrary nonnegative exponents. -/
def CF14RadicalSupportBound : Prop :=
  ∀ A B P : Polynomial ℚ, A ≠ 0 → B ≠ 0 → P ≠ 0 →
    ∀ c : ℚ, c ≠ 0 → ∀ e s t k : ℕ,
      (UniqueFactorizationMonoid.radical ((A^s)*(Polynomial.X^e*B^t)*(Polynomial.C c*P^k))).natDegree ≤
        A.natDegree+B.natDegree+1+P.natDegree

/-- The exact proved polynomial-abc consequence for the two original
summands. Nonzero constant term is the previously derived axis screen.
No abc, radical-support or summand-coprimality conclusion is supplied. -/
def CF14NonaxisABC : Prop :=
  ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 →
    IsCoprime (rationalPolynomial A) (rationalPolynomial B) →
    ∀ (inverse : Bool) (P : Polynomial ℤ) (c : ℤ) (k : ℕ), c ≠ 0 → 0 < k →
      P.coeff 0 ≠ 0 → affineGraphPullback inverse A B=Polynomial.C c*P^k →
      0 < (affineGraphPullback inverse A B).natDegree →
      (affineGraphPullback inverse A B).natDegree+1 ≤
        A.natDegree+B.natDegree+1+P.natDegree

/-- All actual positive graph degrees, both charts, all integer scalars and
all exponents, including zero. No irreducibility premise is needed. -/
def CF14HomogeneousSmallPowerExclusion : Prop :=
  ∀ A B : Polynomial ℤ, 1 ≤ graphDegree A B →
    IsCoprime (rationalPolynomial A) (rationalPolynomial B) →
    ∀ (inverse : Bool) (G : SourcePolynomial) (d k : ℕ) (c : ℤ),
      G.IsHomogeneous d → (d=1 ∨ d=2) → graphPullback inverse A B ≠ MvPolynomial.C c*G^k

def CF14ActualMixedNonpowers : Prop :=
  ∀ (X : ℝ) (D A B : Polynomial ℤ), 32 ≤ X → boundedGraphData X D A B →
    1 ≤ graphDegree A B → ∀ inverse : Bool,
      5 ≤ graphPullbackDegree inverse (graphDegree A B) ∧
      graphPullbackDegree inverse (graphDegree A B) ≤ (if inverse then 11 else 9) ∧
      mixedPullbackNonpowers inverse A B

/-- Finish CF14 at the same entire actual rounded class as CF11–13. Graph,
resultant, primitive pullback and its non-power property are fixed before all
members. Common-factor rulings and actual degree-zero graphs remain explicit. -/
def CF14RoundedClassNonpowers : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ X₀ : ℝ, 32 ≤ X₀ ∧
    ∀ X ψ B E a : ℝ, X₀ ≤ X → 0 ≤ ψ → ψ ≤ 2/3 →
      0 < B → 0 < E → 0 < a → B*E = X^ψ →
      ∀ (F : SourcePolynomial) (p : ℕ) (z₀ : Fin 2 → ZMod p)
        (ι : Type) (n b d u v : ι → ℕ), Nat.Prime p → roundedScale X ψ δ ≤ (p:ℝ) →
        (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
        (∀ i, actualRealBox X B E (n i) (b i) (d i)) →
        (∀ i, actualDirectInterval a (roundedHeight X ψ δ : ℝ) (b i) (d i)) →
        (∀ i, polynomialValue F (sourcePoint (b i) (d i) (u i) (v i)) = 0) →
        (∀ i, goodSourcePrime F (b i) (d i) (u i) (v i) p) →
        (∀ i, sourceReduction (b i) (d i) (u i) (v i) p = z₀) →
        ∃ D A C : Polynomial ℤ, boundedGraphData X D A C ∧ (rulingRoots D).card ≤ 3 ∧
          (∀ i, graphRulingCase (selectedRealChart ψ) D A C (sourcePoint (b i) (d i) (u i) (v i))) ∧
          (graphDegree A C = 0 ∨ (fullGraphResultant A C ≠ 0 ∧
            |(fullGraphResultant A C : ℝ)| ≤ 720*X^(90:ℕ) ∧
            mixedPullbackNonpowers (selectedRealChart ψ) A C ∧
            ∀ i : ι, (sourcePoint (b i) (d i) (u i) (v i)) (if selectedRealChart ψ then 1 else 0) ∈ rulingRoots D ∨
              (sourceGraphGCD (selectedRealChart ψ) A C (b i) (d i) (u i) (v i) ∣ (fullGraphResultant A C).natAbs ∧
                signedGraphRecovery (selectedRealChart ψ) A C (b i) (d i) (u i) (v i) ∧
                reducedGraphLevel (selectedRealChart ψ) A C (b i) (d i) (u i) (v i))))

end
end P0365Subquarter
