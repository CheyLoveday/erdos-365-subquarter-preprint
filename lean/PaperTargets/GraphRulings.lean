import PaperTargets.ClassRelations
import Mathlib.RingTheory.Polynomial.Content

/-! CF13 first connected stage: the actual bounded relation gives one bounded
integral graph plus at most three rulings, with all degenerate cases retained.
Source: corrected v3 ALGEBRA AR07, MATHEMATICS §6 / addendum B. Full homogeneous
resultant, evaluated gcd and corrected level/content application follow next. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

abbrev rationalPolynomial (P : Polynomial ℤ) : Polynomial ℚ := P.map (Int.castRingHom ℚ)
def integerPolynomialValue (P : Polynomial ℤ) (s : ℚ) : ℚ := (rationalPolynomial P).eval s

def graphSection (inverse : Bool) (G : SourcePolynomial) (t : Fin 2) : Polynomial ℤ :=
  ∑ k : Fin 4, Polynomial.monomial k.val
    (G.coeff (relationExponent inverse ⟨k.val+4*t.val,by omega⟩))

def rulingRoots (D : Polynomial ℤ) : Finset ℚ := (rationalPolynomial D).roots.toFinset

def boundedGraphData (X : ℝ) (D A B : Polynomial ℤ) : Prop :=
  D ≠ 0 ∧ D.IsPrimitive ∧ IsCoprime (rationalPolynomial A) (rationalPolynomial B) ∧
    D.natDegree ≤ 3 ∧ A.natDegree ≤ 3 ∧ B.natDegree ≤ 3 ∧
    ∀ P ∈ ({D,A,B} : Finset (Polynomial ℤ)), ∀ k, |(P.coeff k : ℝ)| ≤ X^(15:ℕ)

def graphRulingCase (inverse : Bool) (D A B : Polynomial ℤ) (z : Fin 2 → ℚ) : Prop :=
  let s := z (if inverse then 1 else 0)
  let t := z (if inverse then 0 else 1)
  s ∈ rulingRoots D ∨ (integerPolynomialValue B s ≠ 0 ∧ integerPolynomialValue A s ≠ 0 ∧
    t = integerPolynomialValue A s / integerPolynomialValue B s)

def CF13RelationSections : Prop :=
  ∀ (inverse : Bool) (X : ℝ) (G : SourcePolynomial), boundedSourceRelation inverse X G →
    let P := graphSection inverse G 0
    let Q := graphSection inverse G 1
    (P ≠ 0 ∨ Q ≠ 0) ∧ P.natDegree ≤ 3 ∧ Q.natDegree ≤ 3 ∧
    (∀ t : Fin 2, ∀ k, |((graphSection inverse G t).coeff k : ℝ)| ≤ X^(14:ℕ)) ∧
    ∀ z : Fin 2 → ℚ, polynomialValue G z =
      integerPolynomialValue P (z (if inverse then 1 else 0)) +
      z (if inverse then 0 else 1)*integerPolynomialValue Q (z (if inverse then 1 else 0))

/-- Actual primitive common factor and integral quotient pair; coprimality is
in Q[X], so integer scalar contents do not become false Bezout-unit premises. -/
def CF13PrimitiveGCDRemoval : Prop :=
  ∀ P Q : Polynomial ℤ, (P ≠ 0 ∨ Q ≠ 0) → ∃ D A B : Polynomial ℤ,
    D ≠ 0 ∧ D.IsPrimitive ∧ P = D*(-A) ∧ Q = D*B ∧
    IsCoprime (rationalPolynomial A) (rationalPolynomial B) ∧
    D.natDegree ≤ max P.natDegree Q.natDegree ∧
    A.natDegree ≤ P.natDegree ∧ B.natDegree ≤ Q.natDegree

/-- A genuine integer factor-height theorem, not an assumed height for the
chosen graph. The generic fixed-degree bound also supports later coarse factors. -/
def CF13IntegerFactorHeight : Prop :=
  ∀ (d : ℕ) (H : ℝ), 1 ≤ H → ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ d →
    (∀ k, |(P.coeff k : ℝ)| ≤ H) → ∀ A : Polynomial ℤ, A ∣ P →
      ∀ k, |(A.coeff k : ℝ)| ≤ (2:ℝ)^d * (d+1) * H

/-- Exact positive-partner dispatch: zero numerator/denominator leaves only
rulings; actual degree zero is a constant graph. No source is dropped. -/
def CF13GraphRulingDispatch : Prop :=
  ∀ P Q D A B : Polynomial ℤ, D ≠ 0 → P = D*(-A) → Q = D*B →
    IsCoprime (rationalPolynomial A) (rationalPolynomial B) → D.natDegree ≤ 3 →
    (rulingRoots D).card ≤ 3 ∧
    (∀ s t : ℚ, t ≠ 0 →
      (integerPolynomialValue P s+t*integerPolynomialValue Q s = 0 ↔
        s ∈ rulingRoots D ∨ (integerPolynomialValue B s ≠ 0 ∧
          integerPolynomialValue A s ≠ 0 ∧ t = integerPolynomialValue A s/integerPolynomialValue B s))) ∧
    ((A = 0 ∨ B = 0) → ∀ s t : ℚ, t ≠ 0 →
      integerPolynomialValue P s+t*integerPolynomialValue Q s = 0 → s ∈ rulingRoots D) ∧
    (max A.natDegree B.natDegree = 0 → ∀ s t : ℚ, t ≠ 0 →
      integerPolynomialValue P s+t*integerPolynomialValue Q s = 0 →
        s ∈ rulingRoots D ∨ t = (A.coeff 0 : ℚ)/(B.coeff 0 : ℚ))

def CF13ActualGraphRulingDecomposition : Prop :=
  ∀ (inverse : Bool) (X : ℝ) (G : SourcePolynomial), 32 ≤ X →
    boundedSourceRelation inverse X G → ∃ D A B : Polynomial ℤ,
      boundedGraphData X D A B ∧ (rulingRoots D).card ≤ 3 ∧
      ∀ n b d u v : ℕ, PairSource n b d u v →
        polynomialValue G (sourcePoint b d u v) = 0 →
          graphRulingCase inverse D A B (sourcePoint b d u v)

/-- One decomposition before the entire actual class, connected to CF12. -/
def CF13RoundedClassGraphRulings : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ X₀ : ℝ, 32 ≤ X₀ ∧
    ∀ X ψ B E a : ℝ, X₀ ≤ X → 0 ≤ ψ → ψ ≤ 2/3 →
      0 < B → 0 < E → 0 < a → B*E = X^ψ →
      ∀ (F : SourcePolynomial) (p : ℕ) (z₀ : Fin 2 → ZMod p)
        (ι : Type) (n b d u v : ι → ℕ), Nat.Prime p → roundedScale X ψ δ ≤ (p : ℝ) →
        (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
        (∀ i, actualRealBox X B E (n i) (b i) (d i)) →
        (∀ i, actualDirectInterval a (roundedHeight X ψ δ : ℝ) (b i) (d i)) →
        (∀ i, polynomialValue F (sourcePoint (b i) (d i) (u i) (v i)) = 0) →
        (∀ i, goodSourcePrime F (b i) (d i) (u i) (v i) p) →
        (∀ i, sourceReduction (b i) (d i) (u i) (v i) p = z₀) →
        ∃ D A B : Polynomial ℤ, boundedGraphData X D A B ∧ (rulingRoots D).card ≤ 3 ∧
          ∀ i : ι, graphRulingCase (selectedRealChart ψ) D A B
            (sourcePoint (b i) (d i) (u i) (v i))

end
end P0365Subquarter
