import PaperTargets.DividedMinors

/-! CF12, corrected v3 MATHEMATICS §4 / addendum B and ALGEBRA AR06.
One bounded integer relation for every row of the selected class, including
empty classes, fewer than eight rows, repetitions and every lower rank.
The final target consumes the proved actual localized CF11 application. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- The original monomial exponents, in the two original coordinate orders. -/
def relationExponent (inverse : Bool) (j : Fin 8) : Fin 2 →₀ ℕ :=
  Finsupp.single (if inverse then 1 else 0) (j.val % 4) +
    Finsupp.single (if inverse then 0 else 1) (if j.val < 4 then 0 else 1)

/-- Actual integral polynomial, not an abstract relation label. -/
def relationPolynomial (inverse : Bool) (c : Fin 8 → ℤ) : SourcePolynomial :=
  ∑ j : Fin 8, MvPolynomial.monomial (relationExponent inverse j) (c j)

/-- Both bidegree orientations, polynomial coefficient height and nonzero. -/
def boundedSourceRelation (inverse : Bool) (X : ℝ) (G : SourcePolynomial) : Prop :=
  G ≠ 0 ∧ (∀ e, |(G.coeff e : ℝ)| ≤ X ^ (14 : ℕ)) ∧
    ∀ e ∈ G.support, e (if inverse then 1 else 0) ≤ 3 ∧
      e (if inverse then 0 else 1) ≤ 1

/-- No rank-seven premise and no eight distinct available sources are required.
The coefficient bound is the seven-minor Leibniz bound, valid at every rank. -/
def CF12BoundedIntegerRelation : Prop :=
  ∀ (ι : Type) (A : ι → Fin 8 → ℤ) (H : ℝ), 1 ≤ H →
    (∀ i j, |(A i j : ℝ)| ≤ H) →
    (∀ f : Fin 8 → ι, Matrix.det (fun i j => A (f i) j) = 0) →
    ∃ c : Fin 8 → ℤ, c ≠ 0 ∧ (∀ j, |(c j : ℝ)| ≤ 5040 * H^7) ∧
      ∀ i : ι, ∑ j : Fin 8, A i j * c j = 0

/-- Uniform height of both ORIGINAL integer rows in the actual source shell. -/
def CF12SourceRowHeight : Prop :=
  ∀ (X : ℝ), 1 ≤ X → ∀ n b d u v : ℕ,
    PairSource n b d u v → (n : ℝ) ≤ 2*X → ∀ (inverse : Bool) (j : Fin 8),
      |(sourceIntegerRow inverse b d u v j : ℝ)| ≤ 9 * X^(11/6 : ℝ)

/-- Exact coefficient support and actual evaluation, preserving all columns. -/
def CF12RelationPolynomial : Prop :=
  ∀ (inverse : Bool) (c : Fin 8 → ℤ),
    (∀ j, (relationPolynomial inverse c).coeff (relationExponent inverse j) = c j) ∧
    (relationPolynomial inverse c = 0 ↔ c = 0) ∧
    (∀ e, (relationPolynomial inverse c).coeff e = 0 ∨
      ∃ j, e = relationExponent inverse j ∧ (relationPolynomial inverse c).coeff e = c j) ∧
    (∀ e ∈ (relationPolynomial inverse c).support,
      e (if inverse then 1 else 0) ≤ 3 ∧ e (if inverse then 0 else 1) ≤ 1) ∧
    ∀ z : Fin 2 → ℚ, polynomialValue (relationPolynomial inverse c) z =
      ∑ j : Fin 8, (c j : ℚ) * chartMonomial inverse z j

/-- Clearing positive actual denominators transfers the integer row relation
back to a polynomial on the original rational source point, in either chart. -/
def CF12SourceRelationEvaluation : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v → ∀ (inverse : Bool) (c : Fin 8 → ℤ),
    (∑ j : Fin 8, sourceIntegerRow inverse b d u v j * c j = 0) ↔
      polynomialValue (relationPolynomial inverse c) (sourcePoint b d u v) = 0

/-- One relation before ALL class members; uniform threshold before the class.
No input relation, full-rank hypothesis, coefficient census or basis is supplied. -/
def CF12ActualClassRelation : Prop :=
  ∃ X₀ : ℝ, 4 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ (ι : Type) (n b d u v : ι → ℕ),
      (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
      (∀ i, (n i : ℝ) ≤ 2*X) →
      ∀ inverse : Bool,
      (∀ f : Fin 8 → ι, Matrix.det (fun i j => sourceIntegerRow inverse
        (b (f i)) (d (f i)) (u (f i)) (v (f i)) j) = 0) →
      ∃ G : SourcePolynomial, boundedSourceRelation inverse X G ∧
        ∀ i : ι, polynomialValue G (sourcePoint (b i) (d i) (u i) (v i)) = 0

/-- Connected actual CF11-to-CF12 application, with no zero-minor premise.
A common residue is an explicit label, so no class centre is assumed to exist. -/
def CF12RoundedEntireClassRelation : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ X₀ : ℝ, 4 ≤ X₀ ∧
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
        ∃ G : SourcePolynomial, boundedSourceRelation (selectedRealChart ψ) X G ∧
          ∀ i : ι, polynomialValue G (sourcePoint (b i) (d i) (u i) (v i)) = 0

end
end P0365Subquarter
