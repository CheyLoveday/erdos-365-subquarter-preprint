import PaperTargets.UniformRectangles
import PaperTargets.ClassRelations

/-! CF04: variable-size bounded integer relation and the actual coarse
polynomial producer. Constants precede height, profile, box and population.
This is the special k=3,l=2 internal route, not general Reuss Lemma 7. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- All ranks, including an empty population and H=1. No basis is supplied. -/
def CF04GenericBoundedIntegerRelation : Prop :=
  ∀ H : ℕ, 1≤H → ∀ (ι : Type) (A : ι → Fin H → ℤ) (L : ℝ),
    1≤L → (∀ i j, |(A i j:ℝ)|≤L) →
    (∀ f : Fin H → ι, (Matrix.of (fun i j => A (f i) j)).det=0) →
    ∃ c : Fin H → ℤ, c≠0 ∧
      (∀ j, |(c j:ℝ)|≤((H-1).factorial:ℝ)*L^(H-1)) ∧
      ∀ i : ι, ∑ j : Fin H, A i j*c j=0

/-- Actual original source/closed-interval polynomial, with degree and height
uniform before every varying parameter. No input polynomial, determinant or
rank hypothesis remains. Empty populations and unit coordinates are included. -/
def CF04ActualUniformCoarsePolynomial : Prop :=
  ∀ δ : ℝ, 0<δ → δ≤1 → ∃ D N : ℕ, 1≤D ∧
    ∃ K X₀ : ℝ, 0<K ∧ 32≤X₀ ∧
      ∀ X ψ B E t : ℝ, X₀≤X →
        profileTheta/2≤ψ → ψ≤(2/3)*(1-profileTheta/2) →
        0<B → 0<E → 0<t → B*E=X^ψ →
        ∀ (S : Finset ℕ) (b d u v : ℕ → ℕ),
          (∀ n ∈ S, PairSource n (b n) (d n) (u n) (v n)) →
          (∀ n ∈ S, actualRealBox X B E n (b n) (d n)) →
          (∀ n ∈ S, actualDirectInterval t (roundedHeight X ψ δ:ℝ) (b n) (d n)) →
          ∃ F : SourcePolynomial, F≠0 ∧ F.totalDegree≤D ∧
            (∀ e, |(F.coeff e:ℝ)|≤K*X^N) ∧
            ∀ n ∈ S, polynomialValue F (sourcePoint (b n) (d n) (u n) (v n))=0

end
end P0365Subquarter
