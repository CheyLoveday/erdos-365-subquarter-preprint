import PaperTargets.ClassCounts
import PaperTargets.FactorInventory
import PaperTargets.SingularCounts

/-! Connected CF17 source count on one original interval, before the still-open
coarse polynomial existence and global box/interval aggregation. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- All singular and smooth populations of one rationally irreducible curve
are counted on original starts; prime lists and labels are derived internally. -/
def CF17IrreducibleIntervalSourceCount : Prop :=
  StewartPrimitiveThue → ∀ (D : ℕ) (H C δ : ℝ), 0≤H → 0≤C → 0<δ → δ≤1 →
    ∀ ε : ℝ, 0<ε → ∃ X₀ K : ℝ, 32≤X₀ ∧ 0<K ∧ ∀ X ψ B E a : ℝ,
      X₀≤X → 0≤ψ → ψ≤2/3 → 0<B → 0<E → 0<a → B*E=X^ψ →
      ∀ F : SourcePolynomial, F.totalDegree≤D →
        Irreducible (rationalSourcePolynomial F) →
        (∀ e, |(F.coeff e:ℝ)|≤C*X^H) →
        ∀ (S : Finset ℕ) (b d u v : ℕ → ℕ),
          (∀ n ∈ S, PairSource n (b n) (d n) (u n) (v n)) →
          (∀ n ∈ S, actualRealBox X B E n (b n) (d n)) →
          (∀ n ∈ S, actualDirectInterval a (roundedHeight X ψ δ:ℝ) (b n) (d n)) →
          (∀ n ∈ S, polynomialValue F (sourcePoint (b n) (d n) (u n) (v n))=0) →
          (S.card:ℝ)≤K*roundedScale X ψ δ*X^ε

/-- Produce the actual primitive irreducible factor cover and sum the derived
curve bounds, uniformly before the supplied nonzero coarse polynomial. -/
def CF17CoarseIntervalSourceCount : Prop :=
  StewartPrimitiveThue → ∀ (D : ℕ) (H C δ : ℝ), 0≤H → 0≤C → 0<δ → δ≤1 →
    ∀ ε : ℝ, 0<ε → ∃ X₀ K : ℝ, 32≤X₀ ∧ 0<K ∧ ∀ X ψ B E a : ℝ,
      X₀≤X → 0≤ψ → ψ≤2/3 → 0<B → 0<E → 0<a → B*E=X^ψ →
      ∀ F : SourcePolynomial, F≠0 → F.totalDegree≤D →
        (∀ e, |(F.coeff e:ℝ)|≤C*X^H) →
        ∀ (S : Finset ℕ) (b d u v : ℕ → ℕ),
          (∀ n ∈ S, PairSource n (b n) (d n) (u n) (v n)) →
          (∀ n ∈ S, actualRealBox X B E n (b n) (d n)) →
          (∀ n ∈ S, actualDirectInterval a (roundedHeight X ψ δ:ℝ) (b n) (d n)) →
          (∀ n ∈ S, polynomialValue F (sourcePoint (b n) (d n) (u n) (v n))=0) →
          (S.card:ℝ)≤K*roundedScale X ψ δ*X^ε

end
end P0365Subquarter
