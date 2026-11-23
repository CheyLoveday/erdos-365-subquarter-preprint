import PaperTargets.GenericCoarse
import PaperTargets.IntervalCounts
import PaperTargets.IntervalCover
import PaperTargets.ResidualProfiles
import PaperTargets.SmallKernelScale
import PaperTargets.SmallMultipliers

/-! CF17: actual original-source box counts. The coarse polynomials and one
common interval family are constructed internally; Stewart stays explicit. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Sum produced-polynomial interval counts through one common rounded cover.
The selected route is the conservative M*T*X^epsilon bound. -/
def CF17CompactBoxSourceCount : Prop :=
  StewartPrimitiveThue → ∀ δ ε : ℝ, 0<δ → δ≤1 → 0<ε →
    ∃ X₀ K : ℝ, 32≤X₀ ∧ 0<K ∧
      ∀ X ψ B E : ℝ, X₀≤X →
        profileTheta/2≤ψ → ψ≤(2/3)*(1-profileTheta/2) →
        0<B → 0<E → B*E=X^ψ →
        ∀ (S : Finset ℕ) (b d u v : ℕ → ℕ),
          (∀ n∈S,PairSource n (b n) (d n) (u n) (v n)) →
          (∀ n∈S,actualRealBox X B E n (b n) (d n)) →
          (S.card:ℝ)≤K*X^(profileTheta+δ+ε)

/-- A single actual residual source gives the common box profile. Empty
populations are handled separately, with no source-existence premise. -/
def CF17ResidualBoxSourceCount : Prop :=
  StewartPrimitiveThue → ∀ δ ε : ℝ, 0<δ → δ≤1 → 0<ε →
    ∃ X₀ K : ℝ, 32≤X₀ ∧ 0<K ∧
      ∀ X B E : ℝ, X₀≤X → 0<B → 0<E →
        ∀ (S : Finset ℕ) (b d u v : ℕ → ℕ),
          (∀ n∈S,PairSource n (b n) (d n) (u n) (v n)) →
          (∀ n∈S,actualRealBox X B E n (b n) (d n)) →
          (∀ n∈S,X^profileTheta<(b n*d n:ℝ)) →
          (∀ n∈S,X^profileTheta<(u n*v n:ℝ)) →
          (S.card:ℝ)≤K*X^(profileTheta+δ+ε)

/-- Include both actual small-product complements and absorb fixed slack.
No polynomial, profile, residue-label or counting budget is supplied. -/
def CF17ActualBoxSourceCount : Prop :=
  StewartPrimitiveThue → ∀ ε : ℝ, 0<ε →
    ∃ X₀ K : ℝ, 32≤X₀ ∧ 0<K ∧
      ∀ X B E : ℝ, X₀≤X → 0<B → 0<E →
        ∀ (S : Finset ℕ) (b d u v : ℕ → ℕ),
          (∀ n∈S,PairSource n (b n) (d n) (u n) (v n)) →
          (∀ n∈S,actualRealBox X B E n (b n) (d n)) →
          (S.card:ℝ)≤K*X^(profileTheta+ε)

end
end P0365Subquarter
