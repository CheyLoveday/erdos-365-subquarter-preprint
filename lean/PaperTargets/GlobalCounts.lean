import PaperTargets.BoxCounts
import PaperTargets.RulingCounts

/-! CF18: original-source dyadic/shell aggregation, positive-natural count,
and real/floor adapter. The precise external Stewart input remains explicit. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- All original finite shell sources, including both orientations and returns.
No box cover, polynomial, profile or counting budget is supplied. -/
def CF18OriginalShellSourceCount : Prop :=
  StewartPrimitiveThue → ∀ ε : ℝ, 0<ε →
    ∃ X₀ K : ℝ, 32≤X₀ ∧ 0<K ∧ ∀ X : ℝ, X₀≤X →
      ∀ (S : Finset ℕ) (b d u v : ℕ → ℕ),
        (∀ n∈S,PairSource n (b n) (d n) (u n) (v n)) →
        (∀ n∈S,X≤(n:ℝ) ∧ (n:ℝ)≤2*X) →
        (S.card:ℝ)≤K*X^(profileTheta+ε)

/-- Full canonical positive-natural original count with one uniform constant,
including the finite head. This remains conditional on the exact Stewart Prop. -/
def CF18NaturalPairCount : Prop :=
  StewartPrimitiveThue → ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ N : ℕ, 1≤N → (PairCount N:ℝ)≤C*(N:ℝ)^(profileTheta+ε)

/-- The original real-cutoff count is the natural count at floor X. -/
def CF18RealPairCount : Prop :=
  StewartPrimitiveThue → ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ X : ℝ, 1≤X → (PairCount (Nat.floor X):ℝ)≤C*X^(profileTheta+ε)

end
end P0365Subquarter
