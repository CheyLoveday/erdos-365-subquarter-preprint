import PaperTargets.ClassCounts

/-! CF03 original small-multiplier complement. The fixed multiplier-ratio
cubic count is supplied by the proved coordinate-ruling route. Positive product
labels are counted dyadically; no Y-sized independent covers are multiplied. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- One dyadic u-range costs at most Y positive (u,v) labels with uv<=Y. -/
def CF03DyadicProductLabels : Prop :=
  ∀ Y k : ℕ, ∀ S : Finset (ℕ × ℕ),
    (∀ z ∈ S, 0<z.1 ∧ 0<z.2 ∧ z.1*z.2≤Y ∧ 2^k≤z.1 ∧ z.1<2^(k+1)) →
    S.card≤Y

/-- The number of positive multiplier pairs with uv<=Y is O(Y log Y),
including Y0 and Y1. No source height or coprimality is needed for labels. -/
def CF03SmallMultiplierLabels : Prop :=
  ∀ Y : ℕ, ∀ S : Finset (ℕ × ℕ),
    (∀ z ∈ S, 0<z.1 ∧ 0<z.2 ∧ z.1*z.2≤Y) →
    S.card≤Y*(Nat.log 2 Y+1)

/-- Count actual original starts by their selected primitive multiplier pairs;
each fixed pair costs the uniform cubic level-one bound8400. -/
def CF03OriginalSmallMultiplierCount : Prop :=
  StewartPrimitiveThue → ∀ Y : ℕ, ∀ S : Finset ℕ,
    (∀ n ∈ S, ∃ b d u v : ℕ, PairSource n b d u v ∧ u*v≤Y) →
    S.card≤8400*Y*(Nat.log 2 Y+1)

/-- The actual shell-scale complement costs Y times one epsilon loss.
The fixed factor4 allows the constant-factor multiplier boundary ranges. -/
def CF03OriginalSmallMultiplierSubpower : Prop :=
  StewartPrimitiveThue → ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ X Y : ℝ, 32≤X → 0≤Y → Y≤4*X → ∀ S : Finset ℕ,
      (∀ n ∈ S, ∃ b d u v : ℕ, PairSource n b d u v ∧ (u*v:ℝ)≤Y) →
      (S.card:ℝ)≤C*Y*X^ε

end
end P0365Subquarter
