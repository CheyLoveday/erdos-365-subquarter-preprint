import PaperProofs.BoxCounts

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF17CompactBoxSourceCount
#print CF17ResidualBoxSourceCount
#print CF17ActualBoxSourceCount
#check (compact_box_source_count : CF17CompactBoxSourceCount)
#check (residual_box_source_count : CF17ResidualBoxSourceCount)
#check (actual_box_source_count : CF17ActualBoxSourceCount)
#print axioms compact_box_source_count
#print axioms residual_box_source_count
#print axioms actual_box_source_count
set_option pp.all false

example : CF17CompactBoxSourceCount := by
  intro hThue δ ε hδ hδ₁ hε
  exact compact_box_source_count hThue δ ε hδ hδ₁ hε

example : CF17ResidualBoxSourceCount := by
  intro hThue δ ε hδ hδ₁ hε
  exact residual_box_source_count hThue δ ε hδ hδ₁ hε

example : CF17ActualBoxSourceCount := by
  intro hThue ε hε
  exact actual_box_source_count hThue ε hε

-- Empty populations do not require an actual anchor source.
example (hThue : StewartPrimitiveThue) (ε : ℝ) (hε : 0<ε) :
    ∃ X₀ K : ℝ,32≤X₀ ∧ 0<K ∧ ∀ X B E : ℝ,
      X₀≤X → 0<B → 0<E → (0:ℝ)≤K*X^(profileTheta+ε) := by
  obtain ⟨X₀,K,hX₀,hK,hcount⟩ := actual_box_source_count hThue ε hε
  refine ⟨X₀,K,hX₀,hK,?_⟩
  intro X B E hX hB hE
  have hh := hcount X B E hX hB hE (∅:Finset ℕ)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (by simp) (by simp)
  simpa only [Finset.card_empty,Nat.cast_zero] using hh

-- A genuine unit-kernel source at both lower closed box endpoints.
-- This checks the input domain; no unknown eventual threshold is asserted.
example : PairSource 288 2 1 6 17 ∧ actualRealBox 288 2 1 288 2 1 := by
  refine ⟨⟨by decide,by decide,by decide,by decide,
    Nat.squarefree_two,squarefree_one,by decide,by decide⟩,?_⟩
  norm_num [actualRealBox]

-- Zero coordinates are excluded by the original positive-source definition.
example (n d u v : ℕ) : ¬PairSource n 0 d u v := by
  simp [PairSource]

end
end P0365Subquarter
