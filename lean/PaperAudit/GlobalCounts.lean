import PaperProofs.GlobalCounts

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF18OriginalShellSourceCount
#print CF18NaturalPairCount
#print CF18RealPairCount
#check (original_shell_source_count : CF18OriginalShellSourceCount)
#check (natural_pair_count : CF18NaturalPairCount)
#check (real_pair_count : CF18RealPairCount)
#print axioms original_shell_source_count
#print axioms natural_pair_count
#print axioms real_pair_count
set_option pp.all false

example : CF18OriginalShellSourceCount := by
  intro hThue ε hε
  exact original_shell_source_count hThue ε hε

example : CF18NaturalPairCount := by
  intro hThue ε hε
  exact natural_pair_count hThue ε hε

example : CF18RealPairCount := by
  intro hThue ε hε
  exact real_pair_count hThue ε hε

-- The counted population is nonempty: the original 8/9 source is included.
example : 1≤PairCount 8 := by
  classical
  rw [count_source_correspondence 8]
  apply Finset.one_le_card.mpr
  refine ⟨8,Finset.mem_filter.mpr ⟨by decide,?_⟩⟩
  exact ⟨2,1,1,3,by
    exact ⟨by decide,by decide,by decide,by decide,
      Nat.squarefree_two,squarefree_one,by decide,by decide⟩⟩

-- The real cutoff adapter counts exactly the same original starts.
open scoped Classical in
example (X : ℝ) (hX : 1≤X) (n : ℕ) :
    n∈((Finset.range (Nat.floor X+1)).filter
      (fun k => Powerful k ∧ Powerful (k+1))) ↔
      (n:ℝ)≤X ∧ Powerful n ∧ Powerful (n+1) := by
  classical
  simp only [Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  rw [Nat.le_floor_iff (by linarith : 0≤X)]

end
end P0365Subquarter
