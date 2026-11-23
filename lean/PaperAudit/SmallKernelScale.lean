import PaperProofs.SmallKernelScale

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF02OriginalSmallKernelSubpower
#check (original_small_kernel_subpower : CF02OriginalSmallKernelSubpower)
#print axioms original_small_kernel_subpower
set_option pp.all false

example : CF02OriginalSmallKernelSubpower := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := original_small_kernel_subpower ε hε
  exact ⟨C,hC,fun X Y hX hY S hS => hbound X Y hX hY S hS⟩

-- Every real cutoff below one, including zero and fractional cutoffs,
-- forces the original source population to be empty.
example (Y : ℝ) (hY : Y<1) (S : Finset ℕ)
    (hS : ∀ n ∈ S, ∃ b d u v : ℕ, PairSource n b d u v ∧ (b*d:ℝ)≤Y) : S=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨b,d,u,v,hs,hp⟩ := hS n hn
  have hbd : 1≤b*d := Nat.succ_le_of_lt (Nat.mul_pos hs.1 hs.2.1)
  have hone : (1:ℝ)≤(b*d:ℝ) := by exact_mod_cast hbd
  linarith

end
end P0365Subquarter
