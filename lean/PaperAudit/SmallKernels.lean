import PaperProofs.SmallKernels

namespace P0365Subquarter

set_option pp.all true

#print CF02SourceTrace
#print CF02FixedKernelProductCount
#print CF02SmallKernelProductCount
#print SmallKernelCount
#print CF02OriginalSmallKernelCount

#check (source_trace : CF02SourceTrace)
#check (fixed_kernel_product_count : CF02FixedKernelProductCount)
#check (small_kernel_product_count : CF02SmallKernelProductCount)
#check (original_small_kernel_count : CF02OriginalSmallKernelCount)

#print axioms pell_pow_y_nonneg
#print axioms two_pow_le_pell_x
#print axioms pell_x_card_le_log_of_fundamental
#print axioms pell_nontrivial_x_card_le_log
#print axioms source_trace
#print axioms fixed_kernel_product_count
#print axioms small_kernel_product_count
#print axioms original_small_kernel_count

example (N : ℕ) : SmallKernelCount 0 N = 0 := by
  have h := original_small_kernel_count 0 N
  exact Nat.eq_zero_of_le_zero (by simpa using h)

example (Y : ℕ) : SmallKernelCount Y 0 = 0 := by
  classical
  have hzero : ¬ ∃ b d u v : ℕ, PairSource 0 b d u v ∧ b * d ≤ Y := by
    rintro ⟨b, d, u, v, hs, _⟩
    exact Nat.lt_irrefl 0 (additive_and_integer_source 0 b d u v hs).1
  unfold SmallKernelCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hN, hs⟩
  have hn0 : n = 0 := by have := Finset.mem_range.mp hN; omega
  subst n
  exact hzero hs

example (D N : ℕ) : (∅ : Finset ℕ).card ≤ Nat.log 2 (2 * N + 1) + 1 := by
  apply fixed_kernel_product_count D N ∅
  simp

example (D N : ℕ) (S : Finset ℕ) (hD : D = 0 ∨ D = 1)
    (hS : ∀ n ∈ S, n ≤ N ∧ ∃ b d u v : ℕ, PairSource n b d u v ∧ b * d = D) :
    S.card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  rcases hS n hn with ⟨_, b, d, u, v, hs, hbd⟩
  have ht := source_trace n b d u v hs
  have hbdZ : (b : ℤ) * (d : ℤ) = (D : ℤ) := by exact_mod_cast hbd
  rw [hbdZ] at ht
  let a : Pell.Solution₁ (D : ℤ) :=
    Pell.Solution₁.mk (2 * (n : ℤ) + 1)
      (2 * (b : ℤ) * (d : ℤ) * (u : ℤ) * (v : ℤ)) ht
  have hnpos : 0 < (n : ℤ) := by
    exact_mod_cast (additive_and_integer_source n b d u v hs).1
  have hx : 1 < a.x := by change 1 < 2 * (n : ℤ) + 1; omega
  have hp := Pell.Solution₁.d_pos_of_one_lt_x hx
  have hns := Pell.Solution₁.d_nonsquare_of_one_lt_x hx
  rcases hD with rfl | rfl
  · norm_num at hp
  · exact hns ⟨1, by decide⟩

end P0365Subquarter
