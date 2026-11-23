import PaperTargets.SmallKernels
import PaperProofs.CanonicalSource
import Mathlib.NumberTheory.Pell
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

/-!
Native requalification of the stronger CF02 Pell-count route from
docs/research/2026-10-13-p0365-bound/PellCounting.lean, SHA-256
236e08b75c7f419dfe884a46b867962a157c8a50a4454b76a7f3236c2b0c11f5.
No scratch import and no external Pell hypothesis. The final counts use only
the frozen maintained PairSource; Mathlib's proved classification is internal.
-/

namespace P0365Subquarter

set_option autoImplicit false

theorem pell_pow_y_nonneg {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (m : ℕ) : 0 ≤ (a ^ m).y := by
  cases m with
  | zero => simp
  | succ m => exact (Pell.Solution₁.y_pow_succ_pos ha.x_pos ha.2.1 m).le

theorem two_pow_le_pell_x {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (m : ℕ) : (2 : ℤ) ^ m ≤ (a ^ m).x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ha2 : (2 : ℤ) ≤ a.x := by have h := ha.1; omega
    have hcross : 0 ≤ D * ((a ^ m).y * a.y) :=
      mul_nonneg ha.d_pos.le (mul_nonneg (pell_pow_y_nonneg ha m) ha.2.1.le)
    calc
      (2 : ℤ) ^ (m + 1) = (2 : ℤ) ^ m * 2 := pow_succ _ _
      _ ≤ (a ^ m).x * a.x := mul_le_mul ih ha2 (by norm_num)
        (Pell.Solution₁.x_pow_pos ha.x_pos m).le
      _ ≤ (a ^ m).x * a.x + D * ((a ^ m).y * a.y) := le_add_of_nonneg_right hcross
      _ = (a ^ (m + 1)).x := by rw [pow_succ, Pell.Solution₁.x_mul]

theorem pell_x_card_le_log_of_fundamental {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (U : ℕ) (S : Finset ℤ)
    (hS : ∀ x ∈ S, 0 < x ∧ x ≤ (U : ℤ) ∧
      ∃ y : ℤ, 0 ≤ y ∧ x ^ 2 - D * y ^ 2 = 1) :
    S.card ≤ Nat.log 2 U + 1 := by
  classical
  have hsub : S ⊆ (Finset.range (Nat.log 2 U + 1)).image (fun m : ℕ => (a ^ m).x) := by
    intro x hx
    rcases hS x hx with ⟨hxpos, hxU, y, hy, hEq⟩
    let b : Pell.Solution₁ D := Pell.Solution₁.mk x y hEq
    obtain ⟨m, hm⟩ := ha.eq_pow_of_nonneg (show 0 < b.x from hxpos) (show 0 ≤ b.y from hy)
    have hxm : x = (a ^ m).x := by
      simpa [b] using congrArg (fun z : Pell.Solution₁ D => z.x) hm
    have hpowZ : (2 : ℤ) ^ m ≤ (U : ℤ) :=
      (two_pow_le_pell_x ha m).trans (by rw [← hxm]; exact hxU)
    have hpowN : 2 ^ m ≤ U := by exact_mod_cast hpowZ
    have hmle : m ≤ Nat.log 2 U := Nat.le_log_of_pow_le (by decide) hpowN
    exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), hxm.symm⟩
  calc
    S.card ≤ ((Finset.range (Nat.log 2 U + 1)).image (fun m : ℕ => (a ^ m).x)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.log 2 U + 1)).card := Finset.card_image_le
    _ = Nat.log 2 U + 1 := Finset.card_range _

theorem pell_nontrivial_x_card_le_log (D : ℤ) (U : ℕ) (S : Finset ℤ)
    (hS : ∀ x ∈ S, 1 < x ∧ x ≤ (U : ℤ) ∧
      ∃ y : ℤ, 0 ≤ y ∧ x ^ 2 - D * y ^ 2 = 1) :
    S.card ≤ Nat.log 2 U + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  rcases hS x₀ hx₀ with ⟨hx₀pos, _, y₀, _, hEq₀⟩
  let b : Pell.Solution₁ D := Pell.Solution₁.mk x₀ y₀ hEq₀
  have hb : 1 < b.x := hx₀pos
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (Pell.Solution₁.d_pos_of_one_lt_x hb) (Pell.Solution₁.d_nonsquare_of_one_lt_x hb)
  apply pell_x_card_le_log_of_fundamental ha U S
  intro x hx
  rcases hS x hx with ⟨hxpos, hxU, y, hy, hEq⟩
  exact ⟨lt_trans zero_lt_one hxpos, hxU, y, hy, hEq⟩

theorem source_trace : CF02SourceTrace := by
  intro n b d u v h
  rcases h with ⟨_, _, _, _, _, _, hn, hs⟩
  have hnZ : (n : ℤ) = (b : ℤ) ^ 3 * (u : ℤ) ^ 2 := by exact_mod_cast hn
  have hsZ : (d : ℤ) ^ 3 * (v : ℤ) ^ 2 = (b : ℤ) ^ 3 * (u : ℤ) ^ 2 + 1 := by
    exact_mod_cast hs
  calc
    _ = 1 + 4 * (b : ℤ) ^ 3 * (u : ℤ) ^ 2 *
        ((b : ℤ) ^ 3 * (u : ℤ) ^ 2 + 1 - (d : ℤ) ^ 3 * (v : ℤ) ^ 2) := by
      rw [hnZ]
      ring
    _ = 1 := by rw [hsZ]; ring

theorem fixed_kernel_product_count : CF02FixedKernelProductCount := by
  intro D N S hS
  classical
  have hinj : Function.Injective (fun n : ℕ => 2 * (n : ℤ) + 1) := by
    intro m n h
    change 2 * (m : ℤ) + 1 = 2 * (n : ℤ) + 1 at h
    omega
  have htrace := pell_nontrivial_x_card_le_log (D : ℤ) (2 * N + 1)
    (S.image (fun n : ℕ => 2 * (n : ℤ) + 1)) ?_
  · rwa [Finset.card_image_of_injective S hinj] at htrace
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  rcases hS n hn with ⟨hnN, b, d, u, v, hs, hD⟩
  have hnpos : 0 < (n : ℤ) := by
    exact_mod_cast (additive_and_integer_source n b d u v hs).1
  have hnNZ : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hnN
  refine ⟨by omega, by push_cast; omega,
    2 * (b : ℤ) * (d : ℤ) * (u : ℤ) * (v : ℤ), by positivity, ?_⟩
  have ht := source_trace n b d u v hs
  have hDZ : (b : ℤ) * (d : ℤ) = (D : ℤ) := by exact_mod_cast hD
  rwa [hDZ] at ht

theorem small_kernel_product_count : CF02SmallKernelProductCount := by
  intro Y N S hS
  classical
  let F : ℕ → Finset ℕ := fun k => S.filter
    (fun n => ∃ b d u v : ℕ, PairSource n b d u v ∧ b * d = k + 1)
  have hcover : S ⊆ (Finset.range Y).biUnion F := by
    intro n hn
    rcases hS n hn with ⟨_, b, d, u, v, hs, hY⟩
    have hpos : 0 < b * d := Nat.mul_pos hs.1 hs.2.1
    refine Finset.mem_biUnion.mpr ⟨b * d - 1, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨hn, b, d, u, v, hs, by omega⟩
  have hF (k : ℕ) (_hk : k ∈ Finset.range Y) :
      (F k).card ≤ Nat.log 2 (2 * N + 1) + 1 := by
    apply fixed_kernel_product_count (k + 1) N (F k)
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnS, hex⟩
    exact ⟨(hS n hnS).1, hex⟩
  simpa using (Finset.card_le_card hcover).trans
    (Finset.card_biUnion_le_card_mul (Finset.range Y) F _ hF)

theorem original_small_kernel_count : CF02OriginalSmallKernelCount := by
  classical
  intro Y N
  apply small_kernel_product_count Y N
    ((Finset.range (N + 1)).filter
      (fun n => ∃ b d u v : ℕ, PairSource n b d u v ∧ b * d ≤ Y))
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hN, hs⟩
  exact ⟨by simpa using (Finset.mem_range.mp hN), hs⟩

end P0365Subquarter
