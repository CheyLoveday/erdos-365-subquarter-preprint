import PaperTargets.SmallMultipliers
import PaperProofs.ClassCounts

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem finite_fiber_bound {α β : Type} [DecidableEq β] (S : Finset α) (T : Finset β)
    (f : α → β) (k : ℕ) (hmap : ∀ z ∈ S, f z ∈ T)
    (hfib : ∀ r ∈ T, (S.filter (fun z => f z=r)).card ≤ k) : S.card ≤ T.card*k := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f:=f) (t:=T) (fun z hz => hmap z hz)]
  calc
    _ ≤ ∑ r ∈ T, k := Finset.sum_le_sum hfib
    _ = _ := by simp

/-- A dyadic multiplier range is contained in one rectangle of area at most Y. -/
theorem dyadic_product_labels : CF03DyadicProductLabels := by
  classical
  intro Y k S hS
  let a := 2^k
  have ha : 0<a := pow_pos (by decide) _
  have hsub : S⊆(Finset.Ico a (2*a)).product (Finset.Icc 1 (Y/a)) := by
    intro z hz
    obtain ⟨hu,hv,hprod,hlo,hhi⟩ := hS z hz
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨hlo,?_⟩,Finset.mem_Icc.mpr ⟨hv,?_⟩⟩
    · simpa [a,pow_succ,Nat.mul_comm] using hhi
    · apply (Nat.le_div_iff_mul_le ha).mpr
      have hlow : a*z.2≤z.1*z.2 := Nat.mul_le_mul_right z.2 hlo
      simpa [Nat.mul_comm] using hlow.trans hprod
  calc
    S.card ≤ ((Finset.Ico a (2*a)).product (Finset.Icc 1 (Y/a))).card := Finset.card_le_card hsub
    _ = a*(Y/a) := by simp [Finset.card_product,Nat.card_Ico,Nat.card_Icc,two_mul]
    _ ≤ Y := by simpa [Nat.mul_comm] using Nat.div_mul_le_self Y a

/-- Logarithmic dyadic labels, each paid only once by its positive product. -/
theorem small_multiplier_labels : CF03SmallMultiplierLabels := by
  classical
  intro Y S hS
  have hmap (z : ℕ×ℕ) (hz : z∈S) : Nat.log 2 z.1∈Finset.range (Nat.log 2 Y+1) := by
    obtain ⟨hu,hv,hprod⟩ := hS z hz
    apply Finset.mem_range.mpr
    have huY : z.1≤Y := by nlinarith
    exact Nat.lt_succ_of_le (Nat.log_mono_right huY)
  have hfib (k : ℕ) (_ : k∈Finset.range (Nat.log 2 Y+1)) :
      (S.filter (fun z => Nat.log 2 z.1=k)).card≤Y := by
    apply dyadic_product_labels Y k
    intro z hz
    obtain ⟨hzS,hk⟩ := Finset.mem_filter.mp hz
    obtain ⟨hu,hv,hprod⟩ := hS z hzS
    refine ⟨hu,hv,hprod,?_,?_⟩
    · rw [←hk]
      exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hu)
    · rw [←hk]
      exact Nat.lt_pow_succ_log_self (by decide : 1<2) z.1
  calc
    S.card ≤ (Finset.range (Nat.log 2 Y+1)).card*Y :=
      finite_fiber_bound S _ (fun z => Nat.log 2 z.1) Y hmap hfib
    _ = Y*(Nat.log 2 Y+1) := by simp [Nat.mul_comm]

/-- Choose actual multiplier labels, then count original starts in each fiber. -/
theorem original_small_multiplier_count : CF03OriginalSmallMultiplierCount := by
  classical
  intro hThue Y S hS
  have hchoose : ∀ n : ℕ, ∃ b d u v : ℕ, n∈S → PairSource n b d u v ∧ u*v≤Y := by
    intro n
    by_cases hn : n∈S
    · obtain ⟨b,d,u,v,hs,hp⟩ := hS n hn
      exact ⟨b,d,u,v,fun _ => ⟨hs,hp⟩⟩
    · exact ⟨0,0,0,0,fun h => False.elim (hn h)⟩
  choose b d u v hw using hchoose
  let f : ℕ → ℕ×ℕ := fun n => (u n,v n)
  let T := S.image f
  have hT : T.card≤Y*(Nat.log 2 Y+1) := by
    apply small_multiplier_labels Y T
    intro z hz
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨(hw n hn).1.2.2.1,(hw n hn).1.2.2.2.1,(hw n hn).2⟩
  have hfib (z : ℕ×ℕ) (_ : z∈T) : (S.filter (fun n => f n=z)).card≤8400 := by
    apply fixed_multiplier_ratio_count hThue ((z.2:ℚ)/z.1)
    intro n hn
    obtain ⟨hnS,he⟩ := Finset.mem_filter.mp hn
    refine ⟨b n,d n,u n,v n,(hw n hnS).1,?_⟩
    exact congrArg (fun z : ℕ×ℕ => (z.2:ℚ)/z.1) he
  calc
    S.card ≤ T.card*8400 := finite_fiber_bound S T f 8400 (fun n hn => Finset.mem_image.mpr ⟨n,hn,rfl⟩) hfib
    _ ≤ (Y*(Nat.log 2 Y+1))*8400 := Nat.mul_le_mul_right _ hT
    _ = _ := by ring

/-- Natural floors retain every actual label, including real Y below one. -/
theorem original_small_multiplier_subpower : CF03OriginalSmallMultiplierSubpower := by
  intro hThue ε hε
  obtain ⟨C,hC,hlog⟩ := ruling_log_subpower ε hε
  refine ⟨8400*C*(2:ℝ)^ε,by positivity,?_⟩
  intro X Y hX hY hYX S hS
  let N := Nat.floor Y
  have hNY : (N:ℝ)≤Y := Nat.floor_le hY
  have hnat := original_small_multiplier_count hThue N S (by
    intro n hn
    obtain ⟨b,d,u,v,hs,hp⟩ := hS n hn
    refine ⟨b,d,u,v,hs,?_⟩
    apply Nat.le_floor
    exact_mod_cast hp)
  have hlogs : Nat.log 2 N+1≤8401+Nat.log 2 (2*N+1) := by
    have h := Nat.log_mono_right (b:=2) (by omega : N≤2*N+1)
    omega
  have hb : ((Nat.log 2 N+1:ℕ):ℝ)≤C*(2*X)^ε := by
    have hl := hlog (2*X) (by linarith) N (by linarith)
    have hs : ((Nat.log 2 N+1:ℕ):ℝ)≤(8401+Nat.log 2 (2*N+1):ℝ) := by exact_mod_cast hlogs
    exact hs.trans hl
  have heq : (2*X)^ε=(2:ℝ)^ε*X^ε := Real.mul_rpow (by norm_num) (by linarith)
  calc
    (S.card:ℝ) ≤ 8400*(N:ℝ)*((Nat.log 2 N+1:ℕ):ℝ) := by exact_mod_cast hnat
    _ ≤ (8400*Y)*(C*(2*X)^ε) := mul_le_mul
      (by nlinarith) hb (by positivity) (by positivity)
    _ = (8400*C*(2:ℝ)^ε)*Y*X^ε := by rw [heq]; ring

end
end P0365Subquarter
