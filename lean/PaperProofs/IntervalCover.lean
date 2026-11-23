import PaperTargets.IntervalCover

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- A common additive grid has width a₀/M, at most the relative width at
any of its positive left endpoints. The final grid point retains 4a₀. -/
theorem relative_interval_cover : CF17RelativeIntervalCover := by
  classical
  intro a₀ ha₀ M hM
  have hM₀ : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  let w : ℝ := a₀/(M:ℝ)
  have hw : 0<w := div_pos ha₀ hM₀
  have hMw : (M:ℝ)*w=a₀ := by dsimp [w]; field_simp
  let f : ℕ → ℝ := fun j => a₀+(j:ℝ)*w
  refine ⟨(Finset.range (3*M+1)).image f,?_,?_,?_⟩
  · calc
      _ ≤ (Finset.range (3*M+1)).card := Finset.card_image_le
      _ = 3*M+1 := Finset.card_range _
  · intro a ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
    dsimp [f]
    positivity
  · intro s hs₀ hs₄
    let q : ℝ := (s-a₀)/w
    let j := Nat.floor q
    have hq₀ : 0≤q := div_nonneg (sub_nonneg.mpr hs₀) hw.le
    have hq₃ : q≤((3*M:ℕ):ℝ) := by
      have hh : q≤3*(M:ℝ) := by
        dsimp [q]
        apply (div_le_iff₀ hw).mpr
        nlinarith [hMw]
      exact_mod_cast hh
    have hj : j≤3*M := Nat.floor_le_of_le hq₃
    have hjl : (j:ℝ)*w≤s-a₀ := (le_div_iff₀ hw).mp (Nat.floor_le hq₀)
    have hjr : s-a₀<((j:ℝ)+1)*w := (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one q)
    have hfa : a₀≤f j := by
      dsimp [f]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hw.le)
    have hfs : f j≤s := by dsimp [f]; linarith
    have hsw : s≤f j+w := by dsimp [f]; nlinarith
    have hwidth : w≤f j/(M:ℝ) := by
      dsimp [w]
      exact div_le_div_of_nonneg_right hfa hM₀.le
    refine ⟨f j,Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le hj),rfl⟩,hfs,?_⟩
    calc
      s ≤ f j+w := hsw
      _ ≤ f j+f j/(M:ℝ) := by linarith
      _ = f j*(1+1/(M:ℝ)) := by ring

/-- The inclusive original box places every positive kernel ratio in one
common range [B/(2E),4B/(2E)], independently of the source and shell start. -/
theorem actual_box_interval_cover : CF17ActualBoxIntervalCover := by
  intro X B E hB hE M hM
  let a₀ : ℝ := B/(2*E)
  have ha₀ : 0<a₀ := by dsimp [a₀]; positivity
  obtain ⟨A,hcard,hpos,hcover⟩ := relative_interval_cover a₀ ha₀ M hM
  refine ⟨A,hcard,hpos,?_⟩
  intro n b d hbox
  rcases hbox with ⟨_,_,hb,hb',hd,hd'⟩
  have hd₀ : (0:ℝ)<d := lt_of_lt_of_le hE hd
  have hlo : a₀≤(b:ℝ)/d := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*E) hd₀).mpr
    calc
      B*(d:ℝ) ≤ B*(2*E) := mul_le_mul_of_nonneg_left hd' hB.le
      _ ≤ (b:ℝ)*(2*E) := mul_le_mul_of_nonneg_right hb (by positivity)
  have hhi : (b:ℝ)/d≤4*a₀ := by
    have hu : (b:ℝ)/d≤(2*B)/E := by
      apply (div_le_div_iff₀ hd₀ hE).mpr
      calc
        (b:ℝ)*E ≤ (2*B)*E := mul_le_mul_of_nonneg_right hb' hE.le
        _ ≤ (2*B)*(d:ℝ) := mul_le_mul_of_nonneg_left hd (by positivity)
    have he : (2*B)/E=4*a₀ := by dsimp [a₀]; field_simp; ring
    exact hu.trans_eq he
  obtain ⟨a,ha,hlo',hhi'⟩ := hcover ((b:ℝ)/d) hlo hhi
  exact ⟨a,ha,hlo',hhi'⟩

end
end P0365Subquarter
