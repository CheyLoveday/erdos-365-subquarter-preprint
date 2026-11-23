import PaperTargets.BoxCounts
import PaperProofs.GenericCoarse
import PaperProofs.IntervalCounts
import PaperProofs.IntervalCover
import PaperProofs.ResidualProfiles
import PaperProofs.SmallKernelScale
import PaperProofs.SmallMultipliers

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem real_cover_card {ι α : Type} [DecidableEq α] (S : Finset α) (I : Finset ι)
    (A : ι → Finset α) (f : ι → ℝ) (hcover : S⊆I.biUnion A)
    (hA : ∀ i∈I,((A i).card:ℝ)≤f i) :
    (S.card:ℝ)≤∑ i∈I,f i := by
  classical
  have hc : S.card≤∑ i∈I,(A i).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcast : (S.card:ℝ)≤∑ i∈I,((A i).card:ℝ) := by exact_mod_cast hc
  exact hcast.trans (Finset.sum_le_sum hA)

/-- Produce each actual interval polynomial and sum through one common cover. -/
theorem compact_box_source_count : CF17CompactBoxSourceCount := by
  classical
  intro hThue δ ε hδ hδ₁ hε
  obtain ⟨D,N,hD,Cf,Xc,hCf,hXc,hcoarse⟩ := actual_uniform_coarse_polynomial δ hδ hδ₁
  obtain ⟨Xi,Ki,hXi,hKi,hinterval⟩ := coarse_interval_source_count hThue D
    (N:ℝ) Cf δ (Nat.cast_nonneg N) hCf.le hδ hδ₁ ε hε
  refine ⟨max Xc Xi,4*Ki,hXc.trans (le_max_left _ _),by positivity,?_⟩
  intro X ψ B E hX hψlo hψhi hB hE hBE S b d u v hs hbox
  have hc : Xc≤X := (le_max_left _ _).trans hX
  have hi : Xi≤X := (le_max_right _ _).trans hX
  have hX₃₂ : 32≤X := hXc.trans hc
  have hX₁ : 1≤X := by linarith
  have hXp : 0<X := by linarith
  have htθ : 0<profileTheta := by norm_num [profileTheta]
  have hψ₀ : 0≤ψ := by linarith
  have hψ₂ : ψ≤2/3 := by linarith
  let M : ℕ := roundedHeight X ψ δ
  have hM : (1:ℝ)≤M := (rounded_height_bounds X ψ δ hX₁ hψ₀ hψ₂ hδ.le).1
  have hMn : 1≤M := by exact_mod_cast hM
  have hMp : (0:ℝ)<M := by linarith
  have hR : 0<roundedScale X ψ δ := by
    dsimp [roundedScale]
    exact div_pos (Real.rpow_pos_of_pos hXp _) hMp
  obtain ⟨I,hI,hpos,hcover⟩ := actual_box_interval_cover X B E hB hE M hMn
  have hIreal : (I.card:ℝ)≤4*(M:ℝ) := by
    exact_mod_cast (show I.card≤4*M by omega)
  let T : ℝ → Finset ℕ := fun a => S.filter
    (fun n => actualDirectInterval a (M:ℝ) (b n) (d n))
  have hScover : S⊆I.biUnion T := by
    intro n hn
    obtain ⟨a,ha,hint⟩ := hcover n (b n) (d n) (hbox n hn)
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hn,hint⟩⟩
  have hT (a : ℝ) (ha : a∈I) : ((T a).card:ℝ)≤Ki*roundedScale X ψ δ*X^ε := by
    have hTS : T a⊆S := Finset.filter_subset _ _
    obtain ⟨F,hF,hFD,hFC,hzero⟩ := hcoarse X ψ B E a hc hψlo hψhi hB hE
      (hpos a ha) hBE (T a) b d u v (fun n hn => hs n (hTS hn))
      (fun n hn => hbox n (hTS hn)) (fun n hn => (Finset.mem_filter.mp hn).2)
    exact hinterval X ψ B E a hi hψ₀ hψ₂ hB hE (hpos a ha) hBE F hF hFD (by simpa only [Real.rpow_natCast] using hFC)
      (T a) b d u v (fun n hn => hs n (hTS hn))
      (fun n hn => hbox n (hTS hn)) (fun n hn => (Finset.mem_filter.mp hn).2) hzero
  have hMT : (M:ℝ)*roundedScale X ψ δ=X^(profileTheta+δ) := by
    have hMne : (roundedHeight X ψ δ:ℝ)≠0 := ne_of_gt hMp
    dsimp [roundedScale,M]
    field_simp [hMne]
  calc
    (S.card:ℝ)≤∑ a∈I,Ki*roundedScale X ψ δ*X^ε :=
      real_cover_card S I T _ hScover hT
    _=(I.card:ℝ)*(Ki*roundedScale X ψ δ*X^ε) := by simp
    _≤(4*(M:ℝ))*(Ki*roundedScale X ψ δ*X^ε) :=
      mul_le_mul_of_nonneg_right hIreal (by positivity)
    _=(4*Ki)*((M:ℝ)*roundedScale X ψ δ)*X^ε := by ring
    _=(4*Ki)*X^(profileTheta+δ)*X^ε := by rw [hMT]
    _=(4*Ki)*X^(profileTheta+δ+ε) := by
      rw [Real.rpow_add hXp (profileTheta+δ) ε]
      ring

/-- One actual anchor fixes the profile of the whole residual box. -/
theorem residual_box_source_count : CF17ResidualBoxSourceCount := by
  classical
  intro hThue δ ε hδ hδ₁ hε
  obtain ⟨Xc,K,hXc,hK,hcount⟩ := compact_box_source_count hThue δ ε hδ hδ₁ hε
  obtain ⟨Xp,hXp,hprofile⟩ := residual_compact_profile
  refine ⟨max Xc Xp,K,hXc.trans (le_max_left _ _),hK,?_⟩
  intro X B E hX hB hE S b d u v hs hbox hbd huv
  have hc : Xc≤X := (le_max_left _ _).trans hX
  have hp : Xp≤X := (le_max_right _ _).trans hX
  have hXX : 0<X := by linarith
  by_cases hS : S=∅
  · subst S
    simp only [Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg hK.le (Real.rpow_nonneg hXX.le _)
  · obtain ⟨n,hn⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨ψ,hBE,hψlo,hψhi,_,_⟩ := hprofile X hp B E hB hE n
      (b n) (d n) (u n) (v n) (hs n hn) (hbox n hn) (hbd n hn) (huv n hn)
    exact hcount X ψ B E hc hψlo hψhi hB hE hBE S b d u v hs hbox

/-- Include both original small-product complements and all residual sources. -/
theorem actual_box_source_count : CF17ActualBoxSourceCount := by
  classical
  intro hThue ε hε
  let e : ℝ := ε/3
  have he : 0<e := by dsimp [e]; linarith
  let δ : ℝ := min 1 e
  have hδ : 0<δ := by dsimp [δ]; exact lt_min (by norm_num) he
  have hδ₁ : δ≤1 := min_le_left _ _
  have hδe : δ≤e := min_le_right _ _
  obtain ⟨X₀,Kr,hX₀,hKr,hres⟩ := residual_box_source_count hThue δ e hδ hδ₁ he
  obtain ⟨Kk,hKk,hkernel⟩ := original_small_kernel_subpower e he
  obtain ⟨Ku,hKu,hmult⟩ := original_small_multiplier_subpower hThue e he
  refine ⟨X₀,Kk+Ku+Kr,hX₀,by positivity,?_⟩
  intro X B E hX hB hE S b d u v hs hbox
  have hX₃₂ : 32≤X := hX₀.trans hX
  have hX₁ : 1≤X := by linarith
  have hXp : 0<X := by linarith
  let Y : ℝ := X^profileTheta
  have hY : 0≤Y := (Real.rpow_pos_of_pos hXp _).le
  have hYX : Y≤4*X := calc
    _≤X^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hX₁ (by norm_num [profileTheta])
    _=X := Real.rpow_one _
    _≤4*X := by linarith
  let Sk := S.filter (fun n => (b n*d n:ℝ)≤Y)
  let Su := S.filter (fun n => (u n*v n:ℝ)≤Y)
  let Sr := S.filter (fun n => Y<(b n*d n:ℝ) ∧ Y<(u n*v n:ℝ))
  have hSk : Sk⊆S := Finset.filter_subset _ _
  have hSu : Su⊆S := Finset.filter_subset _ _
  have hSr : Sr⊆S := Finset.filter_subset _ _
  have hk : (Sk.card:ℝ)≤Kk*X^(profileTheta+e) := by
    calc
      _≤Kk*Y*X^e := hkernel X Y hX₃₂ hY Sk (by
        intro n hn
        exact ⟨(hbox n (hSk hn)).2.1,b n,d n,u n,v n,hs n (hSk hn),
          (Finset.mem_filter.mp hn).2⟩)
      _=Kk*X^(profileTheta+e) := by dsimp [Y]; rw [Real.rpow_add hXp]; ring
  have hu : (Su.card:ℝ)≤Ku*X^(profileTheta+e) := by
    calc
      _≤Ku*Y*X^e := hmult X Y hX₃₂ hY hYX Su (by
        intro n hn
        exact ⟨b n,d n,u n,v n,hs n (hSu hn),(Finset.mem_filter.mp hn).2⟩)
      _=Ku*X^(profileTheta+e) := by dsimp [Y]; rw [Real.rpow_add hXp]; ring
  have hr : (Sr.card:ℝ)≤Kr*X^(profileTheta+δ+e) :=
    hres X B E hX hB hE Sr b d u v (fun n hn => hs n (hSr hn))
      (fun n hn => hbox n (hSr hn))
      (fun n hn => (Finset.mem_filter.mp hn).2.1)
      (fun n hn => (Finset.mem_filter.mp hn).2.2)
  have hcover : S⊆(Sk∪Su)∪Sr := by
    intro n hn
    by_cases hk : (b n*d n:ℝ)≤Y
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,hk⟩))
    · by_cases hu : (u n*v n:ℝ)≤Y
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,hu⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hn,lt_of_not_ge hk,lt_of_not_ge hu⟩)
  have hcard : (S.card:ℝ)≤(Sk.card:ℝ)+(Su.card:ℝ)+(Sr.card:ℝ) := by
    have hh : S.card≤Sk.card+Su.card+Sr.card := calc
      _≤((Sk∪Su)∪Sr).card := Finset.card_le_card hcover
      _≤(Sk∪Su).card+Sr.card := Finset.card_union_le _ _
      _≤(Sk.card+Su.card)+Sr.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    exact_mod_cast hh
  have hp : X^(profileTheta+e)≤X^(profileTheta+ε) :=
    Real.rpow_le_rpow_of_exponent_le hX₁ (by dsimp [e]; linarith)
  have hpr : X^(profileTheta+δ+e)≤X^(profileTheta+ε) :=
    Real.rpow_le_rpow_of_exponent_le hX₁ (by dsimp [e] at hδe ⊢; linarith)
  calc
    (S.card:ℝ)≤(Sk.card:ℝ)+(Su.card:ℝ)+(Sr.card:ℝ) := hcard
    _≤Kk*X^(profileTheta+e)+Ku*X^(profileTheta+e)+Kr*X^(profileTheta+δ+e) :=
      add_le_add (add_le_add hk hu) hr
    _≤Kk*X^(profileTheta+ε)+Ku*X^(profileTheta+ε)+Kr*X^(profileTheta+ε) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hp hKk.le)
        (mul_le_mul_of_nonneg_left hp hKu.le)) (mul_le_mul_of_nonneg_left hpr hKr.le)
    _=(Kk+Ku+Kr)*X^(profileTheta+ε) := by ring

end
end P0365Subquarter
