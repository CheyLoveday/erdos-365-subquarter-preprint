import PaperTargets.RulingCounts
import PaperProofs.SourceCounts
import PaperProofs.SmallKernels

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem primitive_hom_content (f : Polynomial ℤ) (hf : f.IsPrimitive) :
    binaryContent (f.homogenize f.natDegree)=1 := by
  have hF : f.homogenize f.natDegree≠0 := by
    intro hz
    exact hf.ne_zero (Polynomial.eq_zero_of_homogenize_eq_zero le_rfl hz)
  obtain ⟨hc,_,he,_⟩ := binary_content_removal (f.homogenize f.natDegree) hF
  have ha : f=Polynomial.C (binaryContent (f.homogenize f.natDegree):ℤ)*
      binaryDehomogenize (binaryPrimitivePart (f.homogenize f.natDegree)) := by
    have h := congrArg (MvPolynomial.aeval ![(Polynomial.X:Polynomial ℤ),1]) he
    rw [Polynomial.aeval_homogenize_X_one f le_rfl] at h
    simpa only [map_mul,MvPolynomial.aeval_C,Polynomial.algebraMap_eq,binaryDehomogenize] using h
  have hu := hf (binaryContent (f.homogenize f.natDegree):ℤ) ⟨_,ha⟩
  have hcZ : 0<(binaryContent (f.homogenize f.natDegree):ℤ) := by exact_mod_cast hc
  rcases Int.isUnit_eq_one_or hu with hp | hn
  · exact_mod_cast hp
  · omega

/-- The actual level-one cubic is admissible even when rationally reducible. -/
theorem multiplier_cubic_admissibility : CF15MultiplierCubicAdmissibility := by
  intro u v hu hv hcop
  let f := multiplierCubic u v
  have huZ : (u:ℤ)≠0 := by exact_mod_cast hu.ne'
  have huQ : (u:ℚ)≠0 := by exact_mod_cast hu.ne'
  have hvQ : (v:ℚ)≠0 := by exact_mod_cast hv.ne'
  have hdm : (Polynomial.C ((u:ℤ)^2)*(Polynomial.X:Polynomial ℤ)^3).natDegree=3 := by
    rw [Polynomial.natDegree_C_mul (pow_ne_zero 2 huZ)]
    simp
  have hlt : (Polynomial.C ((v:ℤ)^2):Polynomial ℤ).natDegree <
      (Polynomial.C ((u:ℤ)^2)*(Polynomial.X:Polynomial ℤ)^3).natDegree := by
    rw [Polynomial.natDegree_C,hdm]
    decide
  have hd : f.natDegree=3 := (Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlt).trans hdm
  have hprim : f.IsPrimitive := by
    intro a ha
    have hvcoeff : f.coeff 0=(v:ℤ)^2 := by
      simp only [f,multiplierCubic,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
        Polynomial.coeff_C,Polynomial.coeff_X_pow]
      norm_num
    have hucoeff : f.coeff 3= -((u:ℤ)^2) := by
      simp only [f,multiplierCubic,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
        Polynomial.coeff_C,Polynomial.coeff_X_pow]
      norm_num
    have hav : a∣(v:ℤ)^2 := by
      rw [←hvcoeff]
      exact (Polynomial.C_dvd_iff_dvd_coeff a f).mp ha 0
    have hau : a∣(u:ℤ)^2 := by
      apply dvd_neg.mp
      rw [←hucoeff]
      exact (Polynomial.C_dvd_iff_dvd_coeff a f).mp ha 3
    have hp : IsCoprime (v:ℤ) (u:ℤ) := hcop.isCoprime
    have hp₁ : IsCoprime ((v:ℤ)^2) (u:ℤ) := by simpa [pow_two] using hp.mul_left hp
    have hp₂ : IsCoprime ((v:ℤ)^2) ((u:ℤ)^2) := by simpa [pow_two] using hp₁.mul_right hp₁
    exact hp₂.isUnit_of_dvd' hav hau
  have hrat : rationalPolynomial f=Polynomial.C ((v:ℚ)^2)-
      Polynomial.C ((u:ℚ)^2)*Polynomial.X^3 := by simp [f,multiplierCubic,rationalPolynomial]
  have hcoeff : (-(u:ℚ)^2)*((v:ℚ)^2/(u:ℚ)^2)=-(v:ℚ)^2 := by
    field_simp
  have hfactor : rationalPolynomial f=Polynomial.C (-(u:ℚ)^2)*
      ((Polynomial.X:Polynomial ℚ)^3-Polynomial.C ((v:ℚ)^2/(u:ℚ)^2)) := by
    rw [hrat,mul_sub,←Polynomial.C_mul,hcoeff]
    simp only [map_neg]
    ring
  have hsep : (rationalPolynomial f).Separable := by
    rw [hfactor]
    apply Polynomial.Separable.unit_mul
    · exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (pow_ne_zero 2 huQ)))
    · exact Polynomial.separable_X_pow_sub_C _ (by norm_num) (div_ne_zero (pow_ne_zero 2 hvQ) (pow_ne_zero 2 huQ))
  refine ⟨hd,hprim,primitive_hom_content f hprim,hsep,?_⟩
  intro b d
  rw [hd]
  have hxhom : ((Polynomial.X:Polynomial ℤ)^3).homogenize 3=(MvPolynomial.X 0:SourcePolynomial)^3 := by
    rw [Polynomial.homogenize_X_pow le_rfl]
    simp
  dsimp only [f,multiplierCubic]
  rw [Polynomial.homogenize_sub,Polynomial.homogenize_C,Polynomial.homogenize_C_mul,hxhom]
  simp only [map_sub,map_mul,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

private theorem primitive_ratio_injective {a b c d : ℕ} (hb : 0<b) (hd : 0<d)
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d)
    (hr : (a:ℚ)/b=(c:ℚ)/d) : a=c ∧ b=d := by
  have hi := Rat.div_int_inj (by exact_mod_cast hb : (0:ℤ)<b)
    (by exact_mod_cast hd : (0:ℤ)<d)
    (by simpa using hab : Nat.Coprime (a:ℤ).natAbs (b:ℤ).natAbs)
    (by simpa using hcd : Nat.Coprime (c:ℤ).natAbs (d:ℤ).natAbs)
    (by simpa using hr : ((a:ℤ):ℚ)/(b:ℤ)=((c:ℤ):ℚ)/(d:ℤ))
  exact ⟨by exact_mod_cast hi.1,by exact_mod_cast hi.2⟩

/-- A fixed positive primitive multiplier ratio costs one cubic level1 count. -/
theorem fixed_multiplier_ratio_count : CF15FixedMultiplierRatioCount := by
  classical
  intro hThue q S hS
  by_cases hempty : S=∅
  · simp [hempty]
  obtain ⟨n₀,hn₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨b₀,d₀,u₀,v₀,hs₀,hq₀⟩ := hS n₀ hn₀
  have hfixed : ∀ n ∈ S, ∃ b d : ℕ, PairSource n b d u₀ v₀ := by
    intro n hn
    obtain ⟨b,d,u,v,hs,hq⟩ := hS n hn
    obtain ⟨hvv,huu⟩ := primitive_ratio_injective hs.2.2.1 hs₀.2.2.1
      (primitive_ratios n b d u v hs).2.1 (primitive_ratios n₀ b₀ d₀ u₀ v₀ hs₀).2.1
      (hq.trans hq₀.symm)
    refine ⟨b,d,?_⟩
    rw [←huu,←hvv]
    exact hs
  have hw : ∀ n : ℕ, ∃ b d : ℕ, n∈S → PairSource n b d u₀ v₀ := by
    intro n
    by_cases hn : n∈S
    · obtain ⟨b,d,hs⟩ := hfixed n hn
      exact ⟨b,d,fun _ => hs⟩
    · exact ⟨0,0,fun h => False.elim (hn h)⟩
  choose b d hsource using hw
  let z : ℕ → Fin 2 → ℤ := fun n => ![(b n:ℤ),d n]
  have hinj : Set.InjOn z (↑S:Set ℕ) := by
    intro n hn m hm he
    have hb : b n=b m := by have h := congrFun he 0; simpa [z] using h
    calc
      n=(b n)^3*u₀^2 := (hsource n hn).2.2.2.2.2.2.1
      _=(b m)^3*u₀^2 := by rw [hb]
      _=m := (hsource m hm).2.2.2.2.2.2.1.symm
  have hcard : (S.image z).card=S.card := Finset.card_image_of_injOn hinj
  let f := multiplierCubic u₀ v₀
  obtain ⟨hd,_,hc,hsep,heval⟩ := multiplier_cubic_admissibility u₀ v₀ hs₀.2.2.1 hs₀.2.2.2.1
    (primitive_ratios n₀ b₀ d₀ u₀ v₀ hs₀).2.1
  change f.natDegree=3 at hd
  have hcount := hThue f hc hsep (by omega) (by omega) 1 (by decide) (S.image z) (by
    intro y hy
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hy
    refine ⟨?_,?_⟩
    · simpa [z,primitiveBinaryPoint] using (primitive_ratios n (b n) (d n) u₀ v₀ (hsource n hn)).1.isCoprime
    · rw [heval]
      exact (additive_and_integer_source n (b n) (d n) u₀ v₀ (hsource n hn)).2.2)
  calc
    S.card=(S.image z).card := hcard.symm
    _≤8400 := by simpa [hd,primeSupportCount] using hcount

/-- Fixing the primitive kernel ratio fixes the product in CF02. -/
theorem fixed_kernel_ratio_count : CF15FixedKernelRatioCount := by
  classical
  intro q N S hS
  by_cases hempty : S=∅
  · simp [hempty]
  obtain ⟨n₀,hn₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨b₀,d₀,u₀,v₀,hs₀,hq₀⟩ := (hS n₀ hn₀).2
  apply fixed_kernel_product_count (b₀*d₀) N S
  intro n hn
  obtain ⟨hnN,b,d,u,v,hs,hq⟩ := hS n hn
  obtain ⟨hbb,hdd⟩ := primitive_ratio_injective hs.2.1 hs₀.2.1
    (primitive_ratios n b d u v hs).1 (primitive_ratios n₀ b₀ d₀ u₀ v₀ hs₀).1
    (hq.trans hq₀.symm)
  exact ⟨hnN,b,d,u,v,hs,congrArg₂ Nat.mul hbb hdd⟩

/-- Both coordinate rulings have one coefficient-independent envelope. -/
theorem coordinate_ruling_count : CF15CoordinateRulingCount := by
  intro hThue i q N S hS
  fin_cases i
  · have h := fixed_kernel_ratio_count q N S (by
      intro n hn
      obtain ⟨hnN,b,d,u,v,hs,hq⟩ := hS n hn
      exact ⟨hnN,b,d,u,v,hs,by simpa [sourcePoint] using hq⟩)
    omega
  · have h := fixed_multiplier_ratio_count hThue q S (by
      intro n hn
      obtain ⟨_,b,d,u,v,hs,hq⟩ := hS n hn
      exact ⟨b,d,u,v,hs,by simpa [sourcePoint] using hq⟩)
    omega

/-- An elementary logarithm/power comparison gives one uniform epsilon loss. -/
theorem ruling_log_subpower : CF15RulingLogSubpower := by
  intro ε hε
  have hl₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  let a : ℝ := (5:ℝ)^ε/(ε*Real.log 2)
  refine ⟨8401+a,by positivity,?_⟩
  intro X hX N hN
  let K := 2*N+1
  let L := Nat.log 2 K
  have hK₀ : K≠0 := by dsimp [K]; omega
  have hpow : (2:ℝ)^L≤(K:ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hK₀
  have hlog : (L:ℝ)*Real.log 2≤Real.log (K:ℝ) := by
    have h := Real.log_le_log (by positivity) hpow
    simpa only [Real.log_pow] using h
  have hK : (K:ℝ)≤5*X := by dsimp [K]; push_cast; nlinarith
  have hchain : (L:ℝ)*Real.log 2≤(5:ℝ)^ε*X^ε/ε := by
    calc
      _≤Real.log (K:ℝ) := hlog
      _≤(K:ℝ)^ε/ε := Real.log_le_rpow_div (by positivity) hε
      _≤(5*X)^ε/ε := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) hK hε.le) hε.le
      _=_ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤5) (by linarith : (0:ℝ)≤X)]
  have heq : ((5:ℝ)^ε*X^ε/ε)/Real.log 2=a*X^ε := by dsimp [a]; field_simp
  have hL : (L:ℝ)≤a*X^ε := by
    rw [←heq]
    exact (le_div_iff₀ hl₂).mpr hchain
  have hone : 1≤X^ε := Real.one_le_rpow (by linarith) hε.le
  change 8401+(L:ℝ)≤(8401+a)*X^ε
  nlinarith

/-- The shell cutoff is converted to its natural floor without losing sources. -/
theorem coordinate_ruling_subpower : CF15CoordinateRulingSubpower := by
  intro hThue ε hε
  obtain ⟨C,hC,hbound⟩ := ruling_log_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro X hX i q S hS
  let N := Nat.floor (2*X)
  have hcount := coordinate_ruling_count hThue i q N S (by
    intro n hn
    obtain ⟨hnX,b,d,u,v,hs,hq⟩ := hS n hn
    exact ⟨Nat.le_floor hnX,b,d,u,v,hs,hq⟩)
  calc
    (S.card:ℝ)≤8401+(Nat.log 2 (2*N+1):ℝ) := by exact_mod_cast hcount
    _≤C*X^ε := hbound X hX N (Nat.floor_le (by linarith))

end
end P0365Subquarter
