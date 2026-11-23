import PaperTargets.ResidualProfiles
import PaperProofs.CanonicalSource

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- The actual consecutive-pair equations control the two box products without
excluding kernels or multipliers equal to one. -/
theorem actual_box_product_bounds : CF04ActualBoxProductBounds := by
  intro X B E hX hB hE n b d u v hs hbox
  rcases hbox with ⟨_,hn,hb,hb',hd,hd'⟩
  have hsource := additive_and_integer_source n b d u v hs
  have hprodN : n*(n+1)=(b*d)^3*(u*v)^2 := by
    calc
      n*(n+1)=(b^3*u^2)*(d^3*v^2) := congrArg₂ (fun x y : ℕ => x*y)
        hs.2.2.2.2.2.2.1 hsource.2.1
      _ = (b*d)^3*(u*v)^2 := by ring
  have hprod : (n:ℝ)*((n:ℝ)+1)=(b*d:ℝ)^3*(u*v:ℝ)^2 := by
    exact_mod_cast hprodN
  have hlo : B*E≤(b*d:ℝ) :=
    mul_le_mul hb hd hE.le (Nat.cast_nonneg b)
  have hhi : (b*d:ℝ)≤(2*B)*(2*E) :=
    mul_le_mul hb' hd' (Nat.cast_nonneg d) (by positivity)
  have hpow := pow_le_pow_left₀ (mul_pos hB hE).le hlo 3
  have hn' : (n:ℝ)+1≤3*X := by linarith
  have hnn := mul_le_mul hn hn' (by positivity : (0:ℝ)≤(n:ℝ)+1)
    (by positivity : (0:ℝ)≤2*X)
  refine ⟨by nlinarith only [hhi],?_⟩
  calc
    (u*v:ℝ)^2*(B*E)^3 ≤ (u*v:ℝ)^2*(b*d:ℝ)^3 :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = (n:ℝ)*((n:ℝ)+1) := by nlinarith only [hprod]
    _ ≤ 6*X^2 := by nlinarith only [hnn]

/-- One explicit logarithmic threshold absorbs the fixed box constants before
any scale, box or actual source is selected. -/
theorem residual_compact_profile : CF04ResidualCompactProfile := by
  have ht : 0<profileTheta := by norm_num [profileTheta]
  let A : ℝ := 2*Real.log 4/profileTheta
  refine ⟨max 32 (Real.exp A),le_max_left _ _,?_⟩
  intro X hX B E hB hE n b d u v hs hbox hbd hq
  have hX₃₂ : 32≤X := (le_max_left _ _).trans hX
  have hX₁ : 1≤X := by linarith
  have hXp : 0<X := by linarith
  have hlog : 0<Real.log X := Real.log_pos (by linarith)
  have hA : A≤Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos A) ((le_max_right _ _).trans hX)
    simpa only [Real.log_exp] using hh
  have h₄ : Real.log 4≤(profileTheta/2)*Real.log X := by
    have hh := (div_le_iff₀ ht).mp hA
    nlinarith only [hh]
  have h₆ : Real.log 6≤profileTheta*Real.log X := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<6) (by norm_num : (6:ℝ)≤4^2)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  let P : ℝ := B*E
  let Q : ℝ := (u*v:ℝ)
  have hP : 0<P := mul_pos hB hE
  have hu : (0:ℝ)<u := by exact_mod_cast hs.2.2.1
  have hv : (0:ℝ)<v := by exact_mod_cast hs.2.2.2.1
  have hQ : 0<Q := mul_pos hu hv
  have hb : (0:ℝ)<b := by exact_mod_cast hs.1
  have hd : (0:ℝ)<d := by exact_mod_cast hs.2.1
  obtain ⟨hbd',hqP⟩ := actual_box_product_bounds X B E hX₁ hB hE n b d u v hs hbox
  have hbdlog := Real.log_lt_log (Real.rpow_pos_of_pos hXp profileTheta) hbd
  rw [Real.log_rpow hXp] at hbdlog
  have hbdlog' := Real.log_le_log (mul_pos hb hd) hbd'
  change Real.log (b*d:ℝ)≤Real.log (4*P) at hbdlog'
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hP.ne'] at hbdlog'
  have hqlog := Real.log_lt_log (Real.rpow_pos_of_pos hXp profileTheta) hq
  rw [Real.log_rpow hXp] at hqlog
  change profileTheta*Real.log X<Real.log Q at hqlog
  have hprodlog := Real.log_le_log (by positivity : 0<Q^2*P^3) hqP
  have hlogQP : Real.log (Q^2*P^3)=2*Real.log Q+3*Real.log P := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
    norm_num
  have hlogX : Real.log (6*X^2)=Real.log 6+2*Real.log X := by
    rw [Real.log_mul (by norm_num : (6:ℝ)≠0) (by positivity),Real.log_pow]
    norm_num
  rw [hlogQP,hlogX] at hprodlog
  let ψ : ℝ := Real.log P/Real.log X
  have hψlo : profileTheta/2≤ψ := by
    apply (le_div_iff₀ hlog).mpr
    linarith
  have hψhi : ψ≤(2/3)*(1-profileTheta/2) := by
    apply (div_le_iff₀ hlog).mpr
    nlinarith only [hqlog,hprodlog,h₆]
  have hqlo : profileTheta/2≤1-(3/2)*ψ := by linarith
  have hm := mul_le_mul hψlo hqlo (by positivity : (0:ℝ)≤profileTheta/2)
    (le_trans (by positivity : (0:ℝ)≤profileTheta/2) hψlo)
  refine ⟨ψ,?_,hψlo,hψhi,hqlo,?_⟩
  · rw [Real.rpow_def_of_pos hXp]
    have he : Real.log X*ψ=Real.log P := by
      dsimp [ψ]
      field_simp
    rw [he,Real.exp_log hP]
  · dsimp [profileM0]
    nlinarith only [hm]

end
end P0365Subquarter
