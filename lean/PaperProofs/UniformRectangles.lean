import PaperTargets.UniformRectangles
import PaperProofs.HeightDeterminants
import PaperProofs.ReussLogScale

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- A fixed finite degree range and its later constant threshold pay the
retained lattice boundary error, using exactly the available positive slack. -/
theorem uniform_rectangle_slack : CF04UniformRectangleSlack := by
  classical
  intro δ c₀ hδ hδ₁ hc₀ hc₀₁
  have hroot : 1<Real.sqrt (1+δ) :=
    (Real.lt_sqrt (by norm_num : (0:ℝ)≤1)).mpr (by nlinarith)
  let g : ℝ := Real.sqrt (1+δ)-1
  have hg : 0<g := by dsimp [g]; linarith
  let C : ℕ := Nat.ceil (3/(g*c₀))+1
  have hC : 1≤C := by dsimp [C]; omega
  have hC₀ : 0≤(C:ℝ) := Nat.cast_nonneg C
  have hcost : 3≤(C:ℝ)*g*c₀ := by
    have hh : 3/(g*c₀)≤(C:ℝ) := calc
      _≤(Nat.ceil (3/(g*c₀)):ℝ) := Nat.le_ceil _
      _≤(C:ℝ) := by exact_mod_cast (show Nat.ceil (3/(g*c₀))≤C by dsimp [C]; omega)
    have hh' := (div_le_iff₀ (mul_pos hg hc₀)).mp hh
    nlinarith only [hh']
  let Amax : ℕ := Nat.ceil (2*(C:ℝ)/c₀)
  refine ⟨C,Amax,hC,?_⟩
  intro K hK
  let Q : ℝ := ∑ j : Fin (Amax+1), K j.val
  have hKn (j : Fin (Amax+1)) : 0≤K j.val :=
    le_trans (by norm_num : (0:ℝ)≤1) (hK j.val (Nat.le_of_lt_succ j.is_lt))
  have hQ : 0≤Q := Finset.sum_nonneg (fun j _ => hKn j)
  refine ⟨1+Q,by linarith,?_⟩
  intro B S T a hB hSlo hShi hTlo hThi ha haB hbudget
  have hB₁ : 1≤B := by linarith
  have hBp : 0<B := by linarith
  have hS : 0<S := (mul_pos hc₀ hBp).trans_le hSlo
  have hT : 0<T := (mul_pos hc₀ hBp).trans_le hTlo
  let A : ℕ := Nat.floor ((C:ℝ)*T/S)
  have hA : (A:ℝ)≤(C:ℝ)*T/S := Nat.floor_le (by positivity)
  have hA' : (C:ℝ)*T/S≤(A:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hTS : T*c₀≤2*S := by
    have hh := mul_le_mul_of_nonneg_right hThi hc₀.le
    nlinarith only [hh,hSlo]
  have hAmax : A≤Amax := by
    have hh : (C:ℝ)*T/S≤2*(C:ℝ)/c₀ := by
      apply (div_le_div_iff₀ hS hc₀).mpr
      have hh := mul_le_mul_of_nonneg_left hTS hC₀
      nlinarith only [hh]
    have hh' : (A:ℝ)≤(Amax:ℝ) := hA.trans (hh.trans (Nat.le_ceil _))
    exact_mod_cast hh'
  have hKA : 0≤K A := le_trans (by norm_num : (0:ℝ)≤1) (hK A hAmax)
  have hKQ : K A≤Q := by
    exact Finset.single_le_sum (fun j _ => hKn j)
      (Finset.mem_univ (⟨A,Nat.lt_succ_iff.mpr hAmax⟩ : Fin (Amax+1)))
  let H : ℕ := Fintype.card (RectangularIndex A C)
  have hcard : (H:ℝ)=((A:ℝ)+1)*((C:ℝ)+1) := by
    simp [H,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hHpos : 0<H := by simp [H]
  have hH₁ : (1:ℝ)≤H := by exact_mod_cast (Nat.succ_le_of_lt hHpos)
  have hH₀ : 0≤(H:ℝ) := Nat.cast_nonneg H
  have hHlower : (C:ℝ)^2*T/S≤(H:ℝ) := calc
    _=((C:ℝ)*T/S)*(C:ℝ) := by ring
    _≤((A:ℝ)+1)*(C:ℝ) := mul_le_mul_of_nonneg_right hA' hC₀
    _≤((A:ℝ)+1)*((C:ℝ)+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _=(H:ℝ) := hcard.symm
  have hSH : (C:ℝ)^2*T≤(H:ℝ)*S := (div_le_iff₀ hS).mp hHlower
  have hsquare : ((3/2:ℝ)*(C:ℝ)*Real.sqrt (1+δ)*T)^2≤2*a*B*(H:ℝ) := by
    calc
      _=(9/4:ℝ)*(1+δ)*T*((C:ℝ)^2*T) := by
        simp only [mul_pow]
        rw [Real.sq_sqrt (by linarith : (0:ℝ)≤1+δ)]
        ring
      _≤(9/4:ℝ)*(1+δ)*T*((H:ℝ)*S) :=
        mul_le_mul_of_nonneg_left hSH (by positivity)
      _=((9/8:ℝ)*(1+δ)*S*T)*(2*(H:ℝ)) := by ring
      _≤(a*B)*(2*(H:ℝ)) := mul_le_mul_of_nonneg_right hbudget (by positivity)
      _=2*a*B*(H:ℝ) := by ring
  have hdecay : (H:ℝ)*(C:ℝ)*Real.sqrt (1+δ)*T≤
      (2/3:ℝ)*(H:ℝ)*Real.sqrt (2*a*B*(H:ℝ)) := by
    calc
      _=((2/3:ℝ)*(H:ℝ))*((3/2:ℝ)*(C:ℝ)*Real.sqrt (1+δ)*T) := by ring
      _≤_ := mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hsquare) (by positivity)
  have hAS : (A:ℝ)*S≤(C:ℝ)*T := (le_div_iff₀ hS).mp hA
  have hheight : (H:ℝ)/2*((A:ℝ)*S+(C:ℝ)*T)≤(H:ℝ)*(C:ℝ)*T := by
    calc
      _≤(H:ℝ)/2*((C:ℝ)*T+(C:ℝ)*T) :=
        mul_le_mul_of_nonneg_left
          (show (A:ℝ)*S+(C:ℝ)*T≤(C:ℝ)*T+(C:ℝ)*T from add_le_add hAS le_rfl)
          (by positivity : (0:ℝ)≤(H:ℝ)/2)
      _=_ := by ring
  have hmargin : 3*B≤(C:ℝ)*g*T := by
    calc
      _≤((C:ℝ)*g*c₀)*B := mul_le_mul_of_nonneg_right hcost hBp.le
      _=((C:ℝ)*g)*(c₀*B) := by ring
      _≤_ := mul_le_mul_of_nonneg_left hTlo (mul_nonneg hC₀ hg.le)
  have hmarginH := mul_le_mul_of_nonneg_left hmargin hH₀
  have hgap : (H:ℝ)/2*((A:ℝ)*S+(C:ℝ)*T)-latticeDeterminantLower H a B≤
      -(H:ℝ)*B := by
    dsimp [latticeDeterminantLower]
    dsimp [g] at hmarginH
    nlinarith only [hheight,hdecay,hmarginH]
  have hgap' : (H:ℝ)/2*((A:ℝ)*S+(C:ℝ)*T)-latticeDeterminantLower H a B≤-B :=
    hgap.trans (by nlinarith only [mul_le_mul_of_nonneg_right hH₁ hBp.le])
  have hKexp : K A<Real.exp B := by
    have hh := Real.add_one_le_exp B
    linarith
  have hstrict : K A*Real.exp (-B)<1 := by
    rw [Real.exp_neg,←div_eq_mul_inv]
    exact (div_lt_one (Real.exp_pos B)).mpr hKexp
  refine ⟨A,hAmax,?_⟩
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgap') hKA).trans_lt hstrict

private theorem enlarged_product_log (B E : ℝ) (hB : 0<B) (hE : 0<E) :
    Real.log ((4*B)*(4*E))=Real.log (B*E)+Real.log 16 := by
  have he : (4*B)*(4*E)=16*(B*E) := by ring
  rw [he,Real.log_mul (by norm_num : (16:ℝ)≠0) (mul_pos hB hE).ne']
  ring

private theorem nominal_multiplier_product_log (X B E : ℝ)
    (hX : 0<X) (hB : 0<B) (hE : 0<E) :
    Real.log (reussMultiplierScale X B*reussMultiplierScale X E)=
      Real.log X-(3/2)*Real.log (B*E) := by
  have hU : 0<reussMultiplierScale X B := by dsimp [reussMultiplierScale]; positivity
  have hV : 0<reussMultiplierScale X E := by dsimp [reussMultiplierScale]; positivity
  rw [Real.log_mul hU.ne' hV.ne']
  dsimp [reussMultiplierScale]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),Real.log_rpow hX,
    Real.log_rpow hB,Real.log_rpow hE,Real.log_mul hB.ne' hE.ne']
  ring

/-- Rounded compact profiles supply the numeric budget before the source tuple;
the bound on each actual integer determinant is then strictly below one. -/
theorem actual_uniform_minor_vanishing : CF04ActualUniformMinorVanishing := by
  classical
  intro δ hδ hδ₁
  have hc₀ : 0<profileTheta/2 := by norm_num [profileTheta]
  have hc₀₁ : profileTheta/2≤1 := by norm_num [profileTheta]
  obtain ⟨C,Amax,hC,hchoose⟩ := uniform_rectangle_slack (δ/2) (profileTheta/2)
    (by linarith) (by linarith) hc₀ hc₀₁
  choose K hK hdet using (fun A : ℕ => actual_height_determinant A C)
  obtain ⟨L₀,hL₀,huniform⟩ := hchoose K (fun A _ => hK A)
  obtain ⟨X₁,hX₁,hrounded⟩ := rounded_log_slack δ (Real.log 16) hδ hδ₁
    (Real.log_nonneg (by norm_num))
  refine ⟨C,Amax,hC,max X₁ (Real.exp L₀),hX₁.trans (le_max_left _ _),?_⟩
  intro X ψ B E t hX hψlo hψhi hB hE ht hBE
  have hX₁' : X₁≤X := (le_max_left _ _).trans hX
  have hX₃₂ : 32≤X := hX₁.trans hX₁'
  have hXp : 0<X := by linarith
  have hXone : 1≤X := by linarith
  have hL : 0<Real.log X := Real.log_pos (by linarith)
  have hLL₀ : L₀≤Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos L₀) ((le_max_right _ _).trans hX)
    simpa only [Real.log_exp] using hh
  have hU : 0<reussMultiplierScale X B := by dsimp [reussMultiplierScale]; positivity
  have hV : 0<reussMultiplierScale X E := by dsimp [reussMultiplierScale]; positivity
  let S : ℝ := Real.log ((4*B)*(4*E))
  let T : ℝ := Real.log ((4*reussMultiplierScale X B)*(4*reussMultiplierScale X E))
  let a : ℝ := Real.log (roundedHeight X ψ δ:ℝ)
  have hlogBE : Real.log (B*E)=ψ*Real.log X := by rw [hBE,Real.log_rpow hXp]
  have hS : S=ψ*Real.log X+Real.log 16 := by
    dsimp [S]
    rw [enlarged_product_log B E hB hE,hlogBE]
  have hT : T=(1-(3/2)*ψ)*Real.log X+Real.log 16 := by
    dsimp [T]
    rw [enlarged_product_log _ _ hU hV,nominal_multiplier_product_log X B E hXp hB hE,hlogBE]
    ring
  have hκ : 0≤Real.log 16 := Real.log_nonneg (by norm_num)
  have hκX : Real.log 16≤Real.log X := Real.log_le_log (by norm_num) (by linarith)
  have hψ₀ : 0≤ψ := by linarith
  have hψ₁ : ψ≤1 := by have hh := hc₀.le; linarith
  have hqlo : profileTheta/2≤1-(3/2)*ψ := by linarith
  have hqhi : 1-(3/2)*ψ≤1 := by linarith
  have hSlo : profileTheta/2*Real.log X≤S := by
    rw [hS]
    linarith [mul_le_mul_of_nonneg_right hψlo hL.le]
  have hShi : S≤2*Real.log X := by
    rw [hS]
    linarith [mul_le_mul_of_nonneg_right hψ₁ hL.le]
  have hTlo : profileTheta/2*Real.log X≤T := by
    rw [hT]
    linarith [mul_le_mul_of_nonneg_right hqlo hL.le]
  have hThi : T≤2*Real.log X := by
    rw [hT]
    linarith [mul_le_mul_of_nonneg_right hqhi hL.le]
  obtain ⟨ha₀,haB,hbudget⟩ := hrounded X hX₁' ψ hψlo hψhi
  have hap : 0<a := by
    have hh : 0<(9/32:ℝ)*profileTheta^2*Real.log X := by
      have hh : 0<profileTheta := by norm_num [profileTheta]
      positivity
    exact hh.trans_le ha₀
  have hbudget' : (9/8)*(1+δ/2)*S*T≤a*Real.log X := by
    rw [←hS,←hT] at hbudget
    have he : (9/8:ℝ)*(1+δ/2)*(S*T/Real.log X)=
        ((9/8:ℝ)*(1+δ/2)*S*T)/Real.log X := by ring
    rw [he] at hbudget
    exact (div_le_iff₀ hL).mp hbudget
  obtain ⟨A,hA,hstrict⟩ := huniform (Real.log X) S T a hLL₀
    hSlo hShi hTlo hThi hap haB hbudget'
  have hMp : 0<(roundedHeight X ψ δ:ℝ) := by
    by_contra hh
    have hz : (roundedHeight X ψ δ:ℝ)=0 :=
      le_antisymm (not_lt.mp hh) (Nat.cast_nonneg _)
    dsimp [a] at hap
    rw [hz,Real.log_zero] at hap
    linarith
  have hM : 1<(roundedHeight X ψ δ:ℝ) := by
    have hh := Real.exp_lt_exp.mpr hap
    simpa only [a,Real.exp_zero,Real.exp_log hMp] using hh
  have hMX : (roundedHeight X ψ δ:ℝ)≤X := (Real.log_le_log_iff hMp hXp).mp haB
  refine ⟨A,hA,?_⟩
  intro n b d u v hs hbox hint
  have hd := hdet A X (roundedHeight X ψ δ:ℝ) B E t hXone hM hMX hB hE ht
    n b d u v hs hbox hint
  change |((rectangularSourceMatrix A C b d u v).det:ℝ)|≤K A*Real.exp
    (((Fintype.card (RectangularIndex A C):ℝ)/2)*((A:ℝ)*S+(C:ℝ)*T)-
      latticeDeterminantLower (Fintype.card (RectangularIndex A C)) a (Real.log X)) at hd
  obtain ⟨hlo,hhi⟩ := abs_lt.mp (hd.trans_lt hstrict)
  have hlo' : (-1:ℤ)<(rectangularSourceMatrix A C b d u v).det := by exact_mod_cast hlo
  have hhi' : (rectangularSourceMatrix A C b d u v).det<(1:ℤ) := by exact_mod_cast hhi
  omega

end
end P0365Subquarter
