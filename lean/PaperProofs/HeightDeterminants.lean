import PaperTargets.HeightDeterminants
import PaperProofs.RootDeterminants
import PaperProofs.UpperHeightSources

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem fin_value_sum (N : ℕ) :
    (∑ i : Fin (N+1), (i.val:ℝ))=(N:ℝ)*((N:ℝ)+1)/2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.cast_zero,Fin.val_succ,
      zero_add,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_succ,mul_one]
    rw [ih]
    ring

private theorem rectangular_exponent_sums (A C : ℕ) :
    (∑ j : RectangularIndex A C, (j.1.val:ℝ))=
      (Fintype.card (RectangularIndex A C):ℝ)*(A:ℝ)/2 ∧
    (∑ j : RectangularIndex A C, (j.2.val:ℝ))=
      (Fintype.card (RectangularIndex A C):ℝ)*(C:ℝ)/2 := by
  have hc : (Fintype.card (RectangularIndex A C):ℝ)=((A:ℝ)+1)*((C:ℝ)+1) := by
    simp [RectangularIndex,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  constructor
  · change (∑ j : Fin (A+1)×Fin (C+1), (j.1.val:ℝ))=_
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one]
    rw [←Finset.mul_sum,fin_value_sum,hc]
    ring
  · change (∑ j : Fin (A+1)×Fin (C+1), (j.2.val:ℝ))=_
    rw [Fintype.sum_prod_type]
    simp only [fin_value_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    rw [hc]
    ring

/-- Rectangular exponent sums and the ratio coupling give the symmetric
height. Only positive scale products are logged. -/
theorem rectangular_scale_products : CF04RectangularScaleProducts := by
  classical
  intro A C
  let H : ℝ := Fintype.card (RectangularIndex A C)
  let γ : ℝ := H/2*((A:ℝ)+(3/2)*(C:ℝ))
  let K : ℝ := Real.exp (γ*Real.log 2)
  have hγ : 0≤γ := by dsimp [γ,H]; positivity
  refine ⟨K,?_,?_⟩
  · dsimp [K]
    calc
      1=Real.exp 0 := by simp
      _≤Real.exp (γ*Real.log 2) := Real.exp_le_exp.mpr
        (mul_nonneg hγ (Real.log_nonneg (by norm_num)))
  · intro B E U V t hB hE hU hV ht htcap hratio d u hdu
    let R (i : RectangularIndex A C) : ℝ := rectangularRowScale A C (d i) (u i)
    let S (j : RectangularIndex A C) : ℝ := rectangularColumnScale t j
    have hd (i : RectangularIndex A C) : 0<(d i:ℝ) := by exact_mod_cast (hdu i).1
    have hu (i : RectangularIndex A C) : 0<(u i:ℝ) := by exact_mod_cast (hdu i).2.1
    have hR (i : RectangularIndex A C) : 0<R i := by
      dsimp [R,rectangularRowScale]; exact mul_pos (pow_pos (hd i) _) (pow_pos (hu i) _)
    have hS (j : RectangularIndex A C) : 0<S j := by
      dsimp [S,rectangularColumnScale]
      exact mul_pos (pow_pos ht _) (pow_pos (Real.rpow_pos_of_pos ht _) _)
    have hRp : 0<∏ i, R i := Finset.prod_pos (fun i _ => hR i)
    have hSp : 0<∏ j, S j := Finset.prod_pos (fun j _ => hS j)
    have hrow (i : RectangularIndex A C) :
        Real.log (R i)≤(A:ℝ)*Real.log E+(C:ℝ)*Real.log U := by
      dsimp [R,rectangularRowScale]
      rw [Real.log_mul (pow_pos (hd i) _).ne' (pow_pos (hu i) _).ne',
        Real.log_pow,Real.log_pow]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (Real.log_le_log (hd i) (hdu i).2.2.1) (Nat.cast_nonneg A))
        (mul_le_mul_of_nonneg_left (Real.log_le_log (hu i) (hdu i).2.2.2) (Nat.cast_nonneg C))
    have hrows : Real.log (∏ i, R i)≤H*((A:ℝ)*Real.log E+(C:ℝ)*Real.log U) := by
      rw [Real.log_prod (fun i _ => (hR i).ne')]
      calc
        _≤∑ _i : RectangularIndex A C, ((A:ℝ)*Real.log E+(C:ℝ)*Real.log U) :=
          Finset.sum_le_sum (fun i _ => hrow i)
        _=_ := by simp [H]; ring
    have hcol (j : RectangularIndex A C) : Real.log (S j)=
        (j.1.val:ℝ)*Real.log t+(j.2.val:ℝ)*((3/2)*Real.log t) := by
      dsimp [S,rectangularColumnScale]
      rw [Real.log_mul (pow_pos ht _).ne' (pow_pos (Real.rpow_pos_of_pos ht _) _).ne',
        Real.log_pow,Real.log_pow,Real.log_rpow ht]
    have hcols : Real.log (∏ j, S j)=γ*Real.log t := by
      rw [Real.log_prod (fun j _ => (hS j).ne')]
      simp_rw [hcol]
      rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul]
      obtain ⟨hA,hC⟩ := rectangular_exponent_sums A C
      rw [hA,hC]
      dsimp [γ,H]
      ring
    have hlogt : Real.log t≤Real.log 2+Real.log B-Real.log E := by
      have hh := Real.log_le_log ht htcap
      rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (div_pos hB hE).ne',
        Real.log_div hB.ne' hE.ne'] at hh
      linarith
    have hlogratio := congrArg Real.log hratio
    rw [Real.log_div hV.ne' hU.ne',Real.log_rpow (div_pos hB hE),
      Real.log_div hB.ne' hE.ne'] at hlogratio
    have hVlog : Real.log V=Real.log U+(3/2)*(Real.log B-Real.log E) := by
      linarith
    have heq : H*((A:ℝ)*Real.log E+(C:ℝ)*Real.log U)+
        γ*(Real.log 2+Real.log B-Real.log E)=
        γ*Real.log 2+rectangularHeightExponent A C B E U V := by
      dsimp [γ,H,rectangularHeightExponent]
      rw [Real.log_mul hB.ne' hE.ne',Real.log_mul hU.ne' hV.ne',hVlog]
      ring
    have htotal : Real.log ((∏ i, R i)*(∏ j, S j))≤
        γ*Real.log 2+rectangularHeightExponent A C B E U V := by
      rw [Real.log_mul hRp.ne' hSp.ne',hcols]
      calc
        _≤H*((A:ℝ)*Real.log E+(C:ℝ)*Real.log U)+
            γ*(Real.log 2+Real.log B-Real.log E) :=
          add_le_add hrows (mul_le_mul_of_nonneg_left hlogt hγ)
        _=_ := heq
    change (∏ i, R i)*(∏ j, S j)≤K*Real.exp (rectangularHeightExponent A C B E U V)
    calc
      _=Real.exp (Real.log ((∏ i, R i)*(∏ j, S j))) :=
        (Real.exp_log (mul_pos hRp hSp)).symm
      _≤Real.exp (γ*Real.log 2+rectangularHeightExponent A C B E U V) :=
        Real.exp_le_exp.mpr htotal
      _=_ := by rw [Real.exp_add]

private theorem multiplier_ratio (X B E : ℝ) (hX : 0<X) (hB : 0<B) (hE : 0<E) :
    reussMultiplierScale X E/reussMultiplierScale X B=(B/E)^(3/2:ℝ) := by
  dsimp [reussMultiplierScale]
  rw [Real.div_rpow hB.le hE.le]
  field_simp

/-- Actual original source ranges supply the row heights and interval cap;
the four-times heights retain exactly the needed ratio coupling. -/
theorem actual_height_determinant : CF04ActualHeightDeterminant := by
  classical
  intro A C
  obtain ⟨K₁,hK₁,hdet⟩ := actual_rectangular_determinant A C
  obtain ⟨K₂,hK₂,hprod⟩ := rectangular_scale_products A C
  refine ⟨K₁*K₂,?_,?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hK₁) (sub_nonneg.mpr hK₂)]
  · intro X M B E t hX hM hMX hB hE ht n b d u v hs hbox hint
    have hXp : 0<X := by linarith
    have hU : 0<reussMultiplierScale X B := by dsimp [reussMultiplierScale]; positivity
    have hV : 0<reussMultiplierScale X E := by dsimp [reussMultiplierScale]; positivity
    let i₀ : RectangularIndex A C := (0,0)
    have hdp : 0<(d i₀:ℝ) := by exact_mod_cast (hs i₀).2.1
    have htd : t*(d i₀:ℝ)≤(b i₀:ℝ) := (le_div_iff₀ hdp).mp (hint i₀).1
    have htcap : t≤2*((4*B)/(4*E)) := by
      have hh : t*E≤2*B :=
        (mul_le_mul_of_nonneg_left (hbox i₀).2.2.2.2.1 ht.le).trans
          (htd.trans (hbox i₀).2.2.2.1)
      have hh' : t≤(2*B)/E := (le_div_iff₀ hE).mpr hh
      have he : 2*((4*B)/(4*E))=(2*B)/E := by ring
      rwa [he]
    have hratio : (4*reussMultiplierScale X E)/(4*reussMultiplierScale X B)=
        ((4*B)/(4*E))^(3/2:ℝ) := by
      have h₁ : (4*reussMultiplierScale X E)/(4*reussMultiplierScale X B)=
          reussMultiplierScale X E/reussMultiplierScale X B := by ring
      have h₂ : (4*B)/(4*E)=B/E := by ring
      rw [h₁,h₂]
      exact multiplier_ratio X B E hXp hB hE
    have hrows (i : RectangularIndex A C) : 0<d i ∧ 0<u i ∧
        (d i:ℝ)≤4*E ∧ (u i:ℝ)≤4*reussMultiplierScale X B := by
      obtain ⟨_,_,_,_,_,hu,_,_⟩ :=
        actual_multiplier_ranges X B E hX hB hE _ _ _ _ _ (hs i) (hbox i)
      exact ⟨(hs i).2.1,(hs i).2.2.1,by linarith [(hbox i).2.2.2.2.2],by linarith⟩
    have hp := hprod (4*B) (4*E) (4*reussMultiplierScale X B)
      (4*reussMultiplierScale X E) t (by positivity) (by positivity)
      (by positivity) (by positivity) ht htcap hratio d u hrows
    have hd := hdet X M t hX hM hMX ht n b d u v hs (fun i => (hbox i).1) hint
    calc
      _≤(∏ i, rectangularRowScale A C (d i) (u i))*
          (∏ j : RectangularIndex A C, rectangularColumnScale t j)*
          (K₁*Real.exp (-latticeDeterminantLower (Fintype.card (RectangularIndex A C))
            (Real.log M) (Real.log X))) := by simpa only [mul_assoc] using hd
      _≤(K₂*Real.exp (rectangularHeightExponent A C (4*B) (4*E)
          (4*reussMultiplierScale X B) (4*reussMultiplierScale X E)))*
          (K₁*Real.exp (-latticeDeterminantLower (Fintype.card (RectangularIndex A C))
            (Real.log M) (Real.log X))) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg (by linarith) (Real.exp_pos _).le)
      _=_ := by rw [sub_eq_add_neg,Real.exp_add]; ring

end
end P0365Subquarter
