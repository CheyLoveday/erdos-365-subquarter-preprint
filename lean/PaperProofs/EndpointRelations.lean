import PaperTargets.EndpointRelations
import PaperProofs.CanonicalSource
import Mathlib.Algebra.MvPolynomial.CommRing

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private def endpointPolynomial (b d : ℕ) : SourcePolynomial :=
  MvPolynomial.C (d:ℤ)*MvPolynomial.X 0-MvPolynomial.C (b:ℤ)

private theorem shell_kernel_height (X : ℝ) (hX : 32≤X)
    (n b d u v : ℕ) (hs : PairSource n b d u v) (hn : (n:ℝ)≤2*X) :
    (b:ℝ)≤3*X ∧ (d:ℝ)≤3*X := by
  have hbounds := source_bounds n b d u v hs
  have hb : b≤n := (Nat.le_self_pow (by decide : 3≠0) b).trans hbounds.1
  have hd : d≤n+1 := (Nat.le_self_pow (by decide : 3≠0) d).trans hbounds.2.2.1
  have hb' : (b:ℝ)≤(n:ℝ) := by exact_mod_cast hb
  have hd' : (d:ℝ)≤(n:ℝ)+1 := by exact_mod_cast hd
  constructor <;> linarith

private theorem endpoint_coefficient (b d : ℕ) (e : Fin 2 →₀ ℕ) :
    (endpointPolynomial b d).coeff e =
      (d:ℤ)*(if Finsupp.single (0:Fin 2) 1=e then 1 else 0)-
        (if 0=e then (b:ℤ) else 0) := by
  classical
  simp only [endpointPolynomial,MvPolynomial.coeff_sub,MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X,MvPolynomial.coeff_C]

private theorem endpoint_leading_coefficient (b d : ℕ) :
    (endpointPolynomial b d).coeff (Finsupp.single (0:Fin 2) 1)=(d:ℤ) := by
  have hsingle : (0 : Fin 2 →₀ ℕ)≠Finsupp.single (0:Fin 2) 1 := by
    intro hh
    have h₀ := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hh
    norm_num at h₀
  rw [endpoint_coefficient]
  simp [hsingle]

private theorem endpoint_nonzero (b d : ℕ) (hd : 0<d) : endpointPolynomial b d≠0 := by
  intro hz
  have hh := congrArg (fun F : SourcePolynomial => F.coeff (Finsupp.single (0:Fin 2) 1)) hz
  rw [endpoint_leading_coefficient] at hh
  have hd₀ : d=0 := by simpa using hh
  omega

private theorem endpoint_degree (b d : ℕ) : (endpointPolynomial b d).totalDegree≤1 := by
  calc
    _ ≤ (MvPolynomial.C (d:ℤ)*MvPolynomial.X (0:Fin 2)).totalDegree :=
      MvPolynomial.totalDegree_sub_C_le _ _
    _ ≤ (MvPolynomial.C (d:ℤ) : SourcePolynomial).totalDegree+
        (MvPolynomial.X (0:Fin 2) : SourcePolynomial).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = 1 := by simp only [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X,zero_add]

private theorem endpoint_height (X : ℝ) (b d : ℕ)
    (hb : (b:ℝ)≤3*X) (hd : (d:ℝ)≤3*X) :
    ∀ e, |((endpointPolynomial b d).coeff e:ℝ)|≤3*X := by
  classical
  intro e
  by_cases he₀ : e=0
  · subst e
    rw [endpoint_coefficient]
    simpa using hb
  · by_cases he₁ : e=Finsupp.single (0:Fin 2) 1
    · subst e
      rw [endpoint_leading_coefficient]
      simpa using hd
    · have hzero : (endpointPolynomial b d).coeff e=0 := by
        rw [endpoint_coefficient]
        simp [he₀,he₁,eq_comm]
      rw [hzero]
      simpa using (Nat.cast_nonneg b).trans hb

private theorem endpoint_evaluation (b d u v b₀ d₀ : ℕ) (hd : 0<d) (hd₀ : 0<d₀)
    (hr : (b:ℝ)/d=(b₀:ℝ)/d₀) :
    polynomialValue (endpointPolynomial b₀ d₀) (sourcePoint b d u v)=0 := by
  have hdR : (d:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hd₀R : (d₀:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd₀)
  have hc := (div_eq_div_iff hdR hd₀R).mp hr
  have hq : (d₀:ℚ)*(b:ℚ)=(b₀:ℚ)*(d:ℚ) := by
    exact_mod_cast (show (d₀:ℝ)*(b:ℝ)=(b₀:ℝ)*(d:ℝ) by nlinarith [hc])
  have hdQ : (d:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have he : (d₀:ℚ)*((b:ℚ)/(d:ℚ))-(b₀:ℚ)=0 := by
    apply sub_eq_zero.mpr
    rw [←mul_div_assoc]
    exact (div_eq_iff hdQ).mpr hq
  simp only [endpointPolynomial,polynomialValue,MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_X]
  simpa [sourcePoint] using he

/-- A single actual endpoint witness supplies one integral linear relation for
all original sources there; an unattained real endpoint has no population. -/
theorem actual_endpoint_relation : CF04ActualEndpointRelation := by
  classical
  intro X hX a
  by_cases hh : ∃ n b d u v : ℕ, PairSource n b d u v ∧ (n:ℝ)≤2*X ∧ (b:ℝ)/d=a
  · obtain ⟨n,b,d,u,v,hs,hn,hr⟩ := hh
    obtain ⟨hb,hd⟩ := shell_kernel_height X hX n b d u v hs hn
    refine ⟨endpointPolynomial b d,endpoint_nonzero b d hs.2.1,
      endpoint_degree b d,endpoint_height X b d hb hd,?_⟩
    intro m b' d' u' v' hs' _ hr'
    exact endpoint_evaluation b' d' u' v' b d hs'.2.1 hs.2.1 (hr'.trans hr.symm)
  · refine ⟨1,one_ne_zero,by simp,?_,?_⟩
    · intro e
      have he : |((1:SourcePolynomial).coeff e:ℝ)|≤1 := by
        rw [MvPolynomial.coeff_one]
        split_ifs <;> norm_num
      exact he.trans (by linarith)
    · intro n b d u v hs hn hr
      exact False.elim (hh ⟨n,b,d,u,v,hs,hn,hr⟩)

private theorem endpoint_product_height (X H C : ℝ) (hX : 32≤X) (hC : 0≤C)
    (F : SourcePolynomial) (hF : ∀ e, |(F.coeff e:ℝ)|≤C*X^H)
    (b d : ℕ) (hb : (b:ℝ)≤3*X) (hd : (d:ℝ)≤3*X) :
    ∀ e, |((F*endpointPolynomial b d).coeff e:ℝ)|≤6*(C+1)*X^(H+1) := by
  classical
  have hX₀ : 0<X := by linarith
  have hpow : 0≤X^H := Real.rpow_nonneg hX₀.le H
  have hprod : X^(H+1)=X^H*X := by rw [Real.rpow_add hX₀,Real.rpow_one]
  have hshift (e : Fin 2 →₀ ℕ) : |((F*MvPolynomial.X 0).coeff e:ℝ)|≤C*X^H := by
    rw [MvPolynomial.coeff_mul_X']
    split_ifs
    · exact hF _
    · simp only [Int.cast_zero,abs_zero]
      exact mul_nonneg hC hpow
  have heq : F*endpointPolynomial b d=
      MvPolynomial.C (d:ℤ)*(F*MvPolynomial.X 0)-MvPolynomial.C (b:ℤ)*F := by
    dsimp [endpointPolynomial]
    ring
  intro e
  have hcoeff : ((F*endpointPolynomial b d).coeff e:ℝ)=
      (d:ℝ)*((F*MvPolynomial.X 0).coeff e:ℝ)-(b:ℝ)*(F.coeff e:ℝ) := by
    rw [heq,MvPolynomial.coeff_sub,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_C_mul]
    push_cast
    rfl
  rw [hcoeff]
  calc
    _ ≤ |(d:ℝ)*((F*MvPolynomial.X 0).coeff e:ℝ)|+|(b:ℝ)*(F.coeff e:ℝ)| := abs_sub _ _
    _ = (d:ℝ)*|((F*MvPolynomial.X 0).coeff e:ℝ)|+(b:ℝ)*|(F.coeff e:ℝ)| := by
      simp only [abs_mul,abs_of_nonneg (show (0:ℝ)≤d from Nat.cast_nonneg d),
        abs_of_nonneg (show (0:ℝ)≤b from Nat.cast_nonneg b)]
    _ ≤ (3*X)*(C*X^H)+(3*X)*(C*X^H) := add_le_add
      (mul_le_mul hd (hshift e) (abs_nonneg _) (by positivity))
      (mul_le_mul hb (hF e) (abs_nonneg _) (by positivity))
    _ = 6*C*X^(H+1) := by rw [hprod]; ring
    _ ≤ 6*(C+1)*X^(H+1) := by
      have hp : 0≤X^(H+1) := Real.rpow_nonneg hX₀.le _
      nlinarith

/-- Adjoin one bounded actual-source endpoint factor to the supplied half-open
relation. Its fixed degree/height cost is uniform before all scales/intervals. -/
theorem closed_interval_relation : CF04ClosedIntervalRelation := by
  classical
  intro D H C _ hC
  let K : ℝ := 6*(C+1)
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro X hX a M _ _ F hFnz hFD hF hvanish
  by_cases hh : ∃ n b d u v : ℕ, PairSource n b d u v ∧ (n:ℝ)≤2*X ∧ (b:ℝ)/d=a
  · obtain ⟨n₀,b₀,d₀,u₀,v₀,hs₀,hn₀,hr₀⟩ := hh
    obtain ⟨hb,hd⟩ := shell_kernel_height X hX n₀ b₀ d₀ u₀ v₀ hs₀ hn₀
    refine ⟨F*endpointPolynomial b₀ d₀,mul_ne_zero hFnz (endpoint_nonzero b₀ d₀ hs₀.2.1),
      (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hFD (endpoint_degree b₀ d₀)),
      endpoint_product_height X H C hX hC F hF b₀ d₀ hb hd,?_⟩
    intro n b d u v hs hn hinterval
    simp only [polynomialValue,MvPolynomial.eval₂_mul]
    change polynomialValue F (sourcePoint b d u v)*
      polynomialValue (endpointPolynomial b₀ d₀) (sourcePoint b d u v)=0
    by_cases hr : a<(b:ℝ)/d
    · rw [hvanish n b d u v hs hn hr hinterval.2,zero_mul]
    · have he : (b:ℝ)/d=a := le_antisymm (le_of_not_gt hr) hinterval.1
      rw [endpoint_evaluation b d u v b₀ d₀ hs.2.1 hs₀.2.1 (he.trans hr₀.symm),mul_zero]
  · refine ⟨F,hFnz,hFD.trans (Nat.le_succ D),?_,?_⟩
    · intro e
      have hp : 0≤X^H := Real.rpow_nonneg (by linarith) H
      have hscale : X^H≤X^(H+1) := by
        rw [Real.rpow_add (by linarith : 0<X),Real.rpow_one]
        have hh := mul_nonneg (by linarith : 0≤X-1) hp
        nlinarith
      calc
        |(F.coeff e:ℝ)| ≤ C*X^H := hF e
        _ ≤ K*X^H := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hp
        _ ≤ K*X^(H+1) := mul_le_mul_of_nonneg_left hscale hK.le
    · intro n b d u v hs hn hinterval
      have hr : a<(b:ℝ)/d := by
        by_contra h
        have he : (b:ℝ)/d=a := le_antisymm (le_of_not_gt h) hinterval.1
        exact hh ⟨n,b,d,u,v,hs,hn,he⟩
      exact hvanish n b d u v hs hn hr hinterval.2

end
end P0365Subquarter
