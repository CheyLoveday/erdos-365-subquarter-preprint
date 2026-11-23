import PaperTargets.LowFactorLevels
import PaperProofs.PullbackNonpowers

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Integral Bezout constructs the proportionality scalar without dividing a
coordinate; primitivity of the second vector makes that scalar a unit. -/
theorem signed_primitive_parallel : CF15SignedPrimitiveParallel := by
  intro z w hz hw he
  obtain ⟨a,b,hzB⟩ := hz
  obtain ⟨c,d,hwB⟩ := hw
  let k : ℤ := a*w 0+b*w 1
  have hx : w 0=k*z 0 := by
    dsimp [k]
    calc
      w 0=w 0*(a*z 0+b*z 1) := by rw [hzB]; ring
      _ = _ := by linear_combination -b*he
  have hy : w 1=k*z 1 := by
    dsimp [k]
    calc
      w 1=w 1*(a*z 0+b*z 1) := by rw [hzB]; ring
      _ = _ := by linear_combination a*he
  have hprod : k*(c*z 0+d*z 1)=1 := by
    calc
      _ = c*w 0+d*w 1 := by rw [hx,hy]; ring
      _ = 1 := hwB
  have hk : IsUnit k := isUnit_iff_dvd_one.mpr ⟨c*z 0+d*z 1,hprod.symm⟩
  rcases Int.isUnit_eq_one_or hk with hk1 | hkn
  · left
    ext i; fin_cases i
    · change w 0=z 0
      rw [hx,hk1,one_mul]
    · change w 1=z 1
      rw [hy,hk1,one_mul]
  · right
    ext i; fin_cases i
    · change w 0= -z 0
      rw [hx,hkn,neg_one_mul]
    · change w 1= -z 1
      rw [hy,hkn,neg_one_mul]

/-- The affine chart counts only its nonzero-denominator parameters; infinity
is paid explicitly in the homogeneous zero count below. -/
theorem primitive_ratio_fiber : CF15PrimitiveRatioFiber := by
  classical
  intro r S hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨z,hz⟩
  · simp
  have hzS := hS z hz
  have hsub : S ⊆ {z,-z} := by
    intro w hw
    have hwS := hS w hw
    have hzQ : (z 1:ℚ) ≠ 0 := by exact_mod_cast hzS.2.1
    have hwQ : (w 1:ℚ) ≠ 0 := by exact_mod_cast hwS.2.1
    have heQ := (div_eq_div_iff hzQ hwQ).mp (hzS.2.2.trans hwS.2.2.symm)
    have he : z 0*w 1=w 0*z 1 := by exact_mod_cast heQ
    rcases signed_primitive_parallel z w hzS.1 hwS.1 he with h | h
    · simp [h]
    · simp [h]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

private theorem finite_fiber_bound {α β : Type} [DecidableEq β] (S : Finset α) (T : Finset β)
    (f : α → β) (k : ℕ) (hmap : ∀ z ∈ S, f z ∈ T)
    (hfib : ∀ r ∈ T, (S.filter (fun z => f z=r)).card ≤ k) : S.card ≤ T.card*k := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := T) (fun z hz => hmap z hz)]
  calc
    _ ≤ ∑ r ∈ T, k := Finset.sum_le_sum hfib
    _ = _ := by simp

private theorem axis_fiber_count (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, primitiveBinaryPoint z ∧ z 1=0) : S.card ≤ 2 := by
  classical
  let e : Fin 2 → ℤ := ![1,0]
  have he : primitiveBinaryPoint e := ⟨1,0,by simp [e]⟩
  have hsub : S ⊆ {e,-e} := by
    intro z hz
    have hs := hS z hz
    have hc : e 0*z 1=z 0*e 1 := by simp [e,hs.2]
    rcases signed_primitive_parallel e z he hs.1 hc with h | h <;> simp [h]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

private theorem integer_eval_cast (K : SourcePolynomial) (x y : ℤ) :
    ((MvPolynomial.eval ![x,y] K : ℤ) : ℚ)=polynomialValue K ![(x:ℚ),y] := by
  have h := MvPolynomial.hom_eval₂ K (RingHom.id ℤ) (Int.castRingHom ℚ) (![x,y] : Fin 2 → ℤ)
  change ((MvPolynomial.eval ![x,y] K : ℤ) : ℚ)=
    MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => ((![x,y] : Fin 2 → ℤ) i : ℚ)) K at h
  have he : (fun i => ((![x,y] : Fin 2 → ℤ) i : ℚ))=(![(x:ℚ),y] : Fin 2 → ℚ) := by
    ext i; fin_cases i <;> rfl
  rw [he] at h
  exact h

private theorem homogeneous_zero_cast (K : SourcePolynomial) (z : Fin 2 → ℤ)
    (hz : MvPolynomial.eval z K=0) : polynomialValue K ![(z 0:ℚ),z 1]=0 := by
  rw [← integer_eval_cast K (z 0) (z 1)]
  have he : (![z 0,z 1] : Fin 2 → ℤ)=z := by ext i; fin_cases i <;> rfl
  rw [he,hz]
  rfl

/-- The affine root count pays for infinity inside the homogeneous degree:
full affine degree excludes it, while a degree drop leaves one degree to pay. -/
theorem homogeneous_primitive_zeros : CF15HomogeneousPrimitiveZeros := by
  classical
  intro K d hK hhom S hS
  let P := binaryDehomogenize K
  obtain ⟨hdeg,hform,hPn⟩ := binary_dehomogenization K d hhom
  have hP : P ≠ 0 := hPn hK
  have hPQ : rationalPolynomial P ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hP
  let T := rulingRoots P
  let S₀ := S.filter (fun z => z 1=0)
  let S₁ := S.filter (fun z => z 1≠0)
  let ratio : (Fin 2 → ℤ) → ℚ := fun z => (z 0:ℚ)/(z 1:ℚ)
  have hroot (z : Fin 2 → ℤ) (hz : z ∈ S₁) : ratio z ∈ T := by
    obtain ⟨hzS,hy⟩ := Finset.mem_filter.mp hz
    have hzK := (hS z hzS).2
    have hzQ := homogeneous_zero_cast K z hzK
    have hyQ : (z 1:ℚ) ≠ 0 := by exact_mod_cast hy
    rw [← hform,(homogeneous_form P d hdeg).2.1 (z 0:ℚ) (z 1:ℚ) hyQ] at hzQ
    have hv : integerPolynomialValue P (ratio z)=0 := (mul_eq_zero.mp hzQ).resolve_right (pow_ne_zero _ hyQ)
    simpa only [T,rulingRoots,Multiset.mem_toFinset,Polynomial.mem_roots hPQ,Polynomial.IsRoot,integerPolynomialValue] using hv
  have hS₁ : S₁.card ≤ T.card*2 := by
    apply finite_fiber_bound S₁ T ratio 2 hroot
    intro r hr
    apply primitive_ratio_fiber r
    intro z hz
    obtain ⟨hzS₁,he⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzS,hy⟩ := Finset.mem_filter.mp hzS₁
    exact ⟨(hS z hzS).1,hy,he⟩
  have hT : T.card ≤ P.natDegree := by
    calc
      _ ≤ (rationalPolynomial P).roots.card := Multiset.toFinset_card_le _
      _ ≤ (rationalPolynomial P).natDegree := Polynomial.card_roots' _
      _ = P.natDegree := Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  have hS₀ : S₀.card ≤ 2 := by
    apply axis_fiber_count
    intro z hz
    obtain ⟨hzS,hy⟩ := Finset.mem_filter.mp hz
    exact ⟨(hS z hzS).1,hy⟩
  have hsplit : S₀.card+S₁.card=S.card := Finset.card_filter_add_card_filter_not (s := S) (fun z : Fin 2 → ℤ => z 1=0)
  by_cases hd : P.natDegree=d
  · have hempty : S₀=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzS,hy⟩ := Finset.mem_filter.mp hz
      have hpz := (hS z hzS).1
      have hxunit : IsUnit (z 0) := isCoprime_zero_right.mp (by simpa [primitiveBinaryPoint,hy] using hpz)
      have hxQ : (z 0:ℚ) ≠ 0 := by exact_mod_cast hxunit.ne_zero
      have hv := homogeneous_zero_cast K z (hS z hzS).2
      rw [hy,Int.cast_zero,← hform] at hv
      change polynomialValue (P.homogenize d) ![(z 0:ℚ),0]=0 at hv
      rw [(homogeneous_form P d hdeg).2.2 (z 0:ℚ)] at hv
      have hcoeff : P.coeff d ≠ 0 := by
        rw [← hd,Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hP
      have hcoeffQ : (P.coeff d:ℚ) ≠ 0 := by exact_mod_cast hcoeff
      exact (mul_ne_zero hcoeffQ (pow_ne_zero _ hxQ)) hv
    have hzero : S₀.card=0 := by rw [hempty]; rfl
    omega
  · have hlt : P.natDegree<d := by change P.natDegree ≤ d at hdeg; omega
    omega

private theorem level_eliminant_nonzero (G H : SourcePolynomial) (a b : ℤ)
    (hb : b ≠ 0) (hn : binaryNonproportional G H) :
    MvPolynomial.C b*G-MvPolynomial.C a*H ≠ 0 := by
  intro hz
  have he := congrArg (MvPolynomial.map (Int.castRingHom ℚ)) hz
  simp only [map_sub,map_mul,MvPolynomial.map_C,map_zero] at he
  change MvPolynomial.C (b:ℚ)*rationalBinary G-
    MvPolynomial.C (a:ℚ)*rationalBinary H=0 at he
  have hq := sub_eq_zero.mp he
  apply hn
  refine ⟨(a:ℚ)/(b:ℚ),?_⟩
  have hbQ : (b:ℚ) ≠ 0 := by exact_mod_cast hb
  apply mul_left_cancel₀ (show (MvPolynomial.C (b:ℚ) : MvPolynomial (Fin 2) ℚ) ≠ 0 by simpa using hbQ)
  rw [← mul_assoc,← MvPolynomial.C_mul]
  rw [show (b:ℚ)*((a:ℚ)/(b:ℚ))=(a:ℚ) by field_simp]
  exact hq

/-- A degree-one homogeneous eliminant contains every fixed pair of linear
levels. The primitive-direction constant two is sufficient for CF15. -/
theorem two_linear_levels : CF15TwoLinearLevels := by
  intro L₁ L₂ hL₁ hL₂ hn h₁ h₂ hh₁ hh₂ S hS
  apply homogeneous_primitive_zeros (MvPolynomial.C h₂*L₁-MvPolynomial.C h₁*L₂) 1
    (level_eliminant_nonzero L₁ L₂ h₁ h₂ hh₂ hn) ((hL₁.C_mul h₂).sub (hL₂.C_mul h₁)) S
  intro z hz
  obtain ⟨hp,h₁z,h₂z⟩ := hS z hz
  refine ⟨hp,?_⟩
  simp only [map_sub,map_mul,MvPolynomial.eval_C,h₁z,h₂z]
  ring

/-- Eliminate a nonzero linear level by squaring it. Nonproportionality of
G and L² proves the degree-two eliminant nonzero, without a conic theorem. -/
theorem linear_quadratic_levels : CF15LinearQuadraticLevels := by
  intro L G hL hG hn hLval hGval hhL hhG S hS
  have hL2 : (L^2).IsHomogeneous 2 := by simpa using hL.pow 2
  have hK := level_eliminant_nonzero G (L^2) hGval (hLval^2) (pow_ne_zero _ hhL) hn
  apply homogeneous_primitive_zeros (MvPolynomial.C (hLval^2)*G-MvPolynomial.C hGval*L^2) 2
    hK ((hG.C_mul (hLval^2)).sub (hL2.C_mul hGval)) S
  intro z hz
  obtain ⟨hp,hLz,hGz⟩ := hS z hz
  refine ⟨hp,?_⟩
  simp only [map_sub,map_mul,map_pow,MvPolynomial.eval_C,hLz,hGz]
  ring

/-- A nonzero degree-two homogeneous eliminant gives at most two directions,
with at most two signed primitive points on each. -/
theorem two_quadratic_levels : CF15TwoQuadraticLevels := by
  intro G₁ G₂ hG₁ hG₂ hn h₁ h₂ hh₁ hh₂ S hS
  apply homogeneous_primitive_zeros (MvPolynomial.C h₂*G₁-MvPolynomial.C h₁*G₂) 2
    (level_eliminant_nonzero G₁ G₂ h₁ h₂ hh₂ hn) ((hG₁.C_mul h₂).sub (hG₂.C_mul h₁)) S
  intro z hz
  obtain ⟨hp,h₁z,h₂z⟩ := hS z hz
  refine ⟨hp,?_⟩
  simp only [map_sub,map_mul,MvPolynomial.eval_C,h₁z,h₂z]
  ring

private def signedLevelDivisors (h : ℤ) : Finset ℤ :=
  (h.natAbs.divisors.image (fun n : ℕ => (n:ℤ))) ∪
    (h.natAbs.divisors.image (fun n : ℕ => -(n:ℤ)))

private theorem signed_divisor_mem (h a : ℤ) (hh : h ≠ 0) (ha : a ∣ h) :
    a ∈ signedLevelDivisors h := by
  classical
  have hn : a.natAbs ∈ h.natAbs.divisors := Nat.mem_divisors.mpr
    ⟨Int.natAbs_dvd_natAbs.mpr ha,by simpa using hh⟩
  apply Finset.mem_union.mpr
  by_cases hp : 0 ≤ a
  · left
    refine Finset.mem_image.mpr ⟨a.natAbs,hn,?_⟩
    rw [Int.natCast_natAbs,abs_of_nonneg hp]
  · right
    refine Finset.mem_image.mpr ⟨a.natAbs,hn,?_⟩
    rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge hp),neg_neg]

private theorem signed_divisor_nonzero (h a : ℤ) (ha : a ∈ signedLevelDivisors h) : a ≠ 0 := by
  classical
  have hn (n : ℕ) (hm : n ∈ h.natAbs.divisors) : n ≠ 0 := by
    intro hz
    have hd := (Nat.mem_divisors.mp hm).1
    have hh := (Nat.mem_divisors.mp hm).2
    exact hh (zero_dvd_iff.mp (by simpa [hz] using hd))
  rcases Finset.mem_union.mp ha with hp | hm
  · obtain ⟨n,hnd,he⟩ := Finset.mem_image.mp hp
    intro hz
    have hc : (n:ℤ)=0 := he.trans hz
    exact hn n hnd (by exact_mod_cast hc)
  · obtain ⟨n,hnd,he⟩ := Finset.mem_image.mp hm
    intro hz
    have hc : (n:ℤ)=0 := neg_eq_zero.mp (he.trans hz)
    exact hn n hnd (by exact_mod_cast hc)

private theorem signed_divisors_card (h : ℤ) : (signedLevelDivisors h).card ≤ 2*h.natAbs.divisors.card := by
  classical
  exact (Finset.card_union_le _ _).trans
    ((add_le_add Finset.card_image_le Finset.card_image_le).trans (by omega))

private theorem low_factor_level_fiber (G H : SourcePolynomial) (hpair : lowBinaryFactorPair G H)
    (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z G=a ∧ MvPolynomial.eval z H=b) :
    S.card ≤ 4 := by
  rcases hpair.2.2 with h | h | h | h
  · exact (two_linear_levels G H h.1 h.2.1 h.2.2 a b ha hb S hS).trans (by decide)
  · exact linear_quadratic_levels G H h.1 h.2.1 h.2.2 a b ha hb S hS
  · apply linear_quadratic_levels H G h.2.1 h.1 h.2.2 b a hb ha S
    intro z hz
    obtain ⟨hp,hG,hH⟩ := hS z hz
    exact ⟨hp,hH,hG⟩
  · exact two_quadratic_levels G H h.1 h.2.1 h.2.2 a b ha hb S hS

/-- Two fixed factor values give signed divisor labels, each pair with at most
four primitive parameters. The fixed factors themselves are never enumerated. -/
theorem low_factor_divisor_budget : CF15LowFactorDivisorBudget := by
  classical
  intro Q G H hpair hG hH h hh S hS
  let D := signedLevelDivisors h
  let f : (Fin 2 → ℤ) → ℤ × ℤ := fun z => (MvPolynomial.eval z G,MvPolynomial.eval z H)
  have hmap (z : Fin 2 → ℤ) (hz : z ∈ S) : f z ∈ D.product D := by
    apply Finset.mem_product.mpr
    have hval := (hS z hz).2
    have hGv : MvPolynomial.eval z G ∣ h := by
      rw [← hval]
      exact map_dvd (MvPolynomial.eval z) hG
    have hHv : MvPolynomial.eval z H ∣ h := by
      rw [← hval]
      exact map_dvd (MvPolynomial.eval z) hH
    exact ⟨signed_divisor_mem h _ hh hGv,signed_divisor_mem h _ hh hHv⟩
  have hfib (r : ℤ × ℤ) (hr : r ∈ D.product D) : (S.filter (fun z => f z=r)).card ≤ 4 := by
    obtain ⟨hr₁,hr₂⟩ := Finset.mem_product.mp hr
    apply low_factor_level_fiber G H hpair r.1 r.2 (signed_divisor_nonzero h _ hr₁) (signed_divisor_nonzero h _ hr₂)
    intro z hz
    obtain ⟨hzS,he⟩ := Finset.mem_filter.mp hz
    exact ⟨(hS z hzS).1,congrArg Prod.fst he,congrArg Prod.snd he⟩
  have hcount := finite_fiber_bound S (D.product D) f 4 hmap hfib
  have hD : D.card ≤ 2*h.natAbs.divisors.card := signed_divisors_card h
  have hsq := Nat.mul_le_mul hD hD
  have hcprod : (D.product D).card=D.card*D.card := Finset.card_product D D
  rw [hcprod] at hcount
  nlinarith

end
end P0365Subquarter
