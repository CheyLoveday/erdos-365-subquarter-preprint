import PaperTargets.PullbackGeometry
import PaperProofs.SourceRecovery

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- A zero section would make the other rational polynomial a unit and force
actual maximum degree zero. Integer scalar contents are retained. -/
theorem mixed_sections_nonzero : CF14MixedSectionsNonzero := by
  intro A B hr hc
  have unit_degree (P : Polynomial ℤ) (h : IsUnit (rationalPolynomial P)) : P.natDegree=0 := by
    have hd := Polynomial.natDegree_eq_zero_of_isUnit h
    simpa only [rationalPolynomial,Polynomial.natDegree_map_eq_of_injective
      (f := Int.castRingHom ℚ) Int.cast_injective] using hd
  constructor
  · intro hA
    have hu : IsUnit (rationalPolynomial B) := isCoprime_zero_left.mp (by simpa [hA] using hc)
    have hB := unit_degree B hu
    simp only [graphDegree,hA,Polynomial.natDegree_zero,hB,max_self] at hr
    omega
  · intro hB
    have hu : IsUnit (rationalPolynomial A) := isCoprime_zero_right.mp (by simpa [hB] using hc)
    have hA := unit_degree A hu
    simp only [graphDegree,hB,Polynomial.natDegree_zero,hA,max_self] at hr
    omega

private theorem degree_sub_of_ne (p q : Polynomial ℤ) (h : p.natDegree ≠ q.natDegree) :
    p-q ≠ 0 ∧ (p-q).natDegree=max p.natDegree q.natDegree := by
  refine ⟨fun he => h (congrArg Polynomial.natDegree (sub_eq_zero.mp he)),?_⟩
  rcases lt_or_gt_of_ne h with hl | hr
  · rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt hl,max_eq_right hl.le]
  · rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hr,max_eq_left hr.le]

/-- The leading degrees cannot cancel: parity for squares and residues modulo
three for cubes. This does not require coprimality. -/
theorem affine_pullback_degrees : CF14AffinePullbackDegrees := by
  intro A B hA hB inverse
  cases inverse
  · have hd : ((Polynomial.X:Polynomial ℤ)^3*B^2).natDegree=3+2*B.natDegree := by
      rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hB)]
      simp
    have hne : (A^2).natDegree ≠ ((Polynomial.X:Polynomial ℤ)^3*B^2).natDegree := by
      rw [Polynomial.natDegree_pow,hd]; omega
    simpa only [affineGraphPullback,Bool.false_eq_true,ite_false,hd,Polynomial.natDegree_pow]
      using degree_sub_of_ne (A^2) (Polynomial.X^3*B^2) hne
  · have hd : ((Polynomial.X:Polynomial ℤ)^2*B^3).natDegree=2+3*B.natDegree := by
      rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hB)]
      simp
    have hne : ((Polynomial.X:Polynomial ℤ)^2*B^3).natDegree ≠ (A^3).natDegree := by
      rw [hd,Polynomial.natDegree_pow]; omega
    simpa only [affineGraphPullback,ite_true,hd,Polynomial.natDegree_pow]
      using degree_sub_of_ne (Polynomial.X^2*B^3) (A^3) hne

private theorem pullback_homogeneous (inverse : Bool) (A B : Polynomial ℤ) :
    (graphPullback inverse A B).IsHomogeneous (graphPullbackDegree inverse (graphDegree A B)) := by
  cases inverse
  · simpa only [graphPullback,graphPullbackDegree,Bool.false_eq_true,ite_false,
      Nat.mul_comm,Nat.add_comm] using
      ((MvPolynomial.isHomogeneous_X_pow 1 3).mul ((Polynomial.isHomogeneous_homogenize (n := graphDegree A B) A).pow 2)).sub
      ((MvPolynomial.isHomogeneous_X_pow 0 3).mul ((Polynomial.isHomogeneous_homogenize (n := graphDegree A B) B).pow 2))
  · simpa only [graphPullback,graphPullbackDegree,ite_true,Nat.mul_comm,Nat.add_comm] using
      ((MvPolynomial.isHomogeneous_X_pow 0 2).mul ((Polynomial.isHomogeneous_homogenize (n := graphDegree A B) B).pow 3)).sub
      ((MvPolynomial.isHomogeneous_X_pow 1 2).mul ((Polynomial.isHomogeneous_homogenize (n := graphDegree A B) A).pow 3))

private theorem dehomogenize_pullback (inverse : Bool) (A B : Polynomial ℤ) :
    MvPolynomial.aeval ![(Polynomial.X:Polynomial ℤ),1] (graphPullback inverse A B) =
      affineGraphPullback inverse A B := by
  have hA : A.natDegree ≤ graphDegree A B := le_max_left _ _
  have hB : B.natDegree ≤ graphDegree A B := le_max_right _ _
  cases inverse <;> simp [graphPullback,affineGraphPullback,hA,hB]

/-- The actual source pullback is homogenized at the full degree N, with its
possible y-axis factor retained. -/
theorem homogeneous_pullback : CF14HomogeneousPullback := by
  intro inverse A B
  have hA : A.natDegree ≤ graphDegree A B := le_max_left _ _
  have hB : B.natDegree ≤ graphDegree A B := le_max_right _ _
  have hd : (affineGraphPullback inverse A B).natDegree ≤ graphPullbackDegree inverse (graphDegree A B) := by
    cases inverse
    · apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp only [Polynomial.natDegree_pow,graphPullbackDegree,Bool.false_eq_true,ite_false]
        omega
      · have h := Polynomial.natDegree_mul_le (p := (Polynomial.X:Polynomial ℤ)^3) (q := B^2)
        simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X,mul_one] at h
        exact h.trans (by dsimp [graphPullbackDegree]; omega)
    · apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · have h := Polynomial.natDegree_mul_le (p := (Polynomial.X:Polynomial ℤ)^2) (q := B^3)
        simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X,mul_one] at h
        exact h.trans (by dsimp [graphPullbackDegree]; omega)
      · simp only [Polynomial.natDegree_pow,graphPullbackDegree,ite_true]; omega
  have hh := pullback_homogeneous inverse A B
  have he := Polynomial.homogenize_eq_of_isHomogeneous hh (dehomogenize_pullback inverse A B)
  refine ⟨hd,he,hh,?_⟩
  intro hAn hBn
  have hF := (affine_pullback_degrees A B hAn hBn inverse).1
  have hH : graphPullback inverse A B ≠ 0 := by
    intro hz
    exact hF (Polynomial.eq_zero_of_homogenize_eq_zero hd (he.trans hz))
  exact ⟨hH,hh.totalDegree hH⟩

private theorem trail_pow (P : Polynomial ℤ) (hP : P ≠ 0) (n : ℕ) :
    (P^n).natTrailingDegree=n*P.natTrailingDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Polynomial.natTrailingDegree_mul (pow_ne_zero _ hP) hP,ih]
    ring

private theorem trail_sub_of_ne (p q : Polynomial ℤ) (hp : p ≠ 0) (hq : q ≠ 0) (h : p.natTrailingDegree ≠ q.natTrailingDegree) :
    (p-q).natTrailingDegree=min p.natTrailingDegree q.natTrailingDegree := by
  have hn : p-q ≠ 0 := fun he => h (congrArg Polynomial.natTrailingDegree (sub_eq_zero.mp he))
  apply le_antisymm
  · rcases lt_or_gt_of_ne h with hl | hr
    · rw [min_eq_left hl.le]
      apply Polynomial.natTrailingDegree_le_of_ne_zero
      rw [Polynomial.coeff_sub,Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hl,sub_zero]
      exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp
    · rw [min_eq_right hr.le]
      apply Polynomial.natTrailingDegree_le_of_ne_zero
      rw [Polynomial.coeff_sub,Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hr,zero_sub,neg_ne_zero]
      exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq
  · apply Polynomial.le_natTrailingDegree hn
    intro m hm
    rw [Polynomial.coeff_sub,Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_le hm (min_le_left _ _)),
      Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_le hm (min_le_right _ _)),sub_self]

private theorem coprime_axis_orders (A B : Polynomial ℤ)
    (hc : IsCoprime (rationalPolynomial A) (rationalPolynomial B)) :
    A.natTrailingDegree=0 ∨ B.natTrailingDegree=0 := by
  by_contra hn
  have hA : A.coeff 0=0 := (Polynomial.natTrailingDegree_ne_zero.mp (not_or.mp hn).1).2
  have hB : B.coeff 0=0 := (Polynomial.natTrailingDegree_ne_zero.mp (not_or.mp hn).2).2
  obtain ⟨a,b,he⟩ := hc
  have h := congrArg (fun P : Polynomial ℚ => P.coeff 0) he
  simp [rationalPolynomial,hA,hB] at h

/-- Exact axis multiplicities are computed before any abc application. -/
theorem axis_orders : CF14AxisOrders := by
  intro A B hr hc inverse
  obtain ⟨hA,hB⟩ := mixed_sections_nonzero A B hr hc
  have hz := coprime_axis_orders A B hc
  have hd := (affine_pullback_degrees A B hA hB inverse).2
  have he : (affineGraphPullback inverse A B).natTrailingDegree=
      (if inverse then min (2+3*B.natTrailingDegree) (3*A.natTrailingDegree)
       else min (2*A.natTrailingDegree) (3+2*B.natTrailingDegree)) := by
    cases inverse
    · have hprod : ((Polynomial.X:Polynomial ℤ)^3*B^2).natTrailingDegree=3+2*B.natTrailingDegree := by
        rw [Polynomial.natTrailingDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hB),
          Polynomial.natTrailingDegree_X_pow,trail_pow B hB]
      have hne : (A^2).natTrailingDegree ≠ ((Polynomial.X:Polynomial ℤ)^3*B^2).natTrailingDegree := by
        rw [trail_pow A hA,hprod]; omega
      simpa only [affineGraphPullback,Bool.false_eq_true,ite_false,trail_pow A hA,hprod] using
        trail_sub_of_ne (A^2) (Polynomial.X^3*B^2) (pow_ne_zero _ hA)
          (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hB)) hne
    · have hprod : ((Polynomial.X:Polynomial ℤ)^2*B^3).natTrailingDegree=2+3*B.natTrailingDegree := by
        rw [Polynomial.natTrailingDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hB),
          Polynomial.natTrailingDegree_X_pow,trail_pow B hB]
      have hne : ((Polynomial.X:Polynomial ℤ)^2*B^3).natTrailingDegree ≠ (A^3).natTrailingDegree := by
        rw [hprod,trail_pow A hA]; omega
      simpa only [affineGraphPullback,ite_true,trail_pow A hA,hprod] using
        trail_sub_of_ne (Polynomial.X^2*B^3) (A^3)
          (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hB)) (pow_ne_zero _ hA) hne
  refine ⟨he,?_,?_,?_⟩
  · cases inverse <;> simp only [Bool.false_eq_true,ite_false,ite_true] at he ⊢ <;> omega
  · cases inverse <;> simp only [Bool.false_eq_true,ite_false,ite_true,graphPullbackDegree,graphDegree] at hd ⊢ <;> omega
  · intro hi; subst inverse
    simp only [ite_true,graphPullbackDegree,graphDegree] at he hd ⊢
    constructor <;> omega

/-- A full pure axis power has multiplicity N≥5, contradicting the proved
axis orders. Zero scalar is included through pullback nonvanishing. -/
theorem axis_power_exclusion : CF14AxisPowerExclusion := by
  intro A B hr hc inverse c i he
  obtain ⟨hA,hB⟩ := mixed_sections_nonzero A B hr hc
  obtain ⟨_,_,_,hH⟩ := homogeneous_pullback inverse A B
  have hn := (hH hA hB).1
  have hc0 : c ≠ 0 := by
    intro h; apply hn; simpa [h] using he
  obtain ⟨_,hxo,hyo,_⟩ := axis_orders A B hr hc inverse
  have hN : 5 ≤ graphPullbackDegree inverse (graphDegree A B) := by
    cases inverse <;> dsimp [graphPullbackDegree] <;> omega
  have hev := congrArg (MvPolynomial.aeval ![(Polynomial.X:Polynomial ℤ),1]) he
  rw [dehomogenize_pullback] at hev
  fin_cases i
  · have hf : affineGraphPullback inverse A B=Polynomial.C c*Polynomial.X^(graphPullbackDegree inverse (graphDegree A B)) := by
      simpa using hev
    have ht := congrArg Polynomial.natTrailingDegree hf
    rw [Polynomial.natTrailingDegree_mul (Polynomial.C_ne_zero.mpr hc0) (pow_ne_zero _ Polynomial.X_ne_zero),
      Polynomial.natTrailingDegree_C,Polynomial.natTrailingDegree_X_pow,zero_add] at ht
    cases inverse <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hxo <;> omega
  · have hf : affineGraphPullback inverse A B=Polynomial.C c := by simpa using hev
    have ht := congrArg Polynomial.natDegree hf
    rw [Polynomial.natDegree_C] at ht
    cases inverse <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hyo <;> omega

/-- All actual mixed CF13 bounded graphs satisfy this geometry before the
source quantifiers. Constant graphs retain their earlier ruling branch. -/
theorem actual_mixed_pullback : CF14ActualMixedPullback := by
  intro X D A B hX hb hr inverse
  have hc := hb.2.2.1
  have hdeg : graphDegree A B ≤ 3 := max_le hb.2.2.2.2.1 hb.2.2.2.2.2.1
  obtain ⟨hA,hB⟩ := mixed_sections_nonzero A B hr hc
  obtain ⟨_,_,hh,h⟩ := homogeneous_pullback inverse A B
  obtain ⟨hn,ht⟩ := h hA hB
  obtain ⟨_,hx,hy,_⟩ := axis_orders A B hr hc inverse
  refine ⟨?_,?_,hn,hh,ht,hx,hy,axis_power_exclusion A B hr hc inverse⟩
  · cases inverse <;> dsimp [graphPullbackDegree] <;> omega
  · cases inverse <;> dsimp [graphPullbackDegree] <;> omega

end
end P0365Subquarter
