import PaperProofs.FactorInventory

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF05PrimitiveFactorInventory
#print CF05UniformPrimitiveFactorCover
#check (primitive_factor_inventory : CF05PrimitiveFactorInventory)
#check (uniform_primitive_factor_cover : CF05UniformPrimitiveFactorCover)
#print axioms primitive_factor_inventory
#print axioms uniform_primitive_factor_cover
set_option pp.all false

example : CF05PrimitiveFactorInventory := by
  intro D F hF hD
  exact primitive_factor_inventory D F hF hD
example : CF05UniformPrimitiveFactorCover := by
  intro D H C hH hC
  exact uniform_primitive_factor_cover D H C hH hC

-- Nonunit integer content alone supplies no rational curve.
example : ∃ s : Finset SourcePolynomial, s=∅ ∧
    (∀ z : Fin 2 → ℚ, polynomialValue (MvPolynomial.C (6:ℤ)) z=0 →
      ∃ A ∈ s, polynomialValue A z=0) := by
  obtain ⟨s,hcard,_,hcover⟩ := primitive_factor_inventory 0 (MvPolynomial.C 6)
    (by simp) (by simp only [MvPolynomial.totalDegree_C,le_refl])
  exact ⟨s,Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard),hcover⟩

-- Three integer prime factors of the content still cost at most one curve.
example : ∃ s : Finset SourcePolynomial, s.card≤1 ∧
    (∀ z : Fin 2 → ℚ, z 0=0 → ∃ A ∈ s, polynomialValue A z=0) := by
  let F : SourcePolynomial := MvPolynomial.C 30*MvPolynomial.X 0
  have hnz : F≠0 := by simp [F]
  have hd : F.totalDegree≤1 := by
    calc
      _ ≤ (MvPolynomial.C (30:ℤ) : SourcePolynomial).totalDegree+
          (MvPolynomial.X (0:Fin 2) : SourcePolynomial).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = 1 := by simp only [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X,zero_add]
  obtain ⟨s,hcard,_,hcover⟩ := primitive_factor_inventory 1 F hnz hd
  refine ⟨s,hcard,?_⟩
  intro z hz
  apply hcover z
  simp [F,polynomialValue,hz]

-- Repeated curve factors are charged through degree, with no content inflation.
example : ∃ s : Finset SourcePolynomial, s.card≤2 ∧
    (∀ z : Fin 2 → ℚ, z 0=0 → ∃ A ∈ s, polynomialValue A z=0) := by
  let F : SourcePolynomial := MvPolynomial.C 30*MvPolynomial.X 0^2
  have hnz : F≠0 := by simp [F]
  have hd : F.totalDegree≤2 := by
    calc
      _ ≤ (MvPolynomial.C (30:ℤ) : SourcePolynomial).totalDegree+
          (MvPolynomial.X (0:Fin 2)^2 : SourcePolynomial).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = 2 := by simp only [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X_pow,zero_add]
  obtain ⟨s,hcard,_,hcover⟩ := primitive_factor_inventory 2 F hnz hd
  refine ⟨s,hcard,?_⟩
  intro z hz
  apply hcover z
  simp [F,polynomialValue,hz]

-- An integer constant can fail primitivity and become a unit over Q.
example : ¬coarseIntegralPrimitive (MvPolynomial.C (2:ℤ)) := by
  intro h
  have hd : ∀ e, (2:ℤ)∣(MvPolynomial.C (2:ℤ) : SourcePolynomial).coeff e :=
    (MvPolynomial.C_dvd_iff_dvd_coeff 2 _).1 (dvd_refl _)
  have hu := h 2 hd
  norm_num [Int.isUnit_iff] at hu
example : IsUnit (coarseRationalPolynomial (MvPolynomial.C (2:ℤ))) := by
  have hu : IsUnit (MvPolynomial.C (2:ℚ) : MvPolynomial (Fin 2) ℚ) :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr
      ⟨2,isUnit_iff_ne_zero.mpr (by norm_num),rfl⟩
  unfold coarseRationalPolynomial
  rw [MvPolynomial.map_C]
  rw [show (Int.castRingHom ℚ) (2:ℤ)=(2:ℚ) by norm_num]
  exact hu

end
end P0365Subquarter
