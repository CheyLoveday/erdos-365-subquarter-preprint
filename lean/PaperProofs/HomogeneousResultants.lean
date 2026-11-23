import PaperTargets.HomogeneousResultants
import PaperProofs.GraphRulings
import Mathlib.RingTheory.Coprime.Lemmas

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Genuine homogenization, with the degree-r coefficient giving its value
at infinity. No division is used in the infinity branch. -/
theorem homogeneous_form : CF13HomogeneousForm := by
  classical
  intro P r hd
  refine ⟨Polynomial.isHomogeneous_homogenize P,?_,?_⟩
  · intro x y hy
    have hmap : (rationalPolynomial P).natDegree ≤ r := by
      simpa only [rationalPolynomial,Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective] using hd
    have h := Polynomial.eval_homogenize hmap (![x,y] : Fin 2 → ℚ) hy
    simpa only [rationalPolynomial,Polynomial.homogenize_map,MvPolynomial.eval_map,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      polynomialValue,integerPolynomialValue] using h
  · intro x
    unfold polynomialValue Polynomial.homogenize
    rw [MvPolynomial.eval₂_sum]
    rw [Finset.sum_eq_single (r,0)]
    · simp [MvPolynomial.eval₂_monomial,Finsupp.prod_fintype,Fin.prod_univ_two]
    · intro kl hkl hne
      have hsum := Finset.mem_antidiagonal.mp hkl
      have hl : kl.2 ≠ 0 := by intro h; apply hne; ext <;> simp_all
      simp [MvPolynomial.eval₂_monomial,Finsupp.prod_fintype,Fin.prod_univ_two,zero_pow hl]
    · simp

/-- Actual maximum degree prevents a simultaneous root at infinity. The
padding formulas reduce its full resultant to the coprime affine resultant. -/
theorem full_resultant_nonzero : CF13FullResultantNonzero := by
  classical
  intro A B hr hcop
  let f := rationalPolynomial A
  let g := rationalPolynomial B
  let r := graphDegree A B
  have hdf : f.natDegree = A.natDegree := Polynomial.natDegree_map_eq_of_injective Int.cast_injective A
  have hdg : g.natDegree = B.natDegree := Polynomial.natDegree_map_eq_of_injective Int.cast_injective B
  have hf : f.natDegree ≤ r := hdf.le.trans (le_max_left _ _)
  have hg : g.natDegree ≤ r := hdg.le.trans (le_max_right _ _)
  have hbase : Polynomial.resultant f g ≠ 0 := Polynomial.resultant_ne_zero f g hcop
  have hfull : Polynomial.resultant f g r r ≠ 0 := by
    by_cases hfr : f.natDegree = r
    · have hf0 : f ≠ 0 := by intro hz; simp only [hz,Polynomial.natDegree_zero] at hfr; omega
      have hpad := Polynomial.resultant_add_right_deg f g r g.natDegree (r-g.natDegree) le_rfl
      rw [Nat.add_sub_of_le hg] at hpad
      rw [hpad]
      apply mul_ne_zero _ (by simpa only [hfr] using hbase)
      apply pow_ne_zero
      simpa only [← hfr,Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hf0
    · have hgr : g.natDegree = r := by dsimp [r,graphDegree] at *; omega
      have hg0 : g ≠ 0 := by intro hz; simp only [hz,Polynomial.natDegree_zero] at hgr; omega
      have hpad := Polynomial.resultant_add_left_deg f g f.natDegree r (r-f.natDegree) le_rfl
      rw [Nat.add_sub_of_le hf] at hpad
      rw [hpad]
      apply mul_ne_zero
      · apply mul_ne_zero (pow_ne_zero _ (by norm_num))
        apply pow_ne_zero
        simpa only [← hgr,Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hg0
      · simpa only [hgr] using hbase
  intro hz
  apply hfull
  change Polynomial.resultant (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) r r = 0
  rw [Polynomial.resultant_map_map]
  change (fullGraphResultant A B : ℚ) = 0
  rw [hz,Int.cast_zero]

private theorem sylvester_monomial (A B : Polynomial ℤ) (r : ℕ) (hr : 1 ≤ r)
    (hA : A.natDegree ≤ r) (hB : B.natDegree ≤ r) (k : ℕ) (hk : k < r+r) :
    ∃ p q : Polynomial ℤ, p.natDegree ≤ r-1 ∧ q.natDegree ≤ r-1 ∧
      A*p+B*q = Polynomial.C (Polynomial.resultant A B r r)*Polynomial.X^k := by
  let z : Polynomial.degreeLT ℤ (r+r) := ⟨Polynomial.X^k,by
    rw [Polynomial.mem_degreeLT,Polynomial.degree_X_pow]
    exact_mod_cast hk⟩
  let W := Polynomial.adjSylvester A B z
  have hw := congrArg (fun t : Polynomial.degreeLT ℤ (r+r) => (t : Polynomial ℤ))
    (LinearMap.congr_fun (Polynomial.sylvesterMap_comp_adjSylvester A B hA hB) z)
  have hd (p : Polynomial.degreeLT ℤ r) : (p : Polynomial ℤ).natDegree ≤ r-1 := by
    by_cases hp : (p : Polynomial ℤ) = 0
    · simp [hp]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr (Polynomial.mem_degreeLT.mp p.property)
      omega
  refine ⟨W.2,W.1,hd _,hd _,?_⟩
  change A*(W.2 : Polynomial ℤ)+B*(W.1 : Polynomial ℤ) =
    Polynomial.resultant A B r r • (Polynomial.X^k) at hw
  simpa only [Polynomial.smul_eq_C_mul] using hw

/-- The same integral adjugate lifts both extreme monomials. Homogenizing
those two identities keeps every projective parameter, including both axes. -/
theorem homogeneous_bezout : CF13HomogeneousBezout := by
  intro A B r hr hA hB
  let N := 2*r-1
  have hN : r+(r-1)=N := by dsimp [N]; omega
  have lift (p q : Polynomial ℤ) (hp : p.natDegree ≤ r-1) (hq : q.natDegree ≤ r-1)
      (k : ℕ) (hk : k ≤ N)
      (he : A*p+B*q=Polynomial.C (Polynomial.resultant A B r r)*Polynomial.X^k) :
      MvPolynomial.C (Polynomial.resultant A B r r)*MvPolynomial.X 0^k*MvPolynomial.X 1^(N-k) =
        p.homogenize (r-1)*A.homogenize r+q.homogenize (r-1)*B.homogenize r := by
    have h := congrArg (fun P : Polynomial ℤ => P.homogenize (r+(r-1))) he
    rw [Polynomial.homogenize_add,Polynomial.homogenize_mul _ _ hA hp,
      Polynomial.homogenize_mul _ _ hB hq,Polynomial.homogenize_C_mul,
      Polynomial.homogenize_X_pow (by omega)] at h
    simpa only [hN,mul_assoc,mul_comm,mul_left_comm] using h.symm
  obtain ⟨p₀,q₀,hp₀,hq₀,he₀⟩ := sylvester_monomial A B r hr hA hB 0 (by omega)
  obtain ⟨p₁,q₁,hp₁,hq₁,he₁⟩ := sylvester_monomial A B r hr hA hB N (by dsimp [N]; omega)
  refine ⟨p₁.homogenize (r-1),q₁.homogenize (r-1),p₀.homogenize (r-1),q₀.homogenize (r-1),
    Polynomial.isHomogeneous_homogenize _,Polynomial.isHomogeneous_homogenize _,
    Polynomial.isHomogeneous_homogenize _,Polynomial.isHomogeneous_homogenize _,?_,?_⟩
  · simpa only [Nat.sub_self,pow_zero,mul_one,N] using lift p₁ q₁ hp₁ hq₁ N le_rfl he₁
  · simpa only [Nat.sub_zero,pow_zero,mul_one,N] using lift p₀ q₀ hp₀ hq₀ 0 (Nat.zero_le _) he₀

/-- Two homogeneous identities and primitive powers imply gcd divisibility
without dividing by either parameter. Signed axes are included. -/
theorem evaluated_gcd : CF13EvaluatedGCD := by
  intro A B r hr hA hB x y hxy
  obtain ⟨L₁,L₂,L₃,L₄,_,_,_,_,hx,hy⟩ := homogeneous_bezout A B r hr hA hB
  let a := homogeneousGraphValue A r x y
  let b := homogeneousGraphValue B r x y
  let g : ℤ := Int.gcd a b
  let R := Polynomial.resultant A B r r
  have hgA : g ∣ a := Int.gcd_dvd_left a b
  have hgB : g ∣ b := Int.gcd_dvd_right a b
  have hex := congrArg (MvPolynomial.eval (![x,y] : Fin 2 → ℤ)) hx
  have hey := congrArg (MvPolynomial.eval (![x,y] : Fin 2 → ℤ)) hy
  simp only [map_mul,map_pow,map_add,MvPolynomial.eval_C,MvPolynomial.eval_X,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at hex hey
  have hgx : g ∣ R*x^(2*r-1) := by
    rw [hex]
    exact dvd_add (dvd_mul_of_dvd_right hgA _) (dvd_mul_of_dvd_right hgB _)
  have hgy : g ∣ R*y^(2*r-1) := by
    rw [hey]
    exact dvd_add (dvd_mul_of_dvd_right hgA _) (dvd_mul_of_dvd_right hgB _)
  obtain ⟨u,v,huv⟩ := hxy.pow (m := 2*r-1) (n := 2*r-1)
  have he : R = u*(R*x^(2*r-1))+v*(R*y^(2*r-1)) := by
    calc
      R = R*(u*x^(2*r-1)+v*y^(2*r-1)) := by rw [huv,mul_one]
      _ = _ := by ring
  change g ∣ R
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right hgx _) (dvd_mul_of_dvd_right hgy _)

private theorem integer_det_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (H : ℝ) (_hH : 0 ≤ H) (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    |((A.det : ℤ) : ℝ)| ≤ (n.factorial : ℝ)*H^n := by
  rw [Int.cast_det,Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
        |((Equiv.Perm.sign σ : ℤ) : ℝ)*∏ i, (A (σ i) i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, |(A (σ i) i : ℝ)| := by
      simp only [abs_mul,abs_unit_intCast,one_mul,Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), H^n := by
      apply Finset.sum_le_sum
      intro σ hσ
      calc
        _ ≤ ∏ _i : Fin n, H := Finset.prod_le_prod₀
          (fun _ _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = H^n := by simp
    _ = _ := by simp [Fintype.card_perm]

/-- Every full Sylvester entry is an actual coefficient or zero; the
Leibniz bound is uniform and does not enumerate graph coefficient labels. -/
theorem resultant_height : CF13ResultantHeight := by
  intro A B r H hH hA hB
  have hb (i j : Fin (r+r)) : |((Polynomial.sylvester A B r r i j : ℤ) : ℝ)| ≤ H := by
    induction j using Fin.addCases with
    | left j =>
      simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_left]
      split_ifs
      · exact hB _
      · simpa using hH
    | right j =>
      simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_right]
      split_ifs
      · exact hA _
      · simpa using hH
  simpa only [two_mul,Polynomial.resultant] using
    integer_det_bound (Polynomial.sylvester A B r r) H hH hb

/-- One nonzero polynomial-height full resultant controls the evaluated gcd
at every primitive parameter of the actual mixed graph. -/
theorem actual_mixed_resultant : CF13ActualMixedResultant := by
  classical
  intro X D A B hX hdata hr
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hA : A.natDegree ≤ graphDegree A B := le_max_left _ _
  have hB : B.natDegree ≤ graphDegree A B := le_max_right _ _
  have hr3 : graphDegree A B ≤ 3 := max_le hdata.2.2.2.2.1 hdata.2.2.2.2.2.1
  have hcoefA := hdata.2.2.2.2.2.2 A (by simp)
  have hcoefB := hdata.2.2.2.2.2.2 B (by simp)
  refine ⟨full_resultant_nonzero A B hr hdata.2.2.1,?_,?_⟩
  · calc
      _ ≤ ((2*graphDegree A B).factorial : ℝ)*(X^(15:ℕ))^(2*graphDegree A B) :=
        resultant_height A B _ _ (pow_nonneg hX0 _) hcoefA hcoefB
      _ ≤ 720*X^(90:ℕ) := by
        apply mul_le_mul
        · have hh := Nat.factorial_le (show 2*graphDegree A B ≤ 6 by omega)
          norm_num [Nat.factorial] at hh ⊢
          exact_mod_cast hh
        · rw [← pow_mul]
          exact pow_le_pow_right₀ hX1 (by omega)
        · positivity
        · norm_num
  · intro x y hxy
    exact evaluated_gcd A B _ hr hA hB x y hxy

end
end P0365Subquarter
