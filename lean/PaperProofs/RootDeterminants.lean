import PaperTargets.RootDeterminants
import PaperProofs.RootColumns
import PaperProofs.MonomialDeterminants
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- The finite sum of coefficient products factors into the column norms. -/
theorem rectangular_root_determinant : CF04RectangularRootDeterminant := by
  classical
  intro A C
  obtain ⟨L,hL,hcols⟩ := root_column_coefficient_bound A C
  have hL₀ : 0≤L := by linarith
  let H : ℕ := Fintype.card (RectangularIndex A C)
  let P (j : RectangularIndex A C) : SourcePolynomial :=
    rootColumnPolynomial j.1.val j.2.val
  let T := Fintype.piFinset (fun j => (P j).support)
  let N : ℝ := (H.factorial:ℝ)*3^(H*(2*A+3*C))*8^(H*C)
  let K : ℝ := 1+N*L^H
  have hN : 0≤N := by dsimp [N]; positivity
  refine ⟨K,?_,?_⟩
  · dsimp [K]
    linarith [mul_nonneg hN (pow_nonneg hL₀ H)]
  · intro a b ha hab α β hα hβ
    let E : ℝ := Real.exp (-latticeDeterminantLower H a b)
    let Q (r : RectangularIndex A C → Fin 2 →₀ ℕ) :
        Matrix (RectangularIndex A C) (RectangularIndex A C) ℝ :=
      Matrix.of (fun i j => bivariateMonomialValue (α i) (β i) (r j))
    have hE : 0≤E := (Real.exp_pos _).le
    have hmon (r : RectangularIndex A C → Fin 2 →₀ ℕ) (hr : r∈T) :
        |(Q r).det|≤N*E := by
      have hr' := Fintype.mem_piFinset.mp hr
      have hdeg (j : RectangularIndex A C) : r j 0≤2*A+3*C ∧ r j 1≤C := by
        have hh := root_column_support j.1.val j.2.val (r j) (hr' j)
        have hi := Nat.le_of_lt_succ j.1.is_lt
        have hj := Nat.le_of_lt_succ j.2.is_lt
        constructor <;> omega
      have hb := monomial_weight_determinant (RectangularIndex A C)
        (2*A+3*C) C r α β a b ha hab hdeg hα hβ
      change |(Q r).det|≤N*E at hb
      exact hb
    have hcoefs : (∑ r∈T, ∏ j : RectangularIndex A C,
        |((P j).coeff (r j):ℝ)|)≤L^H := by
      have hprod : (∏ j : RectangularIndex A C, ∑ e∈(P j).support,
          |((P j).coeff e:ℝ)|) =
          (∑ r∈T, ∏ j : RectangularIndex A C, |((P j).coeff (r j):ℝ)|) :=
        Finset.prod_univ_sum (fun j => (P j).support)
          (fun j e => |((P j).coeff e:ℝ)|)
      rw [←hprod]
      calc
        _ ≤ ∏ _j : RectangularIndex A C, L := by
          apply Finset.prod_le_prod₀
          · intro j hj
            exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
          · intro j hj
            exact hcols j.1.val j.2.val (Nat.le_of_lt_succ j.1.is_lt)
              (Nat.le_of_lt_succ j.2.is_lt)
        _ = L^H := by simp [H]
    have heq : (rectangularRootMatrix A C α β).det =
        ∑ r∈T, (∏ j : RectangularIndex A C, ((P j).coeff (r j):ℝ))*(Q r).det :=
      polynomial_column_expansion (RectangularIndex A C) P α β
    change |(rectangularRootMatrix A C α β).det|≤K*E
    rw [heq]
    calc
      _ ≤ ∑ r∈T, |(∏ j : RectangularIndex A C, ((P j).coeff (r j):ℝ))*(Q r).det| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r∈T, (∏ j : RectangularIndex A C, |((P j).coeff (r j):ℝ)|)*|(Q r).det| := by
        simp only [abs_mul,Finset.abs_prod]
      _ ≤ ∑ r∈T, (∏ j : RectangularIndex A C, |((P j).coeff (r j):ℝ)|)*(N*E) :=
        Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hmon r hr)
          (Finset.prod_nonneg (fun _ _ => abs_nonneg _)))
      _ = (∑ r∈T, ∏ j : RectangularIndex A C, |((P j).coeff (r j):ℝ)|)*(N*E) := by
        rw [Finset.sum_mul]
      _ ≤ L^H*(N*E) := mul_le_mul_of_nonneg_right hcoefs (mul_nonneg hN hE)
      _ = (N*L^H)*E := by ring
      _ ≤ K*E := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hE

/-- Every original source supplies the common row nodes; both scale products
are extracted from the exact integer matrix, before applying the real estimate. -/
theorem actual_rectangular_determinant : CF04ActualRectangularDeterminant := by
  classical
  intro A C
  obtain ⟨K,hK,hbound⟩ := rectangular_root_determinant A C
  refine ⟨K,hK,?_⟩
  intro X M t hX hM hMX ht n b d u v hs hn hint
  have hMp : 0<M := by linarith
  have hXp : 0<X := hMp.trans_le hMX
  have hlogM : 0<Real.log M := Real.log_pos hM
  have hlogMX : Real.log M≤Real.log X := Real.log_le_log hMp hMX
  have hnodes (i : RectangularIndex A C) := actual_rectangular_root_columns
    (n i) (b i) (d i) (u i) (v i) (hs i) X M t hX (hn i) hM.le hMX ht (hint i)
  choose α β hα hαM hβ he using hnodes
  have hαe (i : RectangularIndex A C) : |α i|≤3*Real.exp (-Real.log M) := by
    rw [abs_of_nonneg (hα i),Real.exp_neg,Real.exp_log hMp]
    simpa only [div_eq_mul_inv] using hαM i
  have hβe (i : RectangularIndex A C) : |β i|≤8*Real.exp (-Real.log X) := by
    rw [Real.exp_neg,Real.exp_log hXp]
    simpa only [div_eq_mul_inv] using hβ i
  have hsize := hbound (Real.log M) (Real.log X) hlogM hlogMX α β hαe hβe
  let R (i : RectangularIndex A C) : ℝ := rectangularRowScale A C (d i) (u i)
  let S (j : RectangularIndex A C) : ℝ := rectangularColumnScale t j
  have hcast : ((rectangularSourceMatrix A C b d u v).det:ℝ) =
      Matrix.det (Matrix.of (fun i j => R i*S j*(rectangularRootMatrix A C α β) i j)) := by
    rw [Int.cast_det]
    congr 1
    ext i j
    simpa only [rectangularSourceMatrix,Matrix.map_apply,Matrix.of_apply,R,S,
      rectangularRowScale,rectangularColumnScale,rectangularRootMatrix,mul_assoc] using
      he i A C j.1.val j.2.val (Nat.le_of_lt_succ j.1.is_lt) (Nat.le_of_lt_succ j.2.is_lt)
  have hscale : Matrix.det (Matrix.of (fun i j => R i*S j*(rectangularRootMatrix A C α β) i j)) =
      (∏ i, R i)*(∏ j, S j)*(rectangularRootMatrix A C α β).det := by
    calc
      _ = (∏ i, R i)*Matrix.det (Matrix.of (fun i j => S j*(rectangularRootMatrix A C α β) i j)) := by
        simpa only [Matrix.of_apply,mul_assoc] using
          (Matrix.det_mul_column R (Matrix.of (fun i j => S j*(rectangularRootMatrix A C α β) i j)))
      _ = _ := by
        rw [Matrix.det_mul_row S (rectangularRootMatrix A C α β)]
        ring
  have hnorm := hcast.trans hscale
  have hR : 0≤∏ i, R i := Finset.prod_nonneg (fun i _ => by
    dsimp [R,rectangularRowScale]; positivity)
  have hS : 0≤∏ j, S j := Finset.prod_nonneg (fun j _ => by
    dsimp [S,rectangularColumnScale]; positivity)
  rw [hnorm,abs_mul,abs_mul,abs_of_nonneg hR,abs_of_nonneg hS]
  calc
    _ ≤ (∏ i, R i)*(∏ j, S j)*(K*Real.exp
        (-latticeDeterminantLower (Fintype.card (RectangularIndex A C)) (Real.log M) (Real.log X))) :=
      mul_le_mul_of_nonneg_left hsize (mul_nonneg hR hS)
    _ = _ := by dsimp [R,S]; ring

end
end P0365Subquarter
