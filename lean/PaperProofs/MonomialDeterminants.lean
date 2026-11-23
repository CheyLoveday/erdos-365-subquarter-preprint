import PaperTargets.MonomialDeterminants
import PaperProofs.WeightedMonomials
import Mathlib.Analysis.Complex.Exponential

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem polynomial_column_sum (P : SourcePolynomial) (α β : ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) ![α,β] P =
      ∑ e ∈ P.support, (P.coeff e:ℝ)*bivariateMonomialValue α β e := by
  rw [MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro e he
  simp [bivariateMonomialValue,Fin.prod_univ_succ]

/-- Ordinary finite multilinearity expands columns over their actual supports. -/
theorem polynomial_column_expansion : CF04PolynomialColumnExpansion := by
  classical
  intro ι _ _ P α β
  let g (j : ι) (e : Fin 2 →₀ ℕ) : ι → ℝ :=
    fun i => (P j).coeff e*bivariateMonomialValue (α i) (β i) e
  have hm : (fun j i => MvPolynomial.eval₂ (Int.castRingHom ℝ) ![α i,β i] (P j)) =
      (fun j => ∑ e ∈ (P j).support, g j e) := by
    ext j i
    simpa only [Finset.sum_apply,g] using polynomial_column_sum (P j) (α i) (β i)
  have he := (Matrix.detRowAlternating (n:=ι) (R:=ℝ)).toMultilinearMap.map_sum_finset
    g (fun j => (P j).support)
  change Matrix.det (fun j => ∑ e ∈ (P j).support, g j e) =
    ∑ r ∈ Fintype.piFinset (fun j => (P j).support), Matrix.det (fun j => g j (r j)) at he
  calc
    _ = Matrix.det (fun j i => MvPolynomial.eval₂ (Int.castRingHom ℝ) ![α i,β i] (P j)) :=
      (Matrix.det_transpose _).symm
    _ = ∑ r ∈ Fintype.piFinset (fun j => (P j).support), Matrix.det (fun j => g j (r j)) := by
      rw [hm,he]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      change Matrix.det (Matrix.of (fun j i => ((P j).coeff (r j):ℝ)*
        bivariateMonomialValue (α i) (β i) (r j))) =
          (∏ j : ι, ((P j).coeff (r j):ℝ))*
            Matrix.det (Matrix.of (fun i j => bivariateMonomialValue (α i) (β i) (r j)))
      calc
        _ = (∏ j : ι, ((P j).coeff (r j):ℝ))*
            Matrix.det (Matrix.of (fun j i => bivariateMonomialValue (α i) (β i) (r j))) := by
          simpa only [Matrix.of_apply] using
            (Matrix.det_mul_column (fun j => ((P j).coeff (r j):ℝ))
              (Matrix.of (fun j i => bivariateMonomialValue (α i) (β i) (r j))))
        _ = _ := by
          congr 1
          exact Matrix.det_transpose _

/-- Repeated selected exponent pairs give literally identical columns. -/
theorem repeated_exponent_determinant : CF04RepeatedExponentDeterminant := by
  classical
  intro ι _ _ r α β hn
  obtain ⟨j,k,he,hne⟩ := Function.not_injective_iff.mp hn
  have h₀ : r j 0=r k 0 := congrArg Prod.fst he
  have h₁ : r j 1=r k 1 := congrArg Prod.snd he
  apply Matrix.det_zero_of_column_eq hne
  intro i
  simp only [bivariateMonomialValue,h₀,h₁]

private theorem selection_weight {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι → Fin 2 →₀ ℕ) (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (hr : Function.Injective (fun j => (r j 0,r j 1))) :
    (2/3:ℝ)*(Fintype.card ι:ℝ)*Real.sqrt (2*a*b*(Fintype.card ι:ℝ))-
      2*(Fintype.card ι:ℝ)*b≤∑ j : ι, (a*(r j 0:ℝ)+b*(r j 1:ℝ)) := by
  classical
  let S : Finset (ℕ×ℕ) := Finset.univ.image (fun j => (r j 0,r j 1))
  have hcard : S.card=Fintype.card ι := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hr]
    simp
  have hsum : (∑ e ∈ S, (a*(e.1:ℝ)+b*(e.2:ℝ)))=
      ∑ j : ι, (a*(r j 0:ℝ)+b*(r j 1:ℝ)) := by
    dsimp [S]
    rw [Finset.sum_image hr.injOn]
  have hh := (optimized_weight_moment a b ha (ha.trans_le hab) S).2 hab
  rw [hcard,hsum] at hh
  exact hh

private theorem monomial_entry_bound (α β a b : ℝ) (e : Fin 2 →₀ ℕ)
    (hα : |α|≤3*Real.exp (-a)) (hβ : |β|≤8*Real.exp (-b)) :
    |bivariateMonomialValue α β e|≤
      3^(e 0)*8^(e 1)*Real.exp (-(a*(e 0:ℝ)+b*(e 1:ℝ))) := by
  rw [bivariateMonomialValue,abs_mul,abs_pow,abs_pow]
  calc
    _ ≤ (3*Real.exp (-a))^(e 0)*(8*Real.exp (-b))^(e 1) :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hα _)
        (pow_le_pow_left₀ (abs_nonneg _) hβ _) (by positivity) (by positivity)
    _ = _ := by
      rw [mul_pow,mul_pow,←Real.exp_nat_mul,←Real.exp_nat_mul,
        mul_mul_mul_comm,←Real.exp_add]
      congr 1
      congr 1
      ring

/-- Leibniz expansion and the proved lattice moment bound every selected term.
Zero determinants and the empty matrix need no logarithm-domain exception. -/
theorem monomial_weight_determinant : CF04MonomialWeightDeterminant := by
  classical
  intro ι _ _ D C r α β a b ha hab hdeg hα hβ
  let H : ℕ := Fintype.card ι
  let L : ℝ := (2/3:ℝ)*(H:ℝ)*Real.sqrt (2*a*b*(H:ℝ))-2*(H:ℝ)*b
  change |Matrix.det (Matrix.of (fun i j => bivariateMonomialValue (α i) (β i) (r j)))|≤
    (H.factorial:ℝ)*3^(H*D)*8^(H*C)*Real.exp (-L)
  by_cases hr : Function.Injective (fun j => (r j 0,r j 1))
  · let W : ℝ := ∑ j : ι, (a*(r j 0:ℝ)+b*(r j 1:ℝ))
    have hW : L≤W := selection_weight r a b ha hab hr
    have hD : (∑ j : ι, r j 0)≤H*D := by
      simpa [H] using (Finset.sum_le_sum (s:=Finset.univ) (fun j _ => (hdeg j).1))
    have hC : (∑ j : ι, r j 1)≤H*C := by
      simpa [H] using (Finset.sum_le_sum (s:=Finset.univ) (fun j _ => (hdeg j).2))
    have hterm (σ : Equiv.Perm ι) :
        (∏ j : ι, |bivariateMonomialValue (α (σ j)) (β (σ j)) (r j)|)≤
          3^(H*D)*8^(H*C)*Real.exp (-L) := by
      calc
        _ ≤ ∏ j : ι, 3^(r j 0)*8^(r j 1)*
            Real.exp (-(a*(r j 0:ℝ)+b*(r j 1:ℝ))) :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
            (fun j _ => monomial_entry_bound _ _ a b (r j) (hα (σ j)) (hβ (σ j)))
        _ = 3^(∑ j : ι, r j 0)*8^(∑ j : ι, r j 1)*Real.exp (-W) := by
          simp only [W,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
            ←Real.exp_sum,Finset.sum_neg_distrib]
        _ ≤ _ := mul_le_mul
          (mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤3) hD)
            (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤8) hC) (by positivity) (by positivity))
          (Real.exp_le_exp.mpr (neg_le_neg hW)) (by positivity) (by positivity)
    rw [Matrix.det_apply']
    calc
      _ ≤ ∑ σ : Equiv.Perm ι,
          |((Equiv.Perm.sign σ:ℤ):ℝ)*∏ j : ι,
            bivariateMonomialValue (α (σ j)) (β (σ j)) (r j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm ι, ∏ j : ι,
          |bivariateMonomialValue (α (σ j)) (β (σ j)) (r j)| := by
        simp only [abs_mul,abs_unit_intCast,one_mul,Finset.abs_prod]
      _ ≤ ∑ _σ : Equiv.Perm ι, 3^(H*D)*8^(H*C)*Real.exp (-L) :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
      _ = _ := by simp [Fintype.card_perm,H]; ring
  · have hz : Matrix.det (Matrix.of (fun i j =>
        bivariateMonomialValue (α i) (β i) (r j)))=0 :=
      repeated_exponent_determinant ι r α β hr
    rw [hz,abs_zero]
    positivity

end
end P0365Subquarter
