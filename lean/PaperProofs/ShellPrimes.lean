import PaperTargets.ShellPrimes
import PaperProofs.PrimeAssignment

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Absorb the shell's fixed factor in the witness bound, keeping the original
rounded prime scale and a list uniform before all source polynomials. -/
theorem rounded_shell_source_assignment : CF08RoundedShellSourceAssignment := by
  intro D H C δ hH hC hδ
  let K : ℝ := H+2*(D:ℝ)+3
  have hrho : 0<profileRho := by norm_num [profileRho]
  obtain ⟨L,hL⟩ := exists_nat_gt ((K+1)/profileRho)
  have hLK : K+1<profileRho*(L:ℝ) := by
    have hh := (div_lt_iff₀ hrho).mp hL
    nlinarith
  have hLpos : 0<L := by
    have hK : 0≤K+1 := by dsimp [K]; positivity
    by_contra hn
    have hz : L=0 := by omega
    simp [hz] at hLK
    linarith
  obtain ⟨xw,hxw,hw⟩ := actual_source_witness D H C hH hC
  obtain ⟨xr,_,hr⟩ := rounded_prime_scale δ hδ
  refine ⟨L,max (max xw xr) (max 2 ((2:ℝ)^K)),hLpos,?_,?_⟩
  · exact hxw.trans_le ((le_max_left _ _).trans (le_max_left _ _))
  intro X hX ψ hψ0 hψ2
  have hxw' : xw≤X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hxr' : xr≤X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have htwo : (2:ℝ)^K≤X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hX1 : 1<X := hxw.trans_le hxw'
  have hX0 : 0<X := by linarith
  have hscale : X^profileRho≤roundedScale X ψ δ := hr X hxr' ψ hψ0 hψ2
  have hR : 1≤roundedScale X ψ δ := (Real.one_le_rpow hX1.le hrho.le).trans hscale
  have habsorb : (2*X)^K≤X^(K+1) := by
    rw [Real.mul_rpow (by norm_num) hX0.le]
    calc
      _ ≤ X*X^K := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hX0.le _)
      _ = X^(K+1) := by rw [Real.rpow_add hX0 K 1,Real.rpow_one]; ring
  obtain ⟨s,hcard,hs⟩ := bertrand_list L (roundedScale X ψ δ) hR
  refine ⟨s,hcard,hs,?_,?_⟩
  · intro F hD hcoeff n b d u v hsource hn hns
    have hcoeff' : ∀ e, |(F.coeff e:ℝ)|≤C*(2*X)^H := by
      intro e
      exact (hcoeff e).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hX0.le (by linarith) hH) hC)
    obtain ⟨_,hNb,_⟩ := hw (2*X) (by linarith) F hD hcoeff' n b d u v hsource hn hns
    have hprod : (X^profileRho)^L≤∏ p ∈ s, (p:ℝ) := by
      rw [←hcard,←Finset.prod_const]
      apply Finset.prod_le_prod₀
      · intro p _
        exact Real.rpow_nonneg hX0.le _
      · intro p hp
        exact hscale.trans (hs p hp).2.1
    have hstrict : X^(K+1)<(X^profileRho)^L := by
      rw [←Real.rpow_mul_natCast hX0.le]
      exact Real.rpow_lt_rpow_of_exponent_lt hX1 hLK
    have hsize : (sourceWitness F D b d u v).natAbs<∏ p ∈ s, p := by
      have hh : ((sourceWitness F D b d u v).natAbs:ℝ)<∏ p ∈ s, (p:ℝ) := by
        simp only [Nat.cast_natAbs,Int.cast_abs]
        exact (hNb.trans_le habsorb).trans (hstrict.trans_le hprod)
      have hcast : ((sourceWitness F D b d u v).natAbs:ℝ)<((∏ p ∈ s, p:ℕ):ℝ) := by
        simpa only [Nat.cast_prod] using hh
      exact_mod_cast hcast
    obtain ⟨hmem,hgood,_⟩ := first_good_assignment F D n b d u v s hsource hns hD
      (fun p hp => (hs p hp).1) hsize
    refine ⟨hmem,hgood,?_⟩
    have hp := (hs _ hmem).1
    simp only [smoothResidues,dite_eq_right hp.ne_zero,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hgood.2
  · intro F hD
    exact smooth_label_budget F D L (roundedScale X ψ δ) s hD hcard (by linarith)
      (fun p hp => ⟨(hs p hp).1,(hs p hp).2.2⟩)

end
end P0365Subquarter
