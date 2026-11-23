import PaperTargets.ThueLevels
import PaperProofs.DivisorGrowth

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Primitivity of the affine factor forces content1 of its full homogeneous
lift. Characteristic-zero irreducibility supplies rational separability. -/
theorem high_factor_thue_admissibility : CF15HighFactorThueAdmissibility := by
  intro f hf hirr hd
  have hF : f.homogenize f.natDegree ≠ 0 := by
    intro hz
    exact hf.ne_zero (Polynomial.eq_zero_of_homogenize_eq_zero le_rfl hz)
  obtain ⟨hc,_,he,_⟩ := binary_content_removal (f.homogenize f.natDegree) hF
  have ha : f=Polynomial.C (binaryContent (f.homogenize f.natDegree):ℤ)*
      binaryDehomogenize (binaryPrimitivePart (f.homogenize f.natDegree)) := by
    have h := congrArg (MvPolynomial.aeval ![(Polynomial.X:Polynomial ℤ),1]) he
    rw [Polynomial.aeval_homogenize_X_one f le_rfl] at h
    simpa only [map_mul,MvPolynomial.aeval_C,Polynomial.algebraMap_eq,binaryDehomogenize] using h
  have hu := hf (binaryContent (f.homogenize f.natDegree):ℤ) ⟨_,ha⟩
  have hcZ : 0<(binaryContent (f.homogenize f.natDegree):ℤ) := by exact_mod_cast hc
  have hc1 : binaryContent (f.homogenize f.natDegree)=1 := by
    rcases Int.isUnit_eq_one_or hu with hp | hn
    · exact_mod_cast hp
    · omega
  have hhom := Polynomial.isHomogeneous_homogenize (n := f.natDegree) f
  exact ⟨hc1,hhom,hF,hhom.totalDegree hF,hirr.separable⟩

/-- This application remains conditional on the one precise external input;
all content/separability admissibility for the selected factor is derived. -/
theorem irreducible_thue_level : CF15IrreducibleThueLevel := by
  intro hThue f hf hirr hd hdu h hh S hS
  obtain ⟨hc,_,_,_,hsep⟩ := high_factor_thue_admissibility f hf hirr hd
  have hs := hThue f hc hsep hd hdu h hh S hS
  simpa only [pow_add,pow_one,mul_assoc] using hs

private theorem finite_fiber_bound {α β : Type} [DecidableEq β] (S : Finset α) (T : Finset β)
    (f : α → β) (k : ℕ) (hmap : ∀ z ∈ S, f z ∈ T)
    (hfib : ∀ r ∈ T, (S.filter (fun z => f z=r)).card ≤ k) : S.card ≤ T.card*k := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := T) (fun z hz => hmap z hz)]
  calc
    _ ≤ ∑ r ∈ T, k := Finset.sum_le_sum hfib
    _ = _ := by simp


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


private theorem signed_divisor_abs_dvd (h a : ℤ) (ha : a ∈ signedLevelDivisors h) : a.natAbs ∣ h.natAbs := by
  classical
  rcases Finset.mem_union.mp ha with hp | hm
  · obtain ⟨n,hnd,rfl⟩ := Finset.mem_image.mp hp
    simpa using Nat.dvd_of_mem_divisors hnd
  · obtain ⟨n,hnd,rfl⟩ := Finset.mem_image.mp hm
    simpa using Nat.dvd_of_mem_divisors hnd

/-- Evaluate one fixed high factor. Nonzero Q-levels force its value into
signed divisors, and prime support only decreases along those divisors. -/
theorem high_factor_level_budget : CF15HighFactorLevelBudget := by
  classical
  intro hThue Q f hf hirr hd hdu hfdvd h hh S hS
  let F := f.homogenize f.natDegree
  let value : (Fin 2 → ℤ) → ℤ := fun z => MvPolynomial.eval z F
  have hmap (z : Fin 2 → ℤ) (hz : z ∈ S) : value z ∈ signedLevelDivisors h := by
    obtain ⟨K,hK⟩ := hfdvd
    have hdiv : value z ∣ h := by
      refine ⟨MvPolynomial.eval z K,?_⟩
      rw [← (hS z hz).2,hK,map_mul]
    exact signed_divisor_mem h (value z) hh hdiv
  have hfib (r : ℤ) (hr : r ∈ signedLevelDivisors h) :
      (S.filter (fun z => value z=r)).card ≤ 30800*f.natDegree^(primeSupportCount h.natAbs) := by
    have hrn := signed_divisor_nonzero h r hr
    have hprec := irreducible_thue_level hThue f hf hirr hd hdu r hrn
      (S.filter (fun z => value z=r)) (by
        intro z hz
        obtain ⟨hzS,he⟩ := Finset.mem_filter.mp hz
        exact ⟨(hS z hzS).1,he⟩)
    have hsupport : primeSupportCount r.natAbs ≤ primeSupportCount h.natAbs :=
      Finset.card_le_card (Nat.primeFactors_mono (signed_divisor_abs_dvd h r hr) (by simpa using hh))
    have hp := pow_le_pow_right₀ (show 1≤f.natDegree by omega) hsupport
    calc
      _ ≤ 2800*f.natDegree*f.natDegree^(primeSupportCount r.natAbs) := hprec
      _ ≤ 2800*f.natDegree*f.natDegree^(primeSupportCount h.natAbs) := Nat.mul_le_mul_left _ hp
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hc := finite_fiber_bound S (signedLevelDivisors h) value
    (30800*f.natDegree^(primeSupportCount h.natAbs)) hmap hfib
  calc
    S.card ≤ (signedLevelDivisors h).card*(30800*f.natDegree^(primeSupportCount h.natAbs)) := hc
    _ ≤ (2*divisorCount h.natAbs)*(30800*f.natDegree^(primeSupportCount h.natAbs)) :=
      Nat.mul_le_mul_right _ (signed_divisors_card h)
    _ = _ := by ring

/-- Exhaustive factor selection precedes all h and all parameter subsets. -/
theorem selected_factor_level_budget : CF15SelectedFactorLevelBudget := by
  intro hThue Q hdispatch
  rcases hdispatch with ⟨G,H,hpair,hG,hH⟩ | ⟨f,hf,hirr,hd,hdu,hdiv⟩
  · intro h hh S hS
    exact (low_factor_divisor_budget Q G H hpair hG hH h hh S hS).trans (Nat.le_add_right _ _)
  · intro h hh S hS
    have hcount := high_factor_level_budget hThue Q f hf hirr hd hdu hdiv h hh S hS
    have hp : f.natDegree^(primeSupportCount h.natAbs) ≤ 11^(primeSupportCount h.natAbs) :=
      Nat.pow_le_pow_left hdu _
    exact (hcount.trans (Nat.mul_le_mul_left _ hp)).trans (Nat.le_add_left _ _)

/-- Apply the selected factor budget to the actual primitive pullback in
both charts. The precise external premise remains explicit. -/
theorem actual_graph_level_budget : CF15ActualGraphLevelBudget := by
  intro hThue X D A B hX hg hr inverse
  exact selected_factor_level_budget hThue _ (actual_graph_factor_dispatch X D A B hX hg hr inverse)

end
end P0365Subquarter
