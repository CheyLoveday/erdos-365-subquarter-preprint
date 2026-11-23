import PaperTargets.IntervalCounts
import PaperProofs.ClassCounts
import PaperProofs.ShellPrimes
import PaperProofs.FactorInventory
import PaperProofs.SingularCounts

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem real_cover_card {ι α : Type} [DecidableEq α] (S : Finset α) (I : Finset ι)
    (A : ι → Finset α) (f : ι → ℝ) (hcover : S⊆I.biUnion A)
    (hA : ∀ i ∈ I, ((A i).card:ℝ)≤f i) :
    (S.card:ℝ)≤∑ i ∈ I, f i := by
  classical
  have hc : S.card≤∑ i ∈ I, (A i).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hcast : (S.card:ℝ)≤∑ i ∈ I, ((A i).card:ℝ) := by exact_mod_cast hc
  exact hcast.trans (Finset.sum_le_sum hA)

/-- Derive all labels, count their actual source fibers, and include singulars. -/
theorem irreducible_interval_source_count : CF17IrreducibleIntervalSourceCount := by
  classical
  intro hThue D H C δ hH hC hδ hδ1 ε hε
  obtain ⟨L,xp,hL,hxp,hprime⟩ := rounded_shell_source_assignment D H C δ hH hC hδ
  obtain ⟨xc,Cc,hxc,hCc,hclass⟩ := rounded_class_source_subpower hThue δ hδ hδ1 ε hε
  obtain ⟨xr,_,hscale⟩ := rounded_prime_scale δ hδ
  let J : ℝ := (L:ℝ)*D*2^(L+1)
  let σ : ℝ := 2*(D:ℝ)^3
  let K : ℝ := σ+Cc*J+1
  have hJ : 0≤J := by dsimp [J]; positivity
  have hσ : 0≤σ := by dsimp [σ]; positivity
  refine ⟨max (max xp xc) xr,K,?_,?_,?_⟩
  · exact hxc.trans ((le_max_right _ _).trans (le_max_left _ _))
  · dsimp [K]; positivity
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F hD hir hcoeff S b d u v
    hsource hbox hint hzero
  have hxp' : xp≤X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hxc' : xc≤X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hxr' : xr≤X := (le_max_right _ _).trans hX
  have hX32 : 32≤X := hxc.trans hxc'
  have hX1 : 1≤X := by linarith
  have hR1 : 1≤roundedScale X ψ δ :=
    (Real.one_le_rpow hX1 (by norm_num [profileRho])).trans (hscale X hxr' ψ hψ0 hψ2)
  have hpow : 1≤X^ε := Real.one_le_rpow hX1 hε.le
  have hprod : 1≤roundedScale X ψ δ*X^ε := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR1) (sub_nonneg.mpr hpow)]
  obtain ⟨s,_,hs,hassign,hbudget⟩ := hprime X hxp' ψ hψ0 hψ2
  let A := S.filter (fun n => singularRationalPoint F (sourcePoint (b n) (d n) (u n) (v n)))
  let N := S.filter (fun n => ¬singularRationalPoint F (sourcePoint (b n) (d n) (u n) (v n)))
  have hAS : A⊆S := Finset.filter_subset _ _
  have hNS : N⊆S := Finset.filter_subset _ _
  have hA : (A.card:ℝ)≤σ := by
    have hc := actual_singular_source_count D F hD hir A (by
      intro n hn
      exact ⟨b n,d n,u n,v n,hsource n (hAS hn),(Finset.mem_filter.mp hn).2⟩)
    dsimp [σ]
    exact_mod_cast hc
  have hns : ∀ n ∈ N, nonsingularSource F (b n) (d n) (u n) (v n) := by
    intro n hn
    obtain ⟨hnS,hnots⟩ := Finset.mem_filter.mp hn
    refine ⟨hzero n hnS,?_⟩
    by_contra! h
    exact hnots ⟨hzero n hnS,h⟩
  have hlabel (n : ℕ) (hn : n∈N) :=
    hassign F hD hcoeff n (b n) (d n) (u n) (v n) (hsource n (hNS hn))
      (hbox n (hNS hn)).2.1 (hns n hn)
  let T := fun (p : ℕ) (z : Fin 2 → ZMod p) => N.filter (fun n =>
    firstGoodPrime F (b n) (d n) (u n) (v n) s=p ∧
      sourceReduction (b n) (d n) (u n) (v n) p=z)
  let U := fun p : ℕ => (smoothResidues F p).biUnion (T p)
  have hT (p : ℕ) (hp : p∈s) (z : Fin 2 → ZMod p) (_ : z∈smoothResidues F p) :
      ((T p z).card:ℝ)≤Cc*X^ε := by
    have hTN : T p z⊆N := Finset.filter_subset _ _
    have hTS : T p z⊆S := fun _ hn => hNS (hTN hn)
    apply hclass X ψ B E a hxc' hψ0 hψ2 hB hE ha hBE F p z (T p z) b d u v
      (hs p hp).1 (hs p hp).2.1
      (fun n hn => hsource n (hTS hn)) (fun n hn => hbox n (hTS hn))
      (fun n hn => hint n (hTS hn)) (fun n hn => hzero n (hTS hn))
    · intro n hn
      have hh := (hlabel n (hTN hn)).2.1
      simpa only [(Finset.mem_filter.mp hn).2.1] using hh
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.2
  have hU (p : ℕ) (hp : p∈s) :
      ((U p).card:ℝ)≤((smoothResidues F p).card:ℝ)*(Cc*X^ε) := by
    calc
      _ ≤ ∑ z ∈ smoothResidues F p, Cc*X^ε :=
        real_cover_card (U p) _ (T p) (fun _ => Cc*X^ε) (fun _ hn => hn) (hT p hp)
      _ = _ := by simp
  have hNcover : N⊆s.biUnion U := by
    intro n hn
    obtain ⟨hpmem,_,hzmem⟩ := hlabel n hn
    apply Finset.mem_biUnion.mpr
    refine ⟨_,hpmem,Finset.mem_biUnion.mpr ⟨_,hzmem,?_⟩⟩
    exact Finset.mem_filter.mpr ⟨hn,rfl,rfl⟩
  have hN : (N.card:ℝ)≤Cc*J*(roundedScale X ψ δ*X^ε) := by
    calc
      _ ≤ ∑ p ∈ s, ((smoothResidues F p).card:ℝ)*(Cc*X^ε) :=
        real_cover_card N s U _ hNcover hU
      _ = (∑ p ∈ s, ((smoothResidues F p).card:ℝ))*(Cc*X^ε) := by rw [Finset.sum_mul]
      _ ≤ (J*roundedScale X ψ δ)*(Cc*X^ε) :=
        mul_le_mul_of_nonneg_right (hbudget F hD) (by positivity)
      _ = _ := by ring
  have hScard : S.card≤A.card+N.card := by
    apply (Finset.card_le_card (show S⊆A∪N from ?_)).trans (Finset.card_union_le A N)
    intro n hn
    by_cases hz : singularRationalPoint F (sourcePoint (b n) (d n) (u n) (v n))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,hz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,hz⟩)
  have hScast : (S.card:ℝ)≤(A.card:ℝ)+(N.card:ℝ) := by exact_mod_cast hScard
  calc
    (S.card:ℝ) ≤ (A.card:ℝ)+(N.card:ℝ) := hScast
    _ ≤ σ+Cc*J*(roundedScale X ψ δ*X^ε) := add_le_add hA hN
    _ ≤ σ*(roundedScale X ψ δ*X^ε)+Cc*J*(roundedScale X ψ δ*X^ε) :=
      add_le_add (le_mul_of_one_le_right hσ hprod) le_rfl
    _ ≤ K*roundedScale X ψ δ*X^ε := by
      dsimp [K]
      nlinarith [show 0≤roundedScale X ψ δ*X^ε from le_trans zero_le_one hprod]

/-- Produce the actual coarse factors, use one uniform height, and sum curves. -/
theorem coarse_interval_source_count : CF17CoarseIntervalSourceCount := by
  classical
  intro hThue D H C δ hH hC hδ hδ1 ε hε
  obtain ⟨Cf,hCf,hfactor⟩ := uniform_primitive_factor_cover D H C hH hC
  obtain ⟨X₀,Ki,hX₀,hKi,hinterval⟩ :=
    irreducible_interval_source_count hThue D H Cf δ hH hCf.le hδ hδ1 ε hε
  refine ⟨X₀,(D:ℝ)*Ki+1,hX₀,by positivity,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F hF hD hcoeff S b d u v
    hsource hbox hint hzero
  have hX32 : 32≤X := hX₀.trans hX
  have hX1 : 1≤X := by linarith
  have hXp : 0<X^ε := Real.rpow_pos_of_pos (by linarith) _
  have hRp : 0<roundedScale X ψ δ := by
    have hM := (rounded_height_bounds X ψ δ hX1 hψ0 hψ2 hδ.le).1
    exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)
  obtain ⟨s,hcard,hfac,hcover⟩ := hfactor X hX1 F hF hD hcoeff
  let T := fun A : SourcePolynomial => S.filter (fun n =>
    polynomialValue A (sourcePoint (b n) (d n) (u n) (v n))=0)
  have hScover : S⊆s.biUnion T := by
    intro n hn
    obtain ⟨A,hA,hz⟩ := hcover _ (hzero n hn)
    exact Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_filter.mpr ⟨hn,hz⟩⟩
  have hT (A : SourcePolynomial) (hA : A∈s) :
      ((T A).card:ℝ)≤Ki*roundedScale X ψ δ*X^ε := by
    obtain ⟨_,_,hAD,_,hAir,hAc⟩ := hfac A hA
    have hTS : T A⊆S := Finset.filter_subset _ _
    exact hinterval X ψ B E a hX hψ0 hψ2 hB hE ha hBE A hAD hAir hAc
      (T A) b d u v (fun n hn => hsource n (hTS hn))
      (fun n hn => hbox n (hTS hn)) (fun n hn => hint n (hTS hn))
      (fun n hn => (Finset.mem_filter.mp hn).2)
  calc
    (S.card:ℝ) ≤ ∑ A ∈ s, Ki*roundedScale X ψ δ*X^ε :=
      real_cover_card S s T _ hScover hT
    _ = (s.card:ℝ)*(Ki*roundedScale X ψ δ*X^ε) := by simp
    _ ≤ (D:ℝ)*(Ki*roundedScale X ψ δ*X^ε) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ ((D:ℝ)*Ki+1)*roundedScale X ψ δ*X^ε := by nlinarith

end
end P0365Subquarter
