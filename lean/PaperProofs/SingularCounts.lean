import PaperTargets.SingularCounts
import PaperProofs.CanonicalSource
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Localization.FractionRing

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private abbrev Plane := MvPolynomial (Fin 2) ℚ
private abbrev Bivar := Polynomial (Polynomial ℚ)
private def planeEquiv : Bivar ≃ₐ[ℚ] Plane := Polynomial.Bivariate.equivMvPolynomial ℚ
private def integralBivar : SourcePolynomial →+* Bivar :=
  planeEquiv.symm.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℚ))

private theorem integralBivar_eq : integralBivar=MvPolynomial.eval₂Hom
    (Polynomial.C.comp (Polynomial.C.comp (Int.castRingHom ℚ)))
    ![Polynomial.C Polynomial.X,Polynomial.X] := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [integralBivar,planeEquiv]
  · intro i
    fin_cases i <;> simp [integralBivar,planeEquiv]

private theorem bivar_expansion (F : SourcePolynomial) :
    integralBivar F=∑ e ∈ F.support,
      Polynomial.monomial (e 1) (Polynomial.monomial (e 0) (F.coeff e:ℚ)) := by
  rw [integralBivar_eq]
  change MvPolynomial.eval₂ _ _ F=_
  simp only [MvPolynomial.eval₂_eq',Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply Finset.sum_congr rfl
  intro e _
  simp only [←Polynomial.C_mul_X_pow_eq_monomial,RingHom.comp_apply,Int.coe_castRingHom,map_mul,map_pow]
  ring

private theorem source_support_degree (F : SourcePolynomial) (D : ℕ)
    (hD : F.totalDegree≤D) (e : Fin 2 →₀ ℕ) (he : e∈F.support) : e 0+e 1≤D := by
  have h := (MvPolynomial.le_totalDegree he).trans hD
  rwa [Finsupp.sum_fintype e (fun _ a => a) (fun _ => rfl),Fin.sum_univ_two] at h

private theorem bivar_degree (F : SourcePolynomial) (D : ℕ) (hD : F.totalDegree≤D) :
    (integralBivar F).natDegree≤D := by
  rw [bivar_expansion]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  have hd := source_support_degree F D hD e he
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

private theorem bivar_coeff_degree (F : SourcePolynomial) (D : ℕ) (hD : F.totalDegree≤D)
    (k : ℕ) : ((integralBivar F).coeff k).natDegree≤D := by
  rw [bivar_expansion,Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  have hd := source_support_degree F D hD e he
  rw [Polynomial.coeff_monomial]
  split_ifs
  · exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  · simp

private theorem eval_plane (f : Plane) (z : Fin 2 → ℚ) :
    (planeEquiv.symm f).evalEval (z 0) (z 1)=MvPolynomial.eval z f := by
  have hh : (Polynomial.evalEvalRingHom (z 0) (z 1)).comp planeEquiv.symm.toRingHom=
      MvPolynomial.eval₂Hom (RingHom.id ℚ) z := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [planeEquiv]
    · intro i
      fin_cases i <;> simp [planeEquiv]
  exact congrArg (fun h : Plane →+* ℚ => h f) hh

private theorem eval_integral (F : SourcePolynomial) (z : Fin 2 → ℚ) :
    (integralBivar F).evalEval (z 0) (z 1)=polynomialValue F z := by
  change (planeEquiv.symm (MvPolynomial.map (Int.castRingHom ℚ) F)).evalEval (z 0) (z 1)=_
  rw [eval_plane]
  exact (MvPolynomial.eval₂_eq_eval_map _ _ _).symm

private theorem eval_partial (F : SourcePolynomial) (z : Fin 2 → ℚ) (i : Fin 2) :
    MvPolynomial.eval z (MvPolynomial.pderiv i (rationalSourcePolynomial F))=
      polynomialValue (MvPolynomial.pderiv i F) z := by
  rw [rationalSourcePolynomial,MvPolynomial.pderiv_map]
  exact (MvPolynomial.eval₂_eq_eval_map _ _ _).symm

private theorem singular_fiber_nonzero (f : Plane) (hf : Irreducible f) (z : Fin 2 → ℚ)
    (hgrad : ∀ i : Fin 2, MvPolynomial.eval z (MvPolynomial.pderiv i f)=0) :
    ((planeEquiv.symm f).map (Polynomial.evalRingHom (z 0)))≠0 := by
  intro hz
  let P := planeEquiv.symm f
  let l : Polynomial ℚ := Polynomial.X-Polynomial.C (z 0)
  have hc : ∀ k, l∣P.coeff k := by
    intro k
    apply Polynomial.dvd_iff_isRoot.mpr
    have hh := congrArg (fun Q : Polynomial ℚ => Q.coeff k) hz
    simpa [P,Polynomial.coeff_map] using hh
  obtain ⟨Q,hQ⟩ := (Polynomial.C_dvd_iff_dvd_coeff l P).mpr hc
  let L : Plane := MvPolynomial.X 0-MvPolynomial.C (z 0)
  have heq : f=L*planeEquiv Q := by
    have hh := congrArg (fun T : Bivar => planeEquiv T) hQ
    simpa [P,L,l,planeEquiv] using hh
  have hL : ¬IsUnit L := by
    intro hu
    exact (hu.map (MvPolynomial.eval₂Hom (RingHom.id ℚ) ![z 0,0])).ne_zero (by simp [L])
  have hG : IsUnit (planeEquiv Q) := (hf.isUnit_or_isUnit heq).resolve_left hL
  have hg := hgrad 0
  rw [heq,MvPolynomial.pderiv_mul] at hg
  have hv : MvPolynomial.eval z (planeEquiv Q)=0 := by simpa [L] using hg
  exact (hG.map (MvPolynomial.eval₂Hom (RingHom.id ℚ) z)).ne_zero hv

private theorem bivar_derivative_coeff_degree (P : Bivar) (D : ℕ)
    (hP : ∀ k, (P.coeff k).natDegree≤D) (k : ℕ) :
    (P.derivative.coeff k).natDegree≤D := by
  rw [Polynomial.coeff_derivative]
  exact Polynomial.natDegree_mul_le.trans (by
    simpa only [←Nat.cast_succ,Polynomial.natDegree_natCast,add_zero] using hP (k+1))

private theorem polynomial_det_degree (n D : ℕ)
    (A : Matrix (Fin n) (Fin n) (Polynomial ℚ))
    (hA : ∀ i j, (A i j).natDegree≤D) : A.det.natDegree≤n*D := by
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hp : (∏ i, A (σ i) i).natDegree≤n*D := by
    calc
      _ ≤ ∑ i, (A (σ i) i).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin n, D := Finset.sum_le_sum (fun i _ => hA (σ i) i)
      _ = n*D := by simp
  exact Polynomial.natDegree_mul_le.trans (by
    simpa only [Polynomial.natDegree_intCast,zero_add] using hp)

private theorem resultant_degree (P Q : Bivar) (m n D : ℕ)
    (hP : ∀ k, (P.coeff k).natDegree≤D) (hQ : ∀ k, (Q.coeff k).natDegree≤D) :
    (P.resultant Q m n).natDegree≤(m+n)*D := by
  unfold Polynomial.resultant
  apply polynomial_det_degree
  intro i j
  induction j using Fin.addCases <;>
    simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_left,Fin.addCases_right]
  all_goals split_ifs
  all_goals first | exact hP _ | exact hQ _ | simp

private theorem irreducible_resultant_nonzero (P : Bivar) (hP : Irreducible P)
    (hpos : 0<P.natDegree) : P.resultant P.derivative≠0 := by
  let K := FractionRing (Polynomial ℚ)
  let φ : Polynomial ℚ →+* K := algebraMap _ _
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hp := hP.isPrimitive hpos.ne'
  have hir : Irreducible (P.map φ) :=
    (hp.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hP
  have hcop : IsCoprime (P.map φ) (P.derivative.map φ) := by
    simpa only [Polynomial.Separable,Polynomial.derivative_map] using hir.separable
  have hr := Polynomial.resultant_ne_zero (P.map φ) (P.derivative.map φ) hcop
  intro hz
  apply hr
  simp only [Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.resultant_map_map,hz,map_zero]

private theorem rational_root_card (P : Polynomial ℚ) (hP : P≠0) (T : Finset ℚ)
    (hT : ∀ x ∈ T, P.eval x=0) : T.card≤P.natDegree := by
  classical
  have hs : T⊆P.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr (hT x hx))
  exact (Finset.card_le_card hs).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P))

private theorem eval_bivar_derivative (P : Bivar) (z : Fin 2 → ℚ) :
    P.derivative.evalEval (z 0) (z 1)=
      MvPolynomial.eval z (MvPolynomial.pderiv 1 (planeEquiv P)) := by
  change _=MvPolynomial.eval z (MvPolynomial.pderiv 1
    (Polynomial.Bivariate.equivMvPolynomial ℚ P))
  rw [Polynomial.Bivariate.pderiv_one_equivMvPolynomial]
  simpa only [planeEquiv,AlgEquiv.symm_apply_apply] using
    eval_plane (planeEquiv P.derivative) z

private theorem singular_data (F : SourcePolynomial)
    (hir : Irreducible (rationalSourcePolynomial F)) (z : Fin 2 → ℚ)
    (hz : singularRationalPoint F z) :
    ((integralBivar F).map (Polynomial.evalRingHom (z 0))≠0) ∧
      (integralBivar F).evalEval (z 0) (z 1)=0 ∧
      (integralBivar F).derivative.evalEval (z 0) (z 1)=0 := by
  have hgrad : ∀ i : Fin 2,
      MvPolynomial.eval z (MvPolynomial.pderiv i (rationalSourcePolynomial F))=0 :=
    fun i => (eval_partial F z i).trans (hz.2 i)
  refine ⟨singular_fiber_nonzero _ hir z hgrad,(eval_integral F z).trans hz.1,?_⟩
  have hh := eval_bivar_derivative (integralBivar F) z
  have he : planeEquiv (integralBivar F)=rationalSourcePolynomial F :=
    planeEquiv.apply_symm_apply _
  rw [he] at hh
  exact hh.trans (hgrad 1)

private theorem common_eval_resultant_zero (P Q : Bivar) (m n : ℕ)
    (hm : P.natDegree≤m) (hn : Q.natDegree≤n) (hsize : m≠0 ∨ n≠0)
    (x y : ℚ) (hp : P.evalEval x y=0) (hq : Q.evalEval x y=0) :
    (P.resultant Q m n).eval x=0 := by
  obtain ⟨A,B,_,_,hAB⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant P Q hm hn hsize
  have hh := congrArg (Polynomial.evalEval x y) hAB
  simpa [hp,hq,Polynomial.evalEval_C] using hh.symm

/-- Eliminate at the actual fiber degrees and count projected roots and fibers. -/
theorem singular_rational_point_count : CF06SingularRationalPointCount := by
  classical
  intro D F hD hir S hS
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  let P := integralBivar F
  have hP : Irreducible P := hir.map planeEquiv.symm.toMulEquiv
  have hPD : P.natDegree≤D := bivar_degree F D hD
  have hcoeff : ∀ k, (P.coeff k).natDegree≤D := bivar_coeff_degree F D hD
  obtain ⟨z₀,hz₀⟩ := hne
  obtain ⟨hfiber,hroot,_⟩ := singular_data F hir z₀ (hS z₀ hz₀)
  have hpos : 0<P.natDegree := by
    have hsmall : 0<(P.map (Polynomial.evalRingHom (z₀ 0))).natDegree :=
      Polynomial.natDegree_pos_of_eval₂_root hfiber (RingHom.id ℚ) (by
        change (P.map (Polynomial.evalRingHom (z₀ 0))).eval (z₀ 1)=0
        rw [Polynomial.map_evalRingHom_eval]
        exact hroot) (fun x hx => hx)
    exact hsmall.trans_le Polynomial.natDegree_map_le
  let R := P.resultant P.derivative
  have hR : R≠0 := irreducible_resultant_nonzero P hP hpos
  have hRD : R.natDegree≤2*D^2 := by
    have hder : P.derivative.natDegree≤D :=
      (Polynomial.natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hPD)
    calc
      _ ≤ (P.natDegree+P.derivative.natDegree)*D :=
        resultant_degree P P.derivative _ _ D hcoeff (bivar_derivative_coeff_degree P D hcoeff)
      _ ≤ (2*D)*D := Nat.mul_le_mul_right D (by omega)
      _ = 2*D^2 := by ring
  let V := S.image (fun z => z 0)
  let A := fun x : ℚ => S.filter (fun z => z 0=x)
  have hVR : ∀ x ∈ V, R.eval x=0 := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_,hp,hq⟩ := singular_data F hir z (hS z hz)
    exact common_eval_resultant_zero P P.derivative _ _ le_rfl le_rfl
      (Or.inl hpos.ne') (z 0) (z 1) hp hq
  have hcardV : V.card≤2*D^2 := (rational_root_card R hR V hVR).trans hRD
  have hfiberCard : ∀ x ∈ V, (A x).card≤D := by
    intro x hx
    obtain ⟨z₁,hz₁,hx₁⟩ := Finset.mem_image.mp hx
    let Q := P.map (Polynomial.evalRingHom x)
    have hQ : Q≠0 := by
      have hh := (singular_data F hir z₁ (hS z₁ hz₁)).1
      simpa only [hx₁] using hh
    have hinj : Set.InjOn (fun z : Fin 2 → ℚ => z 1) (↑(A x) : Set (Fin 2 → ℚ)) := by
      intro z hz w hw he
      obtain ⟨_,hzx⟩ := Finset.mem_filter.mp hz
      obtain ⟨_,hwx⟩ := Finset.mem_filter.mp hw
      ext i
      fin_cases i
      · exact hzx.trans hwx.symm
      · exact he
    have hr : ∀ y ∈ (A x).image (fun z => z 1), Q.eval y=0 := by
      intro y hy
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hzS,hzx⟩ := Finset.mem_filter.mp hz
      change (P.map (Polynomial.evalRingHom x)).eval (z 1)=0
      rw [←hzx,Polynomial.map_evalRingHom_eval]
      exact (eval_integral F z).trans (hS z hzS).1
    calc
      (A x).card=((A x).image (fun z => z 1)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ Q.natDegree := rational_root_card Q hQ _ hr
      _ ≤ P.natDegree := Polynomial.natDegree_map_le
      _ ≤ D := hPD
  have hcover : S⊆V.biUnion A := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨z 0,Finset.mem_image.mpr ⟨z,hz,rfl⟩,
      Finset.mem_filter.mpr ⟨hz,rfl⟩⟩
  calc
    S.card≤(V.biUnion A).card := Finset.card_le_card hcover
    _ ≤ V.card*D := Finset.card_biUnion_le_card_mul V A D hfiberCard
    _ ≤ (2*D^2)*D := Nat.mul_le_mul_right D hcardV
    _ = 2*D^3 := by ring

/-- Canonical primitive ratios inject original starts into the proved point set. -/
theorem actual_singular_source_count : CF06ActualSingularSourceCount := by
  classical
  intro D F hD hir S hS
  have hw : ∀ n : ℕ, ∃ b d u v : ℕ, n∈S →
      PairSource n b d u v ∧ singularRationalPoint F (sourcePoint b d u v) := by
    intro n
    by_cases hn : n∈S
    · obtain ⟨b,d,u,v,hs,hz⟩ := hS n hn
      exact ⟨b,d,u,v,fun _ => ⟨hs,hz⟩⟩
    · exact ⟨0,0,0,0,fun h => False.elim (hn h)⟩
  choose b d u v hs using hw
  let z := fun n => sourcePoint (b n) (d n) (u n) (v n)
  have hinj : Set.InjOn z (↑S:Set ℕ) := by
    intro n hn m hm he
    apply source_ratio_injection n m (b n) (d n) (u n) (v n)
      (b m) (d m) (u m) (v m) (hs n hn).1 (hs m hm).1
    apply Prod.ext
    · simpa [z,SourceRatios,sourcePoint] using congrFun he 0
    · simpa [z,SourceRatios,sourcePoint] using congrFun he 1
  calc
    S.card=(S.image z).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ 2*D^3 := singular_rational_point_count D F hD hir (S.image z) (by
      intro w hw
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hw
      exact (hs n hn).2)

end
end P0365Subquarter
