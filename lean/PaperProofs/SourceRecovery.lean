import PaperTargets.SourceRecovery
import PaperProofs.HomogeneousResultants

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- A positive reduced ratio fixes the signed integral vector up to its
positive evaluated gcd. Both sign possibilities remain explicit. -/
theorem primitive_signed_recovery : CF13PrimitiveSignedRecovery := by
  intro v u hv hu hcop a b ha0 hb0 he
  have huZ : (u:ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hu
  have huQ : (u:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hu
  have hbQ : (b:ℚ) ≠ 0 := by exact_mod_cast hb0
  have hcross : (v:ℤ)*b=a*(u:ℤ) := by
    exact_mod_cast (div_eq_div_iff huQ hbQ).mp he
  have hub : (u:ℤ) ∣ b := hcop.symm.isCoprime.dvd_of_dvd_mul_left
    (show (u:ℤ) ∣ (v:ℤ)*b by rw [hcross]; exact dvd_mul_left _ _)
  obtain ⟨k,hb⟩ := hub
  have ha : a=(v:ℤ)*k := by
    apply mul_right_cancel₀ huZ
    calc
      a*(u:ℤ) = (v:ℤ)*b := hcross.symm
      _ = _ := by rw [hb]; ring
  have hk : k ≠ 0 := by intro h; apply hb0; rw [hb,h,mul_zero]
  have hg : Int.gcd a b=k.natAbs := by
    rw [ha,hb,Int.gcd_mul_right,Int.gcd_natCast_natCast,hcop.gcd_eq_one,one_mul]
  have hgZ : (Int.gcd a b : ℤ)=|k| := by rw [hg,Int.natCast_natAbs]
  have hgpos : 0 < Int.gcd a b := Int.gcd_pos_of_ne_zero_left b ha0
  have hg0 : (Int.gcd a b : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hgpos
  have finish (σ : ℤ) (hσ : σ=1 ∨ σ = -1)
      (ha' : a=σ*(Int.gcd a b:ℤ)*(v:ℤ)) (hb' : b=σ*(Int.gcd a b:ℤ)*(u:ℤ)) :
      ∃ σ : ℤ, (σ=1 ∨ σ = -1) ∧ 0<Int.gcd a b ∧
        a=σ*(Int.gcd a b:ℤ)*(v:ℤ) ∧ b=σ*(Int.gcd a b:ℤ)*(u:ℤ) ∧
        (v:ℤ)=σ*a/(Int.gcd a b:ℤ) ∧ (u:ℤ)=σ*b/(Int.gcd a b:ℤ) := by
    have hσ2 : σ*σ=1 := by rcases hσ with rfl | rfl <;> norm_num
    have hd (z w : ℤ) (hz : z=σ*(Int.gcd a b:ℤ)*w) : w=σ*z/(Int.gcd a b:ℤ) := by
      symm
      calc
        _ = (Int.gcd a b:ℤ)*w/(Int.gcd a b:ℤ) := by
          congr 1
          rw [hz]
          calc
            _ = (σ*σ)*((Int.gcd a b:ℤ)*w) := by ring
            _ = _ := by rw [hσ2,one_mul]
        _ = w := Int.mul_ediv_cancel_left _ hg0
    exact ⟨σ,hσ,hgpos,ha',hb',hd _ _ ha',hd _ _ hb'⟩
  rcases lt_or_gt_of_ne hk with hn | hp
  · apply finish (-1) (Or.inr rfl)
    · rw [hgZ,abs_of_neg hn,ha]; ring
    · rw [hgZ,abs_of_neg hn,hb]; ring
  · apply finish 1 (Or.inl rfl)
    · rw [hgZ,abs_of_pos hp,ha]; ring
    · rw [hgZ,abs_of_pos hp,hb]; ring

private theorem content_dvd_coeff (H : SourcePolynomial) (e : Fin 2 →₀ ℕ) :
    (binaryContent H : ℤ) ∣ H.coeff e := by
  classical
  apply Int.natCast_dvd.mpr
  by_cases he : e ∈ H.support
  · exact Finset.gcd_dvd he
  · simp [MvPolynomial.notMem_support_iff.mp he]

private theorem primitive_coeff (H : SourcePolynomial) (e : Fin 2 →₀ ℕ) :
    (binaryPrimitivePart H).coeff e=H.coeff e/(binaryContent H:ℤ) := by
  classical
  simp only [binaryPrimitivePart,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d hd hde
    exact ite_eq_right (fun h => hde h)
  · intro he
    simp [MvPolynomial.notMem_support_iff.mp he]

/-- The explicit coefficient gcd and exact integral quotients construct
one primitive polynomial; no primitive-content hypothesis is assumed. -/
theorem binary_content_removal : CF13BinaryContentRemoval := by
  classical
  intro H hH
  let c := binaryContent H
  let Q := binaryPrimitivePart H
  have hc : 0<c := by
    by_contra hn
    have hz : binaryContent H=0 := by dsimp [c] at hn; omega
    have hh := Finset.gcd_eq_zero_iff.mp hz
    apply hH
    ext e
    by_cases he : e ∈ H.support
    · simpa using hh e he
    · exact MvPolynomial.notMem_support_iff.mp he
  have hcZ : (c:ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  have hfactor : H=MvPolynomial.C (c:ℤ)*Q := by
    ext e
    rw [MvPolynomial.coeff_C_mul,primitive_coeff]
    exact (Int.mul_ediv_cancel' (content_dvd_coeff H e)).symm
  have hs : H.support=Q.support := by
    ext e
    have he := congrArg (fun P : SourcePolynomial => P.coeff e) hfactor
    simp only [MvPolynomial.coeff_C_mul] at he
    simp only [MvPolynomial.mem_support_iff,he,mul_ne_zero_iff]
    exact and_iff_right hcZ
  have hex : ∃ e ∈ H.support, (H.coeff e).natAbs ≠ 0 :=
    Finset.gcd_ne_zero_iff.mp (show binaryContent H ≠ 0 from Nat.ne_of_gt hc)
  have hprim : binaryContent Q=1 := by
    have hg := Finset.extract_gcd' (fun e => (H.coeff e).natAbs)
      (fun e => (Q.coeff e).natAbs) hex (fun e _ => by
        have he := congrArg (fun P : SourcePolynomial => P.coeff e) hfactor
        simp only [MvPolynomial.coeff_C_mul] at he
        simpa only [Int.natAbs_mul,Int.natAbs_natCast,c,binaryContent] using congrArg Int.natAbs he)
    simpa only [hs,binaryContent] using hg
  refine ⟨hc,hprim,hfactor,?_⟩
  intro z
  simpa only [map_mul,MvPolynomial.eval_C] using congrArg (MvPolynomial.eval z) hfactor

/-- At an admitted nonzero signed level, content and the reduced absolute
level divide g^ell. This is the corrected route; content need not divide R. -/
theorem admitted_content_level : CF13AdmittedContentLevel := by
  intro H z g ℓ σ hg hσ hlevel
  have hgZ : (g:ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hnonzero : σ*(g:ℤ)^ℓ ≠ 0 := mul_ne_zero hσ0 (pow_ne_zero _ hgZ)
  have hH : H ≠ 0 := by intro h; rw [h,map_zero] at hlevel; exact hnonzero hlevel.symm
  obtain ⟨hc,hprim,hfactor,heval⟩ := binary_content_removal H hH
  let h := MvPolynomial.eval z (binaryPrimitivePart H)
  have heq : (binaryContent H:ℤ)*h=σ*(g:ℤ)^ℓ := (heval z).symm.trans hlevel
  have hh : h ≠ 0 := by intro hz; rw [hz,mul_zero] at heq; exact hnonzero heq.symm
  have habs : binaryContent H*h.natAbs=g^ℓ := by
    have ha := congrArg Int.natAbs heq
    rcases hσ with rfl | rfl <;> simpa [Int.natAbs_mul] using ha
  refine ⟨hc,hprim,hfactor,?_,h,hh,rfl,heq,?_⟩
  · rw [← habs]; exact dvd_mul_right _ _
  · rw [← habs]; exact dvd_mul_left _ _

private theorem integer_value_cast (H : SourcePolynomial) (x y : ℤ) :
    ((MvPolynomial.eval ![x,y] H : ℤ) : ℚ)=polynomialValue H ![(x:ℚ),y] := by
  have h := MvPolynomial.hom_eval₂ H (RingHom.id ℤ) (Int.castRingHom ℚ) (![x,y] : Fin 2 → ℤ)
  change ((MvPolynomial.eval ![x,y] H : ℤ) : ℚ)=
    MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => ((![x,y] : Fin 2 → ℤ) i : ℚ)) H at h
  have he : (fun i => ((![x,y] : Fin 2 → ℤ) i : ℚ))=(![(x:ℚ),y] : Fin 2 → ℚ) := by
    ext i; fin_cases i <;> rfl
  rw [he] at h
  exact h

private theorem homogeneous_value_cast (P : Polynomial ℤ) (r : ℕ) (x y : ℤ)
    (hd : P.natDegree ≤ r) (hy : y ≠ 0) :
    (homogeneousGraphValue P r x y : ℚ)=integerPolynomialValue P ((x:ℚ)/(y:ℚ))*(y:ℚ)^r := by
  exact (integer_value_cast (P.homogenize r) x y).trans
    ((homogeneous_form P r hd).2.1 _ _ (by exact_mod_cast hy))

private theorem graph_values (A B : Polynomial ℤ) (x y v u : ℕ) (hy : 0<y)
    (hbranch : integerPolynomialValue B ((x:ℚ)/y) ≠ 0 ∧
      integerPolynomialValue A ((x:ℚ)/y) ≠ 0 ∧
      (v:ℚ)/(u:ℚ)=integerPolynomialValue A ((x:ℚ)/y)/integerPolynomialValue B ((x:ℚ)/y)) :
    let av := homogeneousGraphValue A (graphDegree A B) x y
    let bv := homogeneousGraphValue B (graphDegree A B) x y
    av ≠ 0 ∧ bv ≠ 0 ∧ (v:ℚ)/(u:ℚ)=(av:ℚ)/(bv:ℚ) := by
  have hyZ : (y:ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hy
  have hyQ : (y:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hy
  have ha := homogeneous_value_cast A (graphDegree A B) x y (le_max_left _ _) hyZ
  have hb := homogeneous_value_cast B (graphDegree A B) x y (le_max_right _ _) hyZ
  simp only [Int.cast_natCast] at ha hb
  have hap : (homogeneousGraphValue A (graphDegree A B) x y : ℚ) ≠ 0 := by
    rw [ha]; exact mul_ne_zero hbranch.2.1 (pow_ne_zero _ hyQ)
  have hbp : (homogeneousGraphValue B (graphDegree A B) x y : ℚ) ≠ 0 := by
    rw [hb]; exact mul_ne_zero hbranch.1 (pow_ne_zero _ hyQ)
  refine ⟨by exact_mod_cast hap,by exact_mod_cast hbp,?_⟩
  rw [ha,hb,mul_div_mul_right _ _ (pow_ne_zero _ hyQ)]
  exact hbranch.2.2

private theorem direct_level_algebra (b d u v a c g σ : ℤ) (hσ : σ=1 ∨ σ = -1)
    (ha : a=σ*g*v) (hc : c=σ*g*u) :
    d^3*a^2-b^3*c^2=g^2*(d^3*v^2-b^3*u^2) := by
  rw [ha,hc]
  rcases hσ with rfl | rfl <;> ring

private theorem inverse_level_algebra (b d u v a c g σ : ℤ) (hσ : σ=1 ∨ σ = -1)
    (ha : a=σ*g*b) (hc : c=σ*g*d) :
    v^2*c^3-u^2*a^3=σ*g^3*(d^3*v^2-b^3*u^2) := by
  rw [ha,hc]
  rcases hσ with rfl | rfl <;> ring

/-- Actual direct parameters recover the unique positive multipliers, with
both graph signs giving the same positive level g squared. -/
theorem direct_source_recovery : CF13DirectSourceRecovery := by
  intro A B n b d u v hs hbranch
  have hbranch' : integerPolynomialValue B ((b:ℚ)/d) ≠ 0 ∧
      integerPolynomialValue A ((b:ℚ)/d) ≠ 0 ∧
      (v:ℚ)/(u:ℚ)=integerPolynomialValue A ((b:ℚ)/d)/integerPolynomialValue B ((b:ℚ)/d) := by
    simpa [sourceGraphBranch,sourcePoint] using hbranch
  obtain ⟨ha0,hb0,he⟩ := graph_values A B b d v u hs.2.1 hbranch'
  let av := homogeneousGraphValue A (graphDegree A B) b d
  let bv := homogeneousGraphValue B (graphDegree A B) b d
  obtain ⟨σ,hσ,hg,ha,hb,hv,hu⟩ := primitive_signed_recovery v u hs.2.2.2.1 hs.2.2.1
    (primitive_ratios n b d u v hs).2.1 av bv ha0 hb0 he
  refine ⟨σ,hσ,hg,hv,hu,?_⟩
  simp only [graphPullback,graphParameter,graphLevelPower,Bool.false_eq_true,ite_false,
    map_sub,map_mul,map_pow,MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,one_mul]
  change (d:ℤ)^3*av^2-(b:ℤ)^3*bv^2=(Int.gcd av bv:ℤ)^2
  have hsource : (d:ℤ)^3*(v:ℤ)^2-(b:ℤ)^3*(u:ℤ)^2=1 := by
    have hh : (d:ℤ)^3*(v:ℤ)^2=(b:ℤ)^3*(u:ℤ)^2+1 := by exact_mod_cast hs.2.2.2.2.2.2.2
    linarith
  calc
    _ = (Int.gcd av bv:ℤ)^2*((d:ℤ)^3*(v:ℤ)^2-(b:ℤ)^3*(u:ℤ)^2) := by
      exact direct_level_algebra _ _ _ _ _ _ _ _ hσ ha hb
    _ = _ := by rw [hsource,mul_one]

/-- Actual inverse parameters recover the positive kernels. The cubed
kernel sign is retained as either +g cubed or -g cubed. -/
theorem inverse_source_recovery : CF13InverseSourceRecovery := by
  intro A B n b d u v hs hbranch
  have hbranch' : integerPolynomialValue B ((v:ℚ)/u) ≠ 0 ∧
      integerPolynomialValue A ((v:ℚ)/u) ≠ 0 ∧
      (b:ℚ)/(d:ℚ)=integerPolynomialValue A ((v:ℚ)/u)/integerPolynomialValue B ((v:ℚ)/u) := by
    simpa [sourceGraphBranch,sourcePoint] using hbranch
  obtain ⟨ha0,hb0,he⟩ := graph_values A B v u b d hs.2.2.1 hbranch'
  let av := homogeneousGraphValue A (graphDegree A B) v u
  let bv := homogeneousGraphValue B (graphDegree A B) v u
  obtain ⟨σ,hσ,hg,ha,hb,hb',hd'⟩ := primitive_signed_recovery b d hs.1 hs.2.1
    (primitive_ratios n b d u v hs).1 av bv ha0 hb0 he
  refine ⟨σ,hσ,hg,hb',hd',?_⟩
  simp only [graphPullback,graphParameter,graphLevelPower,ite_true,
    map_sub,map_mul,map_pow,MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  change (v:ℤ)^2*bv^3-(u:ℤ)^2*av^3=σ*(Int.gcd av bv:ℤ)^3
  have hsource : (d:ℤ)^3*(v:ℤ)^2-(b:ℤ)^3*(u:ℤ)^2=1 := by
    have hh : (d:ℤ)^3*(v:ℤ)^2=(b:ℤ)^3*(u:ℤ)^2+1 := by exact_mod_cast hs.2.2.2.2.2.2.2
    linarith
  calc
    _ = σ*(Int.gcd av bv:ℤ)^3*((d:ℤ)^3*(v:ℤ)^2-(b:ℤ)^3*(u:ℤ)^2) := by
      exact inverse_level_algebra _ _ _ _ _ _ _ _ hσ ha hb
    _ = _ := by rw [hsource,mul_one]

/-- Compose actual signed recovery with the full resultant and admitted
content removal. All graph and primitive polynomials are defined once. -/
theorem actual_source_resultant_level : CF13ActualSourceResultantLevel := by
  intro X D A B hX hd hr
  obtain ⟨hR,hbound,hgcd⟩ := actual_mixed_resultant X D A B hX hd hr
  refine ⟨hR,hbound,?_⟩
  intro inverse n b d u v hs hbranch
  have hprimitive : IsCoprime (graphParameter inverse b d u v 0) (graphParameter inverse b d u v 1) := by
    cases inverse
    · simpa [graphParameter] using (primitive_ratios n b d u v hs).1.isCoprime
    · simpa [graphParameter] using (primitive_ratios n b d u v hs).2.1.isCoprime
  have hdiv : sourceGraphGCD inverse A B b d u v ∣ (fullGraphResultant A B).natAbs :=
    Int.natCast_dvd.mp (hgcd _ _ hprimitive)
  have hrec : signedGraphRecovery inverse A B b d u v := by
    cases inverse
    · exact direct_source_recovery A B n b d u v hs hbranch
    · exact inverse_source_recovery A B n b d u v hs hbranch
  refine ⟨hdiv,hrec,?_⟩
  obtain ⟨σ,hσ,hg,hnum,hden,hlevel⟩ := hrec
  have hsign : (if inverse then σ else (1:ℤ))=1 ∨ (if inverse then σ else (1:ℤ)) = -1 := by
    cases inverse
    · exact Or.inl rfl
    · exact hσ
  obtain ⟨hc,hprim,hfactor,hcdiv,h,hh,hval,heq,hhdiv⟩ := admitted_content_level
    (graphPullback inverse A B) (graphParameter inverse b d u v)
    (sourceGraphGCD inverse A B b d u v) (graphLevelPower inverse)
    (if inverse then σ else 1) hg hsign hlevel
  exact ⟨hc,hprim,hfactor,hcdiv,h,hh,hval,heq.trans hlevel.symm,hhdiv⟩

/-- Entire actual rounded classes retain all rulings and constants; each
mixed graph has one nonzero resultant and one content polynomial before all
source-dependent gcds, signs and admitted reduced levels. -/
theorem rounded_class_resultant_levels : CF13RoundedClassResultantLevels := by
  intro δ hδ hδ1
  obtain ⟨X₀,hX₀,hclass⟩ := rounded_class_graph_rulings δ hδ hδ1
  refine ⟨X₀,hX₀,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  obtain ⟨D,A,C,hd,hcard,hpoints⟩ := hclass X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  refine ⟨D,A,C,hd,hcard,hpoints,?_⟩
  by_cases hdeg : graphDegree A C=0
  · exact Or.inl hdeg
  · right
    obtain ⟨hR,hbound,hactual⟩ := actual_source_resultant_level X D A C
      (hX₀.trans hX) hd (by omega)
    refine ⟨hR,hbound,?_⟩
    intro i
    have hpoint := hpoints i
    rcases hpoint with hroot | hbranch
    · exact Or.inl hroot
    · exact Or.inr (hactual (selectedRealChart ψ) (n i) (b i) (d i) (u i) (v i) (hs i) hbranch)

end
end P0365Subquarter
