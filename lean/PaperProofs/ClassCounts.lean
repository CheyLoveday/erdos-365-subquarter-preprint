import PaperTargets.ClassCounts
import PaperProofs.RulingCounts

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Degree zero fixes the partner coordinate, including both chart choices. -/
theorem constant_graph_ruling : CF15ConstantGraphRuling := by
  intro inverse A B hr b d u v hbranch
  have hA : A=Polynomial.C (A.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero
    (by have := le_max_left A.natDegree B.natDegree; change max A.natDegree B.natDegree=0 at hr; omega)
  have hB : B=Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero
    (by have := le_max_right A.natDegree B.natDegree; change max A.natDegree B.natDegree=0 at hr; omega)
  have hvalue (P : Polynomial ℤ) (hP : P=Polynomial.C (P.coeff 0)) (s : ℚ) :
      integerPolynomialValue P s=integerPolynomialValue P 0 := by
    conv_lhs => rw [hP]
    conv_rhs => rw [hP]
    simp [integerPolynomialValue,rationalPolynomial]
  exact hbranch.2.2.trans (by rw [hvalue A hA,hvalue B hB])

/-- Split only over the actual common-factor roots, then the one fixed graph. -/
theorem bounded_graph_ruling_class_subpower : CF15BoundedGraphRulingClassSubpower := by
  classical
  intro hThue ε hε
  obtain ⟨Cm,hCm,hm⟩ := actual_graph_source_subpower hThue ε hε
  obtain ⟨Cr,hCr,hr⟩ := coordinate_ruling_subpower hThue ε hε
  refine ⟨4*Cr+Cm,by positivity,?_⟩
  intro X D A B hX hdata inverse S hS
  have hpow : 0≤X^ε := Real.rpow_nonneg (by linarith) _
  have hchoose : ∀ n : ℕ, ∃ b d u v : ℕ, n∈S → PairSource n b d u v ∧
      graphRulingCase inverse D A B (sourcePoint b d u v) := by
    intro n
    by_cases hn : n∈S
    · obtain ⟨b,d,u,v,hs,hg⟩ := (hS n hn).2
      exact ⟨b,d,u,v,fun _ => ⟨hs,hg⟩⟩
    · exact ⟨0,0,0,0,fun h => False.elim (hn h)⟩
  choose b d u v hw using hchoose
  let s : ℕ → ℚ := fun n => sourcePoint (b n) (d n) (u n) (v n) (if inverse then 1 else 0)
  let T := rulingRoots D
  let Sr := S.filter (fun n => s n∈T)
  let Sg := S.filter (fun n => s n∉T)
  have hT : T.card≤3 := by
    calc
      _ ≤ (rationalPolynomial D).roots.card := Multiset.toFinset_card_le _
      _ ≤ (rationalPolynomial D).natDegree := Polynomial.card_roots' _
      _ = D.natDegree := Polynomial.natDegree_map_eq_of_injective Int.cast_injective D
      _ ≤ 3 := hdata.2.2.2.1
  have hSr : (Sr.card:ℝ)≤3*Cr*X^ε := by
    have hcard : (Sr.card:ℝ)=∑ q ∈ T, ((Sr.filter (fun n => s n=q)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise (f:=s) (t:=T)
        (fun n hn => (Finset.mem_filter.mp hn).2)
    rw [hcard]
    calc
      _ ≤ ∑ q ∈ T, Cr*X^ε := Finset.sum_le_sum (fun q _ => by
        apply hr X hX (if inverse then 1 else 0) q
        intro n hn
        obtain ⟨hnr,he⟩ := Finset.mem_filter.mp hn
        have hnS := (Finset.mem_filter.mp hnr).1
        exact ⟨(hS n hnS).1,b n,d n,u n,v n,(hw n hnS).1,he⟩)
      _ = (T.card:ℝ)*(Cr*X^ε) := by simp
      _ ≤ 3*(Cr*X^ε) := mul_le_mul_of_nonneg_right (by exact_mod_cast hT) (by positivity)
      _ = _ := by ring
  have hbranch (n : ℕ) (hn : n∈Sg) : sourceGraphBranch inverse A B (b n) (d n) (u n) (v n) := by
    obtain ⟨hnS,hnot⟩ := Finset.mem_filter.mp hn
    exact (hw n hnS).2.resolve_left hnot
  have hSg : (Sg.card:ℝ)≤(Cr+Cm)*X^ε := by
    by_cases hzero : graphDegree A B=0
    · have hbound := hr X hX (if inverse then 0 else 1)
        (integerPolynomialValue A 0/integerPolynomialValue B 0) Sg (by
          intro n hn
          have hnS := (Finset.mem_filter.mp hn).1
          exact ⟨(hS n hnS).1,b n,d n,u n,v n,(hw n hnS).1,
            constant_graph_ruling inverse A B hzero _ _ _ _ (hbranch n hn)⟩)
      exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith) hpow)
    · have hbound := hm X D A B hX hdata (by omega) inverse Sg (by
        intro n hn
        exact ⟨b n,d n,u n,v n,(hw n (Finset.mem_filter.mp hn).1).1,hbranch n hn⟩)
      exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith) hpow)
  have hsplit : Sr.card+Sg.card=S.card := Finset.card_filter_add_card_filter_not (s:=S) (fun n => s n∈T)
  have hsplitR : (S.card:ℝ)=(Sr.card:ℝ)+(Sg.card:ℝ) := by exact_mod_cast hsplit.symm
  rw [hsplitR]
  calc
    _ ≤ 3*Cr*X^ε+(Cr+Cm)*X^ε := add_le_add hSr hSg
    _ = _ := by ring

/-- Apply CF13 to the whole original finite class before doing any counting. -/
theorem rounded_class_source_subpower : CF15RoundedClassSourceSubpower := by
  intro hThue δ hδ hδ1 ε hε
  obtain ⟨C,hC,hcount⟩ := bounded_graph_ruling_class_subpower hThue ε hε
  obtain ⟨X₀,hX₀,hdecomp⟩ := rounded_class_graph_rulings δ hδ hδ1
  refine ⟨X₀,C,hX₀,hC,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ S b d u v hp hscale hs hb hi hf hg hz
  obtain ⟨D,A,Q,hdata,_,hpoints⟩ := hdecomp X ψ B E a hX hψ0 hψ2 hB hE ha hBE
    F p z₀ {n // n∈S} (fun n => n.val) (fun n => b n.val) (fun n => d n.val)
    (fun n => u n.val) (fun n => v n.val) hp hscale
    (fun n => hs n.val n.property) (fun n => hb n.val n.property)
    (fun n => hi n.val n.property) (fun n => hf n.val n.property)
    (fun n => hg n.val n.property) (fun n => hz n.val n.property)
  apply hcount X D A Q (hX₀.trans hX) hdata (selectedRealChart ψ) S
  intro n hn
  exact ⟨(hb n hn).2.1,b n,d n,u n,v n,hs n hn,hpoints ⟨n,hn⟩⟩

end
end P0365Subquarter
