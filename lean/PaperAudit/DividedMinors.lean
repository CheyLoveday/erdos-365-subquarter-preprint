import PaperProofs.DividedMinors

namespace P0365Subquarter
set_option pp.all true
#print realRootOrder
#print realRootPartnerOrder
#print rootSmoothRow
#print rootErrorRow
#print rootNormalizedRow
#print realIntervalScale
#print realIntervalNode
#print actualDirectInterval
#print actualRealBox
#print realBoxScale
#print realErrorSum
#print selectedRealChart
#print CF11MixedRootDeterminants
#print CF11NormalizedDeterminantBound
#print CF11ActualIntervalNodes
#print CF11ActualBoxDeterminantBound
#print CF11RoundedActualDeterminantBound
#print CF11RoundedActualMinorVanishing
#check (mixed_root_determinants : CF11MixedRootDeterminants)
#check (normalized_determinant_bound : CF11NormalizedDeterminantBound)
#check (actual_interval_nodes : CF11ActualIntervalNodes)
#check (actual_box_determinant_bound : CF11ActualBoxDeterminantBound)
#check (rounded_actual_determinant_bound : CF11RoundedActualDeterminantBound)
#check (rounded_actual_minor_vanishing : CF11RoundedActualMinorVanishing)
#print axioms mixed_root_determinants
#print axioms normalized_determinant_bound
#print axioms actual_interval_nodes
#print axioms actual_box_determinant_bound
#print axioms rounded_actual_determinant_bound
#print axioms rounded_actual_minor_vanishing
set_option pp.all false
-- Full typechecked applications at the independently frozen targets.
example : CF11MixedRootDeterminants := by
  obtain ⟨C,hC,h⟩ := mixed_root_determinants
  refine ⟨C,hC,?_⟩
  intro inverse S w t ht hw hdist
  exact h inverse S w t ht hw hdist
example : CF11NormalizedDeterminantBound := by
  obtain ⟨C,hC,h⟩ := normalized_determinant_bound
  refine ⟨C,hC,?_⟩
  intro inverse X M w β hX hM hw hdist hβ
  exact h inverse X M w β hX hM hw hdist hβ
example : CF11ActualIntervalNodes := by
  intro n b d u v hs X M a hX hn hM hMX ha hint inverse
  exact actual_interval_nodes n b d u v hs X M a hX hn hM hMX ha hint inverse
example : CF11ActualBoxDeterminantBound := by
  obtain ⟨C,hC,h⟩ := actual_box_determinant_bound
  refine ⟨C,hC,?_⟩
  intro X M B E a hX hM hMX hB hE ha n b d u v hs hb hi inverse
  exact h X M B E a hX hM hMX hB hE ha n b d u v hs hb hi inverse
example : CF11RoundedActualDeterminantBound := by
  obtain ⟨C,hC,h⟩ := rounded_actual_determinant_bound
  refine ⟨C,hC,?_⟩
  intro X ψ δ B E a hX hψ0 hψ2 hδ hδ1 hB hE ha hBE n b d u v hs hb hi
  exact h X ψ δ B E a hX hψ0 hψ2 hδ hδ1 hB hE ha hBE n b d u v hs hb hi
example : CF11RoundedActualMinorVanishing := by
  intro δ hδ hδ1
  obtain ⟨X₀,hX₀,h⟩ := rounded_actual_minor_vanishing δ hδ hδ1
  refine ⟨X₀,hX₀,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p n b d u v hp hscale hs hb hi hc hg hr
  exact h X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p n b d u v hp hscale hs hb hi hc hg hr

-- Exact transformed columns, including both chart exponents.
example (w : ℝ) : rootSmoothRow false w = ![1,w^2,w^4,w^6,w^3,w^5,w^7,w^9] := by
  ext j; fin_cases j <;> norm_num [rootSmoothRow,realRootOrder,realRootPartnerOrder] <;> ring
example (w : ℝ) : rootSmoothRow true w = ![1,w^3,w^6,w^9,w^2,w^5,w^8,w^11] := by
  ext j; fin_cases j <;> norm_num [rootSmoothRow,realRootOrder,realRootPartnerOrder] <;> ring
example (w : ℝ) : rootErrorRow false w = ![0,0,0,0,1,w^2,w^4,w^6] := by
  ext j; fin_cases j <;> norm_num [rootErrorRow,realRootOrder]
example (w : ℝ) : rootErrorRow true w = ![0,0,0,0,1,w^3,w^6,w^9] := by
  ext j; fin_cases j <;> norm_num [rootErrorRow,realRootOrder]

-- Five error rows vanish even at distinct nodes within the root cube.
example (inverse : Bool) : Matrix.det (fun i j =>
    if i ∈ ({0,1,2,3,4} : Finset (Fin 8)) then
      rootErrorRow inverse (1+(i.val:ℝ)/8) j
    else rootSmoothRow inverse (1+(i.val:ℝ)/8) j) = 0 := by
  obtain ⟨C,hC,h⟩ := mixed_root_determinants
  have hw (i : Fin 8) : 1 ≤ 1+(i.val:ℝ)/8 ∧ 1+(i.val:ℝ)/8 ≤ 2 := by
    have hi : (i.val:ℝ) < 8 := by exact_mod_cast i.isLt
    constructor <;> (try positivity) <;> linarith
  exact (h inverse {0,1,2,3,4} (fun i => 1+(i.val:ℝ)/8) 1 (by norm_num) hw
    (by intro i j; apply abs_le.2; constructor <;> linarith [(hw i).1,(hw i).2,(hw j).1,(hw j).2])).1 (by decide)

-- Zero diameter includes duplicate nodes, without dividing by differences.
example (inverse : Bool) : Matrix.det (fun _i : Fin 8 => rootSmoothRow inverse (1:ℝ)) = 0 := by
  obtain ⟨C,hC,h⟩ := mixed_root_determinants
  have hh := (h inverse ∅ (fun _ => 1) 0 (by norm_num)
    (by intro i; norm_num) (by intro i j; norm_num)).2 0 (by simp)
  norm_num [profileErrorWeight] at hh
  exact hh

private theorem source_eight : PairSource 8 2 1 1 3 := by
  norm_num [PairSource]
  exact Nat.prime_two.squarefree

-- Important inverse-chart control: normalized t may exceed2, while its
-- cube-root node and derived beta still satisfy the required uniform bounds.
example : 2 < realSourceCoordinate true 2 1 1 3 / realIntervalScale true 1 := by
  norm_num [realSourceCoordinate,realIntervalScale]
example (inverse : Bool) : 1 ≤ realIntervalNode inverse 1 2 1 1 3 ∧
    realIntervalNode inverse 1 2 1 1 3 ≤ 2 ∧
    realIntervalNode inverse 1 2 1 1 3 ≤ 1+3/(1:ℝ) ∧
    |realNormalizedError inverse (realIntervalScale inverse 1) 2 1 1 3| ≤ 8/(1:ℝ) := by
  have hh := actual_interval_nodes 8 2 1 1 3 source_eight 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [actualDirectInterval]) inverse
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

-- Genuine shell and interval upper endpoints, kernel/multiplier one, both
-- original integer matrices. C is the fixed theorem constant, not an input.
example : ∃ C : ℝ, 0<C ∧ ∀ inverse : Bool,
    |(Matrix.det (fun _i : Fin 8 => fun j => sourceIntegerRow inverse 2 1 1 3 j) : ℝ)| ≤
      C*realBoxScale inverse 4 1 1*realErrorSum 4 1 := by
  obtain ⟨C,hC,h⟩ := actual_box_determinant_bound
  refine ⟨C,hC,?_⟩
  intro inverse
  apply h 4 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => 8) (fun _ => 2)
    (fun _ => 1) (fun _ => 1) (fun _ => 3)
  · intro i; exact source_eight
  · intro i; norm_num [actualRealBox]
  · intro i; norm_num [actualDirectInterval]

example : selectedRealChart (2/5) = false ∧ selectedRealChart (1/2) = true := by
  norm_num [selectedRealChart,profileCentre]

end P0365Subquarter
