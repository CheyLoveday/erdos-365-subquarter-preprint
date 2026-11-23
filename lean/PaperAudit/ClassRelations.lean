import PaperProofs.ClassRelations

namespace P0365Subquarter
set_option pp.all true
#print relationExponent
#print relationPolynomial
#print boundedSourceRelation
#print CF12BoundedIntegerRelation
#print CF12SourceRowHeight
#print CF12RelationPolynomial
#print CF12SourceRelationEvaluation
#print CF12ActualClassRelation
#print CF12RoundedEntireClassRelation
#check (bounded_integer_relation : CF12BoundedIntegerRelation)
#check (source_row_height : CF12SourceRowHeight)
#check (relation_polynomial : CF12RelationPolynomial)
#check (source_relation_evaluation : CF12SourceRelationEvaluation)
#check (actual_class_relation : CF12ActualClassRelation)
#check (rounded_entire_class_relation : CF12RoundedEntireClassRelation)
#print axioms bounded_integer_relation
#print axioms source_row_height
#print axioms relation_polynomial
#print axioms source_relation_evaluation
#print axioms actual_class_relation
#print axioms rounded_entire_class_relation
set_option pp.all false

-- Complete applications at all six frozen targets.
example : CF12BoundedIntegerRelation := by
  intro ι A H hH hA hzero
  obtain ⟨c,hc,hbound,hrel⟩ := bounded_integer_relation ι A H hH hA hzero
  exact ⟨c,hc,hbound,hrel⟩
example : CF12SourceRowHeight := by
  intro X hX n b d u v hs hn inverse j
  exact source_row_height X hX n b d u v hs hn inverse j
example : CF12RelationPolynomial := by
  intro inverse c
  have h := relation_polynomial inverse c
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun z => h.2.2.2.2 z⟩
example : CF12SourceRelationEvaluation := by
  intro n b d u v hs inverse c
  exact source_relation_evaluation n b d u v hs inverse c
example : CF12ActualClassRelation := by
  obtain ⟨X₀,hX₀,h⟩ := actual_class_relation
  refine ⟨X₀,hX₀,?_⟩
  intro X hX ι n b d u v hs hn inverse hzero
  exact h X hX ι n b d u v hs hn inverse hzero
example : CF12RoundedEntireClassRelation := by
  intro δ hδ hδ1
  obtain ⟨X₀,hX₀,h⟩ := rounded_entire_class_relation δ hδ hδ1
  refine ⟨X₀,hX₀,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  exact h X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz

-- Empty row type: no choice of an unavailable source or class centre.
example : ∃ c : Fin 8 → ℤ, c ≠ 0 ∧ (∀ j, |(c j : ℝ)| ≤ 5040) ∧
    ∀ i : Fin 0, ∑ j : Fin 8, (Fin.elim0 i : ℤ)*c j = 0 := by
  simpa using bounded_integer_relation (Fin 0) (fun i _ => Fin.elim0 i) 1
    (by norm_num) (by intro i; exact Fin.elim0 i)
    (by intro f; exact Fin.elim0 (f 0))

-- Rank zero is a genuine lower-rank obstruction to using the full adjugate.
example : Matrix.adjugate (0 : Matrix (Fin 8) (Fin 8) ℤ) = 0 := Matrix.adjugate_zero
example : ∃ c : Fin 8 → ℤ, c ≠ 0 ∧ (∀ j, |(c j : ℝ)| ≤ 5040) ∧
    ∀ i : Fin 3, ∑ j : Fin 8, (0:ℤ)*c j = 0 := by
  simpa using bounded_integer_relation (Fin 3) (fun _ _ => 0) 1
    (by norm_num) (by norm_num) (by intro f; exact Matrix.det_zero)

-- Seven independent coordinate rows, fewer than eight sources.
private def sevenRows (i : Fin 7) : Fin 8 → ℤ := Pi.single i.castSucc 1
example : Matrix.det (fun i j : Fin 7 => sevenRows i j.castSucc) = 1 := by
  have he : Matrix.of (fun i j : Fin 7 => sevenRows i j.castSucc) = 1 := by
    ext i j
    simp [sevenRows,Pi.single_apply,Matrix.one_apply,eq_comm]
  change Matrix.det (Matrix.of (fun i j : Fin 7 => sevenRows i j.castSucc)) = 1
  rw [he,Matrix.det_one]
example : ∃ c : Fin 8 → ℤ, c ≠ 0 ∧ (∀ j, |(c j : ℝ)| ≤ 5040) ∧
    ∀ i : Fin 7, ∑ j : Fin 8, sevenRows i j*c j = 0 := by
  have hb : ∀ i j, |(sevenRows i j : ℝ)| ≤ 1 := by
    intro i j
    simp only [sevenRows,Pi.single_apply]
    split_ifs <;> norm_num
  have hz : ∀ f : Fin 8 → Fin 7, Matrix.det (fun i j => sevenRows (f i) j) = 0 := by
    intro f
    have hf := Fintype.not_injective_of_card_lt f (by decide)
    simp only [Function.Injective] at hf
    push_neg at hf
    obtain ⟨i,j,he,hne⟩ := hf
    exact Matrix.det_zero_of_row_eq hne (by rw [he])
  simpa using bounded_integer_relation (Fin 7) sevenRows 1 (by norm_num) hb hz

-- Full rank is excluded by an actual nonzero eight-minor.
example : Matrix.det (1 : Matrix (Fin 8) (Fin 8) ℤ) ≠ 0 := by simp

-- Exact degree-three column in both orientations and its rational value.
example (inverse : Bool) :
    (relationPolynomial inverse (Pi.single 7 1)).coeff (relationExponent inverse 7) = 1 := by
  rw [(relation_polynomial inverse _).1]
  simp
example : polynomialValue (relationPolynomial false (Pi.single 7 1)) (![2,3] : Fin 2 → ℚ) = 24 ∧
    polynomialValue (relationPolynomial true (Pi.single 7 1)) (![2,3] : Fin 2 → ℚ) = 54 := by
  constructor <;> rw [(relation_polynomial _ _).2.2.2.2] <;>
    norm_num [Fin.sum_univ_succ,chartMonomial,Pi.single_apply]

private theorem relation_source_eight : PairSource 8 2 1 1 3 := by
  norm_num [PairSource]
  exact Nat.prime_two.squarefree

-- Genuine original integer entries and shell endpoint in both charts.
example : sourceIntegerRow false 2 1 1 3 7 = 24 ∧
    sourceIntegerRow true 2 1 1 3 7 = 54 := by norm_num [sourceIntegerRow]
example (inverse : Bool) (j : Fin 8) :
    |(sourceIntegerRow inverse 2 1 1 3 j : ℝ)| ≤ 9*(4:ℝ)^(11/6:ℝ) :=
  source_row_height 4 (by norm_num) 8 2 1 1 3 relation_source_eight (by norm_num) inverse j

-- A single actual source has one nonzero bounded polynomial for its entire
-- class. This cannot be obtained by selecting eight distinct sources.
example (inverse : Bool) : ∃ X : ℝ, 4 ≤ X ∧ ∃ G : SourcePolynomial,
    boundedSourceRelation inverse X G ∧ polynomialValue G (sourcePoint 2 1 1 3) = 0 := by
  obtain ⟨X₀,hX₀,h⟩ := actual_class_relation
  refine ⟨X₀,hX₀,?_⟩
  obtain ⟨G,hG,hval⟩ := h X₀ le_rfl (Fin 1) (fun _ => 8) (fun _ => 2)
    (fun _ => 1) (fun _ => 1) (fun _ => 3) (fun _ => relation_source_eight)
    (by intro i; norm_num; linarith) inverse
    (by intro f; exact Matrix.det_zero_of_row_eq (by decide : (0:Fin 8) ≠ 1) rfl)
  exact ⟨G,hG,hval 0⟩

end P0365Subquarter
