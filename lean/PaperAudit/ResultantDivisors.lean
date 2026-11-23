import PaperProofs.ResultantDivisors

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print divisorCount
#print primeSupportCount
#print thueDivisorInventory
#print CF15DivisorCardMul
#print CF15DivisorCardPow
#print CF15DivisorCardDvd
#print CF15PrimeSupportLevel
#print CF15SupportDivisorLower
#print CF15ResultantLevelCharges
#print CF15ThueDivisorInventory
#print CF15ActualGraphDivisorInventory
#check (divisor_card_mul : CF15DivisorCardMul)
#check (divisor_card_pow : CF15DivisorCardPow)
#check (divisor_card_dvd : CF15DivisorCardDvd)
#check (prime_support_level : CF15PrimeSupportLevel)
#check (support_divisor_lower : CF15SupportDivisorLower)
#check (resultant_level_charges : CF15ResultantLevelCharges)
#check (thue_divisor_inventory : CF15ThueDivisorInventory)
#check (actual_graph_divisor_inventory : CF15ActualGraphDivisorInventory)
#print axioms divisor_card_mul
#print axioms divisor_card_pow
#print axioms divisor_card_dvd
#print axioms prime_support_level
#print axioms support_divisor_lower
#print axioms resultant_level_charges
#print axioms thue_divisor_inventory
#print axioms actual_graph_divisor_inventory
set_option pp.all false

-- Complete applications preserve all binders, including zero exponents.
example : CF15DivisorCardMul := by
  intro m n
  exact divisor_card_mul m n
example : CF15DivisorCardPow := by
  intro n k
  exact divisor_card_pow n k
example : CF15DivisorCardDvd := by
  intro m n hn hd
  exact divisor_card_dvd m n hn hd
example : CF15PrimeSupportLevel := by
  intro R g h ℓ hR hg hh
  exact prime_support_level R g h ℓ hR hg hh
example : CF15SupportDivisorLower := by
  intro R hR
  exact support_divisor_lower R hR
example : CF15ResultantLevelCharges := by
  intro R g h ℓ hR hg hh he
  exact resultant_level_charges R g h ℓ hR hg hh he
example : CF15ThueDivisorInventory := by
  intro R ℓ d hR he hd
  exact thue_divisor_inventory R ℓ d hR he hd
example : CF15ActualGraphDivisorInventory := by
  intro X D A B hX hgraph hr
  exact actual_graph_divisor_inventory X D A B hX hgraph hr

-- The nonzero upper modulus guard cannot be removed from monotonicity.
example : (1:ℕ) ∣ 0 ∧ ¬ divisorCount 1 ≤ divisorCount 0 := by
  norm_num [divisorCount]
-- Exponent0 and 0^0=1 are included in the elementary inequalities.
example : divisorCount ((0:ℕ)^0) ≤ (divisorCount 0)^0 := divisor_card_pow 0 0
example : divisorCount (0*7) ≤ divisorCount 0*divisorCount 7 := divisor_card_mul 0 7
-- Unit resultant, empty prime support and degree0 all remain legal.
example : thueDivisorInventory 1 0 0 ≤ (divisorCount 1)^8 :=
  thue_divisor_inventory 1 0 0 (by decide) (by decide) (by decide)
example : primeSupportCount 1=0 ∧ divisorCount 1=1 := by simp [primeSupportCount,divisorCount]
-- A genuine power divisor need not divide the resultant. Dropping this case
-- would lose actual inverse-graph levels. Transfer uses prime support only.
example : (2:ℕ) ∣ 4 ∧ (8:ℕ) ∣ 2^3 ∧ ¬ (8:ℕ) ∣ 4 := by norm_num
example : (8:ℕ).primeFactors ⊆ (4:ℕ).primeFactors :=
  (prime_support_level 4 2 8 3 (by decide) (by norm_num) (by norm_num)).2.2
example : divisorCount 8 ≤ (divisorCount 4)^3 ∧
    (∀ d : ℕ, d ≤ 11 → d^(primeSupportCount 8) ≤ (divisorCount 4)^4) ∧
    16*(divisorCount 8)^2 ≤ 16*(divisorCount 4)^6 :=
  resultant_level_charges 4 2 8 3 (by decide) (by norm_num) (by norm_num) (by decide)
example : thueDivisorInventory 4 3 11 ≤ (divisorCount 4)^8 :=
  thue_divisor_inventory 4 3 11 (by decide) (by decide) (by decide)
-- The lower divisor bound at0 is false: prime support0 is empty, tau0=0.
example : ¬ 2^(primeSupportCount 0) ≤ divisorCount 0 := by simp [primeSupportCount,divisorCount]

end
end P0365Subquarter
