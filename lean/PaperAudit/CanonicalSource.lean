import PaperProofs.CanonicalSource

/-! Ordinary native development readback, not a protected-comparator or release
receipt. Every checked theorem is applied to its independently frozen type.
Actual historical-declaration adapters and all later CFs remain separate. -/

namespace P0365Subquarter

set_option pp.all true

#print Powerful
#print PairSource
#print PairCount
#print SourceRatios

#check (normal_form : CF01NormalForm)
#check (normal_form_unique : CF01NormalFormUnique)
#check (cube_square_powerful : CF01CubeSquarePowerful)
#check (pair_source_equivalence : CF01PairSourceEquivalence)
#check (pair_source_unique : CF01PairSourceUnique)
#check (additive_and_integer_source : CF01AdditiveAndIntegerSource)
#check (cross_endpoint_coprime : CF01CrossEndpointCoprime)
#check (primitive_ratios : CF01PrimitiveRatios)
#check (source_bounds : CF01SourceBounds)
#check (cutoff_source_bounds : CF01CutoffSourceBounds)
#check (source_ratio_injection : CF01SourceRatioInjection)
#check (source_ratio_coordinate_injection : CF01SourceRatioCoordinateInjection)
#check (readback_prime_correspondence : CF01ReadbackPrimeCorrespondence)
#check (readback_powerful_correspondence : CF01ReadbackPowerfulCorrespondence)
#check (readback_source_correspondence : CF01ReadbackSourceCorrespondence)
#check (readback_count_correspondence : CF01ReadbackCountCorrespondence)
#check (count_source_correspondence : CF01CountSourceCorrespondence)
#check (count_empty_boundary : CF01CountEmptyBoundary)
#check (endpoint_overlap_controls : CF01EndpointAndOverlapControls)
#check (noncanonical_control : CF01NoncanonicalControl)

#print axioms powerful_normal_form_exists
#print axioms normal_form
#print axioms normal_form_unique
#print axioms cube_square_powerful
#print axioms pair_source_equivalence
#print axioms pair_source_unique
#print axioms additive_and_integer_source
#print axioms cross_endpoint_coprime
#print axioms primitive_ratios
#print axioms source_bounds
#print axioms cutoff_source_bounds
#print axioms source_ratio_injection
#print axioms source_ratio_coordinate_injection
#print axioms readback_prime_correspondence
#print axioms readback_powerful_correspondence
#print axioms readback_source_correspondence
#print axioms readback_count_correspondence
#print axioms count_source_correspondence
#print axioms count_empty_boundary
#print axioms endpoint_overlap_controls
#print axioms noncanonical_control
#print axioms zero_not_powerful
#print axioms one_powerful
#print axioms two_not_powerful

end P0365Subquarter
