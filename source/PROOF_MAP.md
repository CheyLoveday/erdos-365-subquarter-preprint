# Manuscript and Lean proof map

The [proof notes](../PROOF_NOTES.md) explain the argument. The tables trace each step to the article and the checked Lean source. Edges express mathematical prerequisites at the step level. The Lean links open the implementing declarations and their named contracts.

> Generated reading copy. Its source is [PROOF_MAP.json](PROOF_MAP.json), exported from `research/papers/p0365-subquarter-v1/manuscript/PROOF_MAP.json` with upstream SHA-256 `235415abfb1fa303b026d8adbc2638204b807e2c64950d86467bc7b742fa2baa`. The public data SHA-256 is `7ade37099a672797d4a2bec5fa4071a2a9ff65bb0dc96b7624de1b22518f3182`. Regenerate with `python3 -B render.py`.

## Forward map and dependencies

| Proof step | Article source | Inputs | Used by |
| --- | --- | --- | --- |
| [LP00](../PROOF_NOTES.md#lp00) · Accepted published Stewart bound | [§9](MANUSCRIPT.md#9-resultants-admitted-levels-and-the-precise-stewart-input) | — | [LP03](../PROOF_NOTES.md#lp03), [LP17](../PROOF_NOTES.md#lp17) |
| [LP01](../PROOF_NOTES.md#lp01) · Canonical original sources and injection | [§1](MANUSCRIPT.md#1-counting-function-and-conclusion), [§2](MANUSCRIPT.md#2-canonical-sources-and-injection) | — | [LP02](../PROOF_NOTES.md#lp02), [LP03](../PROOF_NOTES.md#lp03), [LP04](../PROOF_NOTES.md#lp04), [LP06](../PROOF_NOTES.md#lp06), [LP09](../PROOF_NOTES.md#lp09), [LP12](../PROOF_NOTES.md#lp12), [LP22](../PROOF_NOTES.md#lp22), [LP23](../PROOF_NOTES.md#lp23) |
| [LP02](../PROOF_NOTES.md#lp02) · Fixed kernel fibres and complement | [§3](MANUSCRIPT.md#3-fixed-fibres-complements-and-actual-boxes) | [LP01](../PROOF_NOTES.md#lp01) | [LP03](../PROOF_NOTES.md#lp03), [LP14](../PROOF_NOTES.md#lp14), [LP21](../PROOF_NOTES.md#lp21) |
| [LP03](../PROOF_NOTES.md#lp03) · Fixed multiplier fibres and complement | [§3](MANUSCRIPT.md#3-fixed-fibres-complements-and-actual-boxes) | [LP00](../PROOF_NOTES.md#lp00), [LP01](../PROOF_NOTES.md#lp01), [LP02](../PROOF_NOTES.md#lp02) | [LP14](../PROOF_NOTES.md#lp14), [LP21](../PROOF_NOTES.md#lp21) |
| [LP04](../PROOF_NOTES.md#lp04) · Actual boxes and residual compact profile | [§3](MANUSCRIPT.md#3-fixed-fibres-complements-and-actual-boxes) | [LP01](../PROOF_NOTES.md#lp01) | [LP07](../PROOF_NOTES.md#lp07), [LP20](../PROOF_NOTES.md#lp20), [LP21](../PROOF_NOTES.md#lp21) |
| [LP05](../PROOF_NOTES.md#lp05) · Continuous numerical envelope and rounding | [§10](MANUSCRIPT.md#10-profile-optimization-and-rounded-determinant-comparison) | — | [LP06](../PROOF_NOTES.md#lp06), [LP07](../PROOF_NOTES.md#lp07), [LP10](../PROOF_NOTES.md#lp10), [LP13](../PROOF_NOTES.md#lp13), [LP20](../PROOF_NOTES.md#lp20) |
| [LP06](../PROOF_NOTES.md#lp06) · One original closed interval cover | [§4](MANUSCRIPT.md#4-internal-finite-source-coarse-polynomials) | [LP01](../PROOF_NOTES.md#lp01), [LP05](../PROOF_NOTES.md#lp05) | [LP07](../PROOF_NOTES.md#lp07), [LP12](../PROOF_NOTES.md#lp12), [LP20](../PROOF_NOTES.md#lp20) |
| [LP07](../PROOF_NOTES.md#lp07) · Uniform rectangular integer minors | [§4](MANUSCRIPT.md#4-internal-finite-source-coarse-polynomials) | [LP04](../PROOF_NOTES.md#lp04), [LP05](../PROOF_NOTES.md#lp05), [LP06](../PROOF_NOTES.md#lp06) | [LP08](../PROOF_NOTES.md#lp08) |
| [LP08](../PROOF_NOTES.md#lp08) · All-rank coarse polynomial producer | [§4](MANUSCRIPT.md#4-internal-finite-source-coarse-polynomials) | [LP07](../PROOF_NOTES.md#lp07) | [LP09](../PROOF_NOTES.md#lp09), [LP20](../PROOF_NOTES.md#lp20) |
| [LP09](../PROOF_NOTES.md#lp09) · Factors, heights and singular sources | [§4](MANUSCRIPT.md#4-internal-finite-source-coarse-polynomials) | [LP01](../PROOF_NOTES.md#lp01), [LP08](../PROOF_NOTES.md#lp08) | [LP10](../PROOF_NOTES.md#lp10), [LP20](../PROOF_NOTES.md#lp20) |
| [LP10](../PROOF_NOTES.md#lp10) · Source-wise good primes and common classes | [§5](MANUSCRIPT.md#5-a-source-wise-bounded-union-of-good-primes) | [LP05](../PROOF_NOTES.md#lp05), [LP09](../PROOF_NOTES.md#lp09) | [LP11](../PROOF_NOTES.md#lp11), [LP20](../PROOF_NOTES.md#lp20) |
| [LP11](../PROOF_NOTES.md#lp11) · Finite implicit expansion and modular minor | [§6](MANUSCRIPT.md#6-the-same-integer-minor-in-two-estimates) | [LP10](../PROOF_NOTES.md#lp10) | [LP13](../PROOF_NOTES.md#lp13) |
| [LP12](../PROOF_NOTES.md#lp12) · Real estimate of the same original minor | [§6](MANUSCRIPT.md#6-the-same-integer-minor-in-two-estimates) | [LP01](../PROOF_NOTES.md#lp01), [LP06](../PROOF_NOTES.md#lp06) | [LP13](../PROOF_NOTES.md#lp13) |
| [LP13](../PROOF_NOTES.md#lp13) · Zero minors and one entire-class relation | [§7](MANUSCRIPT.md#7-one-bounded-relation-for-the-entire-class) | [LP05](../PROOF_NOTES.md#lp05), [LP11](../PROOF_NOTES.md#lp11), [LP12](../PROOF_NOTES.md#lp12) | [LP14](../PROOF_NOTES.md#lp14) |
| [LP14](../PROOF_NOTES.md#lp14) · Every graph and ruling branch | [§8](MANUSCRIPT.md#8-count-every-class-through-its-graph-and-rulings) | [LP02](../PROOF_NOTES.md#lp02), [LP03](../PROOF_NOTES.md#lp03), [LP13](../PROOF_NOTES.md#lp13) | [LP15](../PROOF_NOTES.md#lp15), [LP19](../PROOF_NOTES.md#lp19) |
| [LP15](../PROOF_NOTES.md#lp15) · Full resultants, signed recovery and fixed content | [§9](MANUSCRIPT.md#9-resultants-admitted-levels-and-the-precise-stewart-input) | [LP14](../PROOF_NOTES.md#lp14) | [LP16](../PROOF_NOTES.md#lp16), [LP18](../PROOF_NOTES.md#lp18) |
| [LP16](../PROOF_NOTES.md#lp16) · Axes, nonpowers and exhaustive factor dispatch | [§9](MANUSCRIPT.md#9-resultants-admitted-levels-and-the-precise-stewart-input) | [LP15](../PROOF_NOTES.md#lp15) | [LP17](../PROOF_NOTES.md#lp17) |
| [LP17](../PROOF_NOTES.md#lp17) · High- and low-degree signed level bounds | [§9](MANUSCRIPT.md#9-resultants-admitted-levels-and-the-precise-stewart-input) | [LP00](../PROOF_NOTES.md#lp00), [LP16](../PROOF_NOTES.md#lp16) | [LP18](../PROOF_NOTES.md#lp18) |
| [LP18](../PROOF_NOTES.md#lp18) · Divisor inventory and injection to original starts | [§9](MANUSCRIPT.md#9-resultants-admitted-levels-and-the-precise-stewart-input) | [LP15](../PROOF_NOTES.md#lp15), [LP17](../PROOF_NOTES.md#lp17) | [LP19](../PROOF_NOTES.md#lp19) |
| [LP19](../PROOF_NOTES.md#lp19) · Every smooth class count | [§8](MANUSCRIPT.md#8-count-every-class-through-its-graph-and-rulings), [§9](MANUSCRIPT.md#9-resultants-admitted-levels-and-the-precise-stewart-input) | [LP14](../PROOF_NOTES.md#lp14), [LP18](../PROOF_NOTES.md#lp18) | [LP20](../PROOF_NOTES.md#lp20) |
| [LP20](../PROOF_NOTES.md#lp20) · Interval and residual box aggregation | [§11](MANUSCRIPT.md#11-conservative-interval-and-box-inventory) | [LP04](../PROOF_NOTES.md#lp04), [LP05](../PROOF_NOTES.md#lp05), [LP06](../PROOF_NOTES.md#lp06), [LP08](../PROOF_NOTES.md#lp08), [LP09](../PROOF_NOTES.md#lp09), [LP10](../PROOF_NOTES.md#lp10), [LP19](../PROOF_NOTES.md#lp19) | [LP21](../PROOF_NOTES.md#lp21) |
| [LP21](../PROOF_NOTES.md#lp21) · Complete original box count | [§11](MANUSCRIPT.md#11-conservative-interval-and-box-inventory) | [LP02](../PROOF_NOTES.md#lp02), [LP03](../PROOF_NOTES.md#lp03), [LP04](../PROOF_NOTES.md#lp04), [LP20](../PROOF_NOTES.md#lp20) | [LP22](../PROOF_NOTES.md#lp22) |
| [LP22](../PROOF_NOTES.md#lp22) · Original shell count | [§12](MANUSCRIPT.md#12-boxes-shells-finite-head-and-real-cutoff) | [LP01](../PROOF_NOTES.md#lp01), [LP21](../PROOF_NOTES.md#lp21) | [LP23](../PROOF_NOTES.md#lp23) |
| [LP23](../PROOF_NOTES.md#lp23) · All natural starts and the finite head | [§12](MANUSCRIPT.md#12-boxes-shells-finite-head-and-real-cutoff) | [LP01](../PROOF_NOTES.md#lp01), [LP22](../PROOF_NOTES.md#lp22) | [LP24](../PROOF_NOTES.md#lp24) |
| [LP24](../PROOF_NOTES.md#lp24) · Real cutoff with the same constant | [§1](MANUSCRIPT.md#1-counting-function-and-conclusion), [§12](MANUSCRIPT.md#12-boxes-shells-finite-head-and-real-cutoff) | [LP23](../PROOF_NOTES.md#lp23) | — |

## Reverse declaration index

Definitions specify objects and contracts. Theorem rows link to proofs. Each linked source span is checked against the frozen candidate during generation.

| Declaration | Kind and role | Named target | Step | Contracts |
| --- | --- | --- | --- | --- |
| [`PairCount`](../lean/PaperTargets/CanonicalSource.lean#L25) | def · definition not a proof | — | [LP01](../PROOF_NOTES.md#lp01) | DEF.POP |
| [`PairSource`](../lean/PaperTargets/CanonicalSource.lean#L20) | def · definition not a proof | — | [LP01](../PROOF_NOTES.md#lp01) | DEF.SOURCE |
| [`Powerful`](../lean/PaperTargets/Definitions.lean#L14) | def · definition not a proof | — | [LP01](../PROOF_NOTES.md#lp01) | DEF.POP |
| [`SourceRatios`](../lean/PaperTargets/CanonicalSource.lean#L31) | def · definition not a proof | — | [LP01](../PROOF_NOTES.md#lp01) | DEF.RATIO |
| [`StewartPrimitiveThue`](../lean/PaperTargets/ThueLevels.lean#L16) | def · published external proposition | — | [LP00](../PROOF_NOTES.md#lp00) | EXT.T |
| [`actualDirectInterval`](../lean/PaperTargets/DividedMinors.lean#L33) | def · definition not a proof | — | [LP06](../PROOF_NOTES.md#lp06) | DEF.BOX |
| [`actualRealBox`](../lean/PaperTargets/DividedMinors.lean#L36) | def · definition not a proof | — | [LP04](../PROOF_NOTES.md#lp04) | DEF.BOX |
| [`actual_box_determinant_bound`](../lean/PaperProofs/DividedMinors.lean#L495) | theorem · proved theorem | [`CF11ActualBoxDeterminantBound`](../lean/PaperTargets/DividedMinors.lean#L86) | [LP12](../PROOF_NOTES.md#lp12) | STD.REAL, C.CHART, R.MIXED, R.SCALES |
| [`actual_box_interval_cover`](../lean/PaperProofs/IntervalCover.lean#L54) | theorem · proved theorem | [`CF17ActualBoxIntervalCover`](../lean/PaperTargets/IntervalCover.lean#L19) | [LP06](../PROOF_NOTES.md#lp06) | DEF.BOX, EXT.R, C.REUSS, J03 |
| [`actual_box_product_bounds`](../lean/PaperProofs/ResidualProfiles.lean#L10) | theorem · proved theorem | [`CF04ActualBoxProductBounds`](../lean/PaperTargets/ResidualProfiles.lean#L11) | [LP04](../PROOF_NOTES.md#lp04) | B.SCALES, J02 |
| [`actual_box_source_count`](../lean/PaperProofs/BoxCounts.lean#L101) | theorem · proved theorem | [`CF17ActualBoxSourceCount`](../lean/PaperTargets/BoxCounts.lean#L42) | [LP21](../PROOF_NOTES.md#lp21) | DEF.SOURCE, STD.ASYMPTOTIC, B.KSMALL, B.MSMALL, B.PARTITION, I.RAW, I.ABSORBED, Z.SHELL, J10, J11 |
| [`actual_class_relation`](../lean/PaperProofs/ClassRelations.lean#L283) | theorem · proved theorem | [`CF12ActualClassRelation`](../lean/PaperTargets/ClassRelations.lean#L62) | [LP13](../PROOF_NOTES.md#lp13) | STD.LINEAR, D.RELATION, D.HEIGHT, J06 |
| [`actual_graph_divisor_growth`](../lean/PaperProofs/DivisorGrowth.lean#L124) | theorem · proved theorem | [`CF15ActualGraphDivisorGrowth`](../lean/PaperTargets/DivisorGrowth.lean#L29) | [LP18](../PROOF_NOTES.md#lp18) | STD.DIVISOR, A.HEIGHT |
| [`actual_graph_divisor_inventory`](../lean/PaperProofs/ResultantDivisors.lean#L122) | theorem · proved theorem | [`CF15ActualGraphDivisorInventory`](../lean/PaperTargets/ResultantDivisors.lean#L54) | [LP18](../PROOF_NOTES.md#lp18) | A.RESULTANT, A.DIVISORS |
| [`actual_graph_factor_dispatch`](../lean/PaperProofs/FactorDispatch.lean#L206) | theorem · proved theorem | [`CF15ActualGraphFactorDispatch`](../lean/PaperTargets/FactorDispatch.lean#L43) | [LP16](../PROOF_NOTES.md#lp16) | STD.POLYABC, A.DISPATCH, J09 |
| [`actual_graph_level_budget`](../lean/PaperProofs/ThueLevels.lean#L147) | theorem · proved theorem | [`CF15ActualGraphLevelBudget`](../lean/PaperTargets/ThueLevels.lean#L62) | [LP17](../PROOF_NOTES.md#lp17) | EXT.T, A.DISPATCH, A.THUE, J09 |
| [`actual_graph_parameter_count`](../lean/PaperProofs/SourceCounts.lean#L97) | theorem · proved theorem | [`CF15ActualGraphParameterCount`](../lean/PaperTargets/SourceCounts.lean#L31) | [LP18](../PROOF_NOTES.md#lp18) | A.CONTENT, A.THUE, A.DIVISORS |
| [`actual_graph_ruling_decomposition`](../lean/PaperProofs/GraphRulings.lean#L305) | theorem · proved theorem | [`CF13ActualGraphRulingDecomposition`](../lean/PaperTargets/GraphRulings.lean#L74) | [LP14](../PROOF_NOTES.md#lp14) | DEF.GRAPH, STD.FACTOR_HEIGHT, D.HEIGHT, G.BIDEGREE, A.NORMAL, J08 |
| [`actual_graph_source_count`](../lean/PaperProofs/SourceCounts.lean#L146) | theorem · proved theorem | [`CF15ActualGraphSourceCount`](../lean/PaperTargets/SourceCounts.lean#L49) | [LP18](../PROOF_NOTES.md#lp18) | DEF.RATIO, DEF.GRAPH, S.INJECT, A.CONTENT, A.DIVISORS, A.GRAPH_SMALL, J09 |
| [`actual_graph_source_subpower`](../lean/PaperProofs/SourceCounts.lean#L172) | theorem · proved theorem | [`CF15ActualGraphSourceSubpower`](../lean/PaperTargets/SourceCounts.lean#L58) | [LP18](../PROOF_NOTES.md#lp18) | STD.DIVISOR, A.HEIGHT, A.GRAPH_SMALL, J09 |
| [`actual_height_determinant`](../lean/PaperProofs/HeightDeterminants.lean#L136) | theorem · proved theorem | [`CF04ActualHeightDeterminant`](../lean/PaperTargets/HeightDeterminants.lean#L28) | [LP07](../PROOF_NOTES.md#lp07) | B.SCALES |
| [`actual_interval_nodes`](../lean/PaperProofs/DividedMinors.lean#L374) | theorem · proved theorem | [`CF11ActualIntervalNodes`](../lean/PaperTargets/DividedMinors.lean#L70) | [LP12](../PROOF_NOTES.md#lp12) | C.CHART, J03 |
| [`actual_minor_normalization`](../lean/PaperProofs/RealSources.lean#L158) | theorem · proved theorem | [`CF11ActualMinorNormalization`](../lean/PaperTargets/RealSources.lean#L68) | [LP12](../PROOF_NOTES.md#lp12) | R.SCALES, J05 |
| [`actual_mixed_nonpowers`](../lean/PaperProofs/PullbackNonpowers.lean#L225) | theorem · proved theorem | [`CF14ActualMixedNonpowers`](../lean/PaperTargets/PullbackNonpowers.lean#L69) | [LP16](../PROOF_NOTES.md#lp16) | STD.POLYABC, A.DISPATCH |
| [`actual_mixed_resultant`](../lean/PaperProofs/HomogeneousResultants.lean#L186) | theorem · proved theorem | [`CF13ActualMixedResultant`](../lean/PaperTargets/HomogeneousResultants.lean#L62) | [LP15](../PROOF_NOTES.md#lp15) | DEF.GRAPH, STD.SYLVESTER, A.RESULTANT, A.HEIGHT, J08 |
| [`actual_multiplier_ranges`](../lean/PaperProofs/UpperHeightSources.lean#L51) | theorem · proved theorem | [`CF04ActualMultiplierRanges`](../lean/PaperTargets/UpperHeightSources.lean#L12) | [LP07](../PROOF_NOTES.md#lp07) | B.SCALES, J02 |
| [`actual_reuss_log_scale`](../lean/PaperProofs/ReussLogScale.lean#L111) | theorem · proved theorem | [`CF04ActualReussLogScale`](../lean/PaperTargets/ReussLogScale.lean#L29) | [LP07](../PROOF_NOTES.md#lp07) | B.SCALES, B.PROFILE, J02 |
| [`actual_row_normalization`](../lean/PaperProofs/RealSources.lean#L121) | theorem · proved theorem | [`CF11ActualRowNormalization`](../lean/PaperTargets/RealSources.lean#L58) | [LP12](../PROOF_NOTES.md#lp12) | R.SCALES |
| [`actual_singular_source_count`](../lean/PaperProofs/SingularCounts.lean#L278) | theorem · proved theorem | [`CF06ActualSingularSourceCount`](../lean/PaperTargets/SingularCounts.lean#L25) | [LP09](../PROOF_NOTES.md#lp09) | DEF.RATIO, STD.BEZOUT, S.INJECT, C.SINGULAR |
| [`actual_source_determinants`](../lean/PaperProofs/SmoothSources.lean#L399) | theorem · proved theorem | [`CF10ActualSourceDeterminants`](../lean/PaperTargets/SmoothSources.lean#L82) | [LP11](../PROOF_NOTES.md#lp11) | DEF.MINOR, STD.IMPLICIT, STD.CB, V.ROWS, V.SERIES, V.FINITE, V.INTEGER, J05 |
| [`actual_source_implicit_polynomial`](../lean/PaperProofs/SmoothSources.lean#L338) | theorem · proved theorem | [`CF09ActualSourceImplicitPolynomial`](../lean/PaperTargets/SmoothSources.lean#L52) | [LP11](../PROOF_NOTES.md#lp11) | STD.IMPLICIT, V.SERIES |
| [`actual_source_resultant_level`](../lean/PaperProofs/SourceRecovery.lean#L236) | theorem · proved theorem | [`CF13ActualSourceResultantLevel`](../lean/PaperTargets/SourceRecovery.lean#L98) | [LP15](../PROOF_NOTES.md#lp15) | DEF.GRAPH, STD.SYLVESTER, A.RESULTANT, A.PULLBACK, A.CONTENT, J09 |
| [`actual_source_witness`](../lean/PaperProofs/PrimeAssignment.lean#L242) | theorem · proved theorem | [`CF07ActualSourceWitness`](../lean/PaperTargets/PrimeAssignment.lean#L71) | [LP10](../PROOF_NOTES.md#lp10) | P.WITNESS, J04 |
| [`actual_uniform_coarse_polynomial`](../lean/PaperProofs/GenericCoarse.lean#L276) | theorem · proved theorem | [`CF04ActualUniformCoarsePolynomial`](../lean/PaperTargets/GenericCoarse.lean#L23) | [LP08](../PROOF_NOTES.md#lp08) | DEF.SOURCE, DEF.PROFILE, EXT.R, STD.LINEAR, B.PROFILE, C.REUSS, J02, J03, J11 |
| [`actual_uniform_minor_vanishing`](../lean/PaperProofs/UniformRectangles.lean#L137) | theorem · proved theorem | [`CF04ActualUniformMinorVanishing`](../lean/PaperTargets/UniformRectangles.lean#L26) | [LP07](../PROOF_NOTES.md#lp07) | C.REUSS |
| [`actual_upper_height_log_budget`](../lean/PaperProofs/UpperHeightSources.lean#L75) | theorem · proved theorem | [`CF04ActualUpperHeightLogBudget`](../lean/PaperTargets/UpperHeightSources.lean#L23) | [LP07](../PROOF_NOTES.md#lp07) | B.SCALES, B.PROFILE, J02 |
| [`admitted_content_level`](../lean/PaperProofs/SourceRecovery.lean#L117) | theorem · proved theorem | [`CF13AdmittedContentLevel`](../lean/PaperTargets/SourceRecovery.lean#L89) | [LP15](../PROOF_NOTES.md#lp15) | A.CONTENT, J09 |
| [`bertrand_list`](../lean/PaperProofs/PrimeAssignment.lean#L288) | theorem · proved theorem | [`CF08BertrandList`](../lean/PaperTargets/PrimeAssignment.lean#L83) | [LP10](../PROOF_NOTES.md#lp10) | STD.PRIMES, P.LIST, J04 |
| [`binaryContent`](../lean/PaperTargets/SourceRecovery.lean#L12) | def · definition not a proof | — | [LP15](../PROOF_NOTES.md#lp15) | DEF.GRAPH |
| [`binaryPrimitivePart`](../lean/PaperTargets/SourceRecovery.lean#L14) | def · definition not a proof | — | [LP15](../PROOF_NOTES.md#lp15) | DEF.GRAPH |
| [`binary_content_removal`](../lean/PaperProofs/SourceRecovery.lean#L77) | theorem · proved theorem | [`CF13BinaryContentRemoval`](../lean/PaperTargets/SourceRecovery.lean#L80) | [LP15](../PROOF_NOTES.md#lp15) | A.CONTENT |
| [`boundedGraphData`](../lean/PaperTargets/GraphRulings.lean#L21) | def · definition not a proof | — | [LP14](../PROOF_NOTES.md#lp14) | DEF.GRAPH |
| [`boundedSourceRelation`](../lean/PaperTargets/ClassRelations.lean#L21) | def · definition not a proof | — | [LP13](../PROOF_NOTES.md#lp13) | DEF.GRAPH |
| [`bounded_graph_ruling_class_subpower`](../lean/PaperProofs/ClassCounts.lean#L23) | theorem · proved theorem | [`CF15BoundedGraphRulingClassSubpower`](../lean/PaperTargets/ClassCounts.lean#L19) | [LP19](../PROOF_NOTES.md#lp19) | A.NORMAL, A.RULINGS, A.GRAPH_SMALL, A.COMPONENT, J08 |
| [`bounded_integer_relation`](../lean/PaperProofs/ClassRelations.lean#L43) | theorem · proved theorem | [`CF12BoundedIntegerRelation`](../lean/PaperTargets/ClassRelations.lean#L28) | [LP13](../PROOF_NOTES.md#lp13) | STD.LINEAR, D.RELATION, J06 |
| [`centre_values`](../lean/PaperProofs/ExactProfiles.lean#L47) | theorem · proved theorem | [`CF16CentreValues`](../lean/PaperTargets/ExactProfiles.lean#L43) | [LP05](../PROOF_NOTES.md#lp05) | O.ENVELOPE |
| [`chartMonomial`](../lean/PaperTargets/SmoothSources.lean#L23) | def · definition not a proof | — | [LP11](../PROOF_NOTES.md#lp11) | DEF.MINOR |
| [`chart_branches`](../lean/PaperProofs/ExactProfiles.lean#L33) | theorem · proved theorem | [`CF16ChartBranches`](../lean/PaperTargets/ExactProfiles.lean#L35) | [LP05](../PROOF_NOTES.md#lp05) | O.ENVELOPE |
| [`cleared_identity`](../lean/PaperProofs/PrimeAssignment.lean#L44) | theorem · proved theorem | [`CF07ClearedIdentity`](../lean/PaperTargets/PrimeAssignment.lean#L64) | [LP10](../PROOF_NOTES.md#lp10) | P.WITNESS |
| [`coarse_interval_source_count`](../lean/PaperProofs/IntervalCounts.lean#L122) | theorem · proved theorem | [`CF17CoarseIntervalSourceCount`](../lean/PaperTargets/IntervalCounts.lean#L29) | [LP20](../PROOF_NOTES.md#lp20) | DEF.RATIO, C.FACTOR, I.CASES, I.RAW, J03, J07, J10 |
| [`compact_box_source_count`](../lean/PaperProofs/BoxCounts.lean#L24) | theorem · proved theorem | [`CF17CompactBoxSourceCount`](../lean/PaperTargets/BoxCounts.lean#L16) | [LP20](../PROOF_NOTES.md#lp20) | DEF.BOX, DEF.PROFILE, O.ROUND, C.REUSS, C.FACTOR, I.RAW, I.ABSORBED, J03, J10, J11 |
| [`constant_graph_ruling`](../lean/PaperProofs/ClassCounts.lean#L9) | theorem · proved theorem | [`CF15ConstantGraphRuling`](../lean/PaperTargets/ClassCounts.lean#L11) | [LP14](../PROOF_NOTES.md#lp14) | A.RULINGS |
| [`coordinate_ruling_count`](../lean/PaperProofs/RulingCounts.lean#L163) | theorem · proved theorem | [`CF15CoordinateRulingCount`](../lean/PaperTargets/RulingCounts.lean#L37) | [LP14](../PROOF_NOTES.md#lp14) | B.MFIX, A.RULINGS |
| [`coordinate_ruling_subpower`](../lean/PaperProofs/RulingCounts.lean#L208) | theorem · proved theorem | [`CF15CoordinateRulingSubpower`](../lean/PaperTargets/RulingCounts.lean#L51) | [LP14](../PROOF_NOTES.md#lp14) | A.RULINGS |
| [`count_empty_boundary`](../lean/PaperProofs/CanonicalSource.lean#L239) | theorem · proved theorem | [`CF01CountEmptyBoundary`](../lean/PaperTargets/CanonicalSource.lean#L127) | [LP01](../PROOF_NOTES.md#lp01) | DEF.POP |
| [`count_source_correspondence`](../lean/PaperProofs/CanonicalSource.lean#L218) | theorem · proved theorem | [`CF01CountSourceCorrespondence`](../lean/PaperTargets/CanonicalSource.lean#L121) | [LP01](../PROOF_NOTES.md#lp01) | DEF.POP, S.PAIR, J01, J12 |
| [`cross_endpoint_coprime`](../lean/PaperProofs/CanonicalSource.lean#L114) | theorem · proved theorem | [`CF01CrossEndpointCoprime`](../lean/PaperTargets/CanonicalSource.lean#L59) | [LP01](../PROOF_NOTES.md#lp01) | S.COPRIME |
| [`cube_square_powerful`](../lean/PaperProofs/CanonicalSource.lean#L48) | theorem · proved theorem | [`CF01CubeSquarePowerful`](../lean/PaperTargets/CanonicalSource.lean#L42) | [LP01](../PROOF_NOTES.md#lp01) | S.NORMAL |
| [`direct_source_recovery`](../lean/PaperProofs/SourceRecovery.lean#L184) | theorem · proved theorem | [`CF13DirectSourceRecovery`](../lean/PaperTargets/SourceRecovery.lean#L72) | [LP15](../PROOF_NOTES.md#lp15) | A.PULLBACK |
| [`distinct_low_factor_pair`](../lean/PaperProofs/FactorDispatch.lean#L77) | theorem · proved theorem | [`CF15DistinctLowFactorPair`](../lean/PaperTargets/FactorDispatch.lean#L22) | [LP16](../PROOF_NOTES.md#lp16) | A.LOW_DISJOINT |
| [`divisor_subpower`](../lean/PaperProofs/DivisorGrowth.lean#L75) | theorem · proved theorem | [`CF15DivisorSubpower`](../lean/PaperTargets/DivisorGrowth.lean#L18) | [LP18](../PROOF_NOTES.md#lp18) | STD.DIVISOR |
| [`dyadic_product_labels`](../lean/PaperProofs/SmallMultipliers.lean#L18) | theorem · proved theorem | [`CF03DyadicProductLabels`](../lean/PaperTargets/SmallMultipliers.lean#L11) | [LP03](../PROOF_NOTES.md#lp03) | B.MSMALL |
| [`evaluated_gcd`](../lean/PaperProofs/HomogeneousResultants.lean#L118) | theorem · proved theorem | [`CF13EvaluatedGCD`](../lean/PaperTargets/HomogeneousResultants.lean#L48) | [LP15](../PROOF_NOTES.md#lp15) | STD.SYLVESTER, A.RESULTANT |
| [`finite_implicit_polynomial`](../lean/PaperProofs/SmoothSources.lean#L241) | theorem · proved theorem | [`CF09FiniteImplicitPolynomial`](../lean/PaperTargets/SmoothSources.lean#L40) | [LP11](../PROOF_NOTES.md#lp11) | STD.IMPLICIT, V.SERIES |
| [`first_cutoffs`](../lean/PaperProofs/CutoffControls.lean#L12) | theorem · proved theorem | [`CF01FirstCutoffs`](../lean/PaperTargets/CutoffControls.lean#L10) | [LP01](../PROOF_NOTES.md#lp01) | DEF.POP |
| [`first_good_assignment`](../lean/PaperProofs/PrimeAssignment.lean#L330) | theorem · proved theorem | [`CF08FirstGoodAssignment`](../lean/PaperTargets/PrimeAssignment.lean#L88) | [LP10](../PROOF_NOTES.md#lp10) | P.ASSIGN, J04 |
| [`fixed_content_divisor_count`](../lean/PaperProofs/SourceCounts.lean#L60) | theorem · proved theorem | [`CF15FixedContentDivisorCount`](../lean/PaperTargets/SourceCounts.lean#L21) | [LP18](../PROOF_NOTES.md#lp18) | A.DIVISORS, J09 |
| [`fixed_content_level_bound`](../lean/PaperProofs/SourceCounts.lean#L9) | theorem · proved theorem | [`CF15FixedContentLevelBound`](../lean/PaperTargets/SourceCounts.lean#L12) | [LP18](../PROOF_NOTES.md#lp18) | A.THUE, A.LOW_COUNT |
| [`fixed_kernel_product_count`](../lean/PaperProofs/SmallKernels.lean#L94) | theorem · proved theorem | [`CF02FixedKernelProductCount`](../lean/PaperTargets/SmallKernels.lean#L21) | [LP02](../PROOF_NOTES.md#lp02) | S.COPRIME, B.KFIX |
| [`fixed_kernel_ratio_count`](../lean/PaperProofs/RulingCounts.lean#L147) | theorem · proved theorem | [`CF15FixedKernelRatioCount`](../lean/PaperTargets/RulingCounts.lean#L31) | [LP02](../PROOF_NOTES.md#lp02) | B.KFIX, A.RULINGS |
| [`fixed_multiplier_ratio_count`](../lean/PaperProofs/RulingCounts.lean#L99) | theorem · proved theorem | [`CF15FixedMultiplierRatioCount`](../lean/PaperTargets/RulingCounts.lean#L24) | [LP03](../PROOF_NOTES.md#lp03) | EXT.T, B.MFIX, A.RULINGS |
| [`fullGraphResultant`](../lean/PaperTargets/HomogeneousResultants.lean#L18) | def · definition not a proof | — | [LP15](../PROOF_NOTES.md#lp15) | DEF.GRAPH |
| [`full_resultant_nonzero`](../lean/PaperProofs/HomogeneousResultants.lean#L35) | theorem · proved theorem | [`CF13FullResultantNonzero`](../lean/PaperTargets/HomogeneousResultants.lean#L30) | [LP15](../PROOF_NOTES.md#lp15) | A.RESULTANT |
| [`generic_bounded_integer_relation`](../lean/PaperProofs/GenericCoarse.lean#L45) | theorem · proved theorem | [`CF04GenericBoundedIntegerRelation`](../lean/PaperTargets/GenericCoarse.lean#L12) | [LP08](../PROOF_NOTES.md#lp08) | STD.LINEAR, C.REUSS |
| [`graphDegree`](../lean/PaperTargets/HomogeneousResultants.lean#L13) | def · definition not a proof | — | [LP15](../PROOF_NOTES.md#lp15) | DEF.GRAPH |
| [`graphPullback`](../lean/PaperTargets/SourceRecovery.lean#L25) | def · definition not a proof | — | [LP15](../PROOF_NOTES.md#lp15) | DEF.GRAPH |
| [`graph_parameter_injection`](../lean/PaperProofs/SourceCounts.lean#L127) | theorem · proved theorem | [`CF15GraphParameterInjection`](../lean/PaperTargets/SourceCounts.lean#L41) | [LP18](../PROOF_NOTES.md#lp18) | S.INJECT, A.GRAPH_SMALL, J09 |
| [`graph_ruling_dispatch`](../lean/PaperProofs/GraphRulings.lean#L239) | theorem · proved theorem | [`CF13GraphRulingDispatch`](../lean/PaperTargets/GraphRulings.lean#L60) | [LP14](../PROOF_NOTES.md#lp14) | A.NORMAL |
| [`high_factor_level_budget`](../lean/PaperProofs/ThueLevels.lean#L99) | theorem · proved theorem | [`CF15HighFactorLevelBudget`](../lean/PaperTargets/ThueLevels.lean#L42) | [LP17](../PROOF_NOTES.md#lp17) | EXT.T, A.THUE |
| [`high_factor_thue_admissibility`](../lean/PaperProofs/ThueLevels.lean#L10) | theorem · proved theorem | [`CF15HighFactorThueAdmissibility`](../lean/PaperTargets/ThueLevels.lean#L25) | [LP17](../PROOF_NOTES.md#lp17) | A.THUE |
| [`homogeneousGraphValue`](../lean/PaperTargets/HomogeneousResultants.lean#L15) | def · definition not a proof | — | [LP15](../PROOF_NOTES.md#lp15) | DEF.GRAPH |
| [`homogeneous_bezout`](../lean/PaperProofs/HomogeneousResultants.lean#L94) | theorem · proved theorem | [`CF13HomogeneousBezout`](../lean/PaperTargets/HomogeneousResultants.lean#L36) | [LP15](../PROOF_NOTES.md#lp15) | STD.SYLVESTER, A.RESULTANT |
| [`homogeneous_primitive_zeros`](../lean/PaperProofs/LowFactorLevels.lean#L104) | theorem · proved theorem | [`CF15HomogeneousPrimitiveZeros`](../lean/PaperTargets/LowFactorLevels.lean#L42) | [LP17](../PROOF_NOTES.md#lp17) | A.LOW_COUNT |
| [`homogeneous_small_power_exclusion`](../lean/PaperProofs/PullbackNonpowers.lean#L208) | theorem · proved theorem | [`CF14HomogeneousSmallPowerExclusion`](../lean/PaperTargets/PullbackNonpowers.lean#L63) | [LP16](../PROOF_NOTES.md#lp16) | STD.POLYABC |
| [`infinity_low_factor_pair`](../lean/PaperProofs/FactorDispatch.lean#L94) | theorem · proved theorem | [`CF15InfinityLowFactorPair`](../lean/PaperTargets/FactorDispatch.lean#L30) | [LP16](../PROOF_NOTES.md#lp16) | A.LOW_DISJOINT |
| [`integer_coarse_factor_height`](../lean/PaperProofs/CoarseFactors.lean#L95) | theorem · proved theorem | [`CF05IntegerCoarseFactorHeight`](../lean/PaperTargets/CoarseFactors.lean#L26) | [LP09](../PROOF_NOTES.md#lp09) | STD.FACTOR_HEIGHT |
| [`integer_factor_height`](../lean/PaperProofs/GraphRulings.lean#L181) | theorem · proved theorem | [`CF13IntegerFactorHeight`](../lean/PaperTargets/GraphRulings.lean#L53) | [LP14](../PROOF_NOTES.md#lp14) | STD.FACTOR_HEIGHT |
| [`inverse_source_recovery`](../lean/PaperProofs/SourceRecovery.lean#L210) | theorem · proved theorem | [`CF13InverseSourceRecovery`](../lean/PaperTargets/SourceRecovery.lean#L76) | [LP15](../PROOF_NOTES.md#lp15) | A.PULLBACK |
| [`irreducible_interval_source_count`](../lean/PaperProofs/IntervalCounts.lean#L22) | theorem · proved theorem | [`CF17IrreducibleIntervalSourceCount`](../lean/PaperTargets/IntervalCounts.lean#L13) | [LP20](../PROOF_NOTES.md#lp20) | STD.FP, C.SINGULAR, P.LIST, P.ASSIGN, P.LABELS, A.COMPONENT, I.CASES, I.RAW, I.ABSORBED, J04, J07, J10 |
| [`irreducible_thue_level`](../lean/PaperProofs/ThueLevels.lean#L32) | theorem · proved theorem | [`CF15IrreducibleThueLevel`](../lean/PaperTargets/ThueLevels.lean#L33) | [LP17](../PROOF_NOTES.md#lp17) | EXT.T, A.THUE |
| [`kronecker_control`](../lean/PaperProofs/CoarseFactors.lean#L60) | theorem · proved theorem | [`CF05KroneckerControl`](../lean/PaperTargets/CoarseFactors.lean#L17) | [LP09](../PROOF_NOTES.md#lp09) | STD.FACTOR_HEIGHT |
| [`linear_quadratic_levels`](../lean/PaperProofs/LowFactorLevels.lean#L195) | theorem · proved theorem | [`CF15LinearQuadraticLevels`](../lean/PaperTargets/LowFactorLevels.lean#L55) | [LP17](../PROOF_NOTES.md#lp17) | A.LOW_COUNT |
| [`low_factor_divisor_budget`](../lean/PaperProofs/LowFactorLevels.lean#L274) | theorem · proved theorem | [`CF15LowFactorDivisorBudget`](../lean/PaperTargets/LowFactorLevels.lean#L71) | [LP17](../PROOF_NOTES.md#lp17) | STD.BEZOUT, A.LOW_DISJOINT, A.LOW_COUNT |
| [`mixed_root_determinants`](../lean/PaperProofs/DividedMinors.lean#L187) | theorem · proved theorem | [`CF11MixedRootDeterminants`](../lean/PaperTargets/DividedMinors.lean#L51) | [LP12](../PROOF_NOTES.md#lp12) | STD.REAL, R.MIXED |
| [`multiplier_cubic_admissibility`](../lean/PaperProofs/RulingCounts.lean#L27) | theorem · proved theorem | [`CF15MultiplierCubicAdmissibility`](../lean/PaperTargets/RulingCounts.lean#L14) | [LP03](../PROOF_NOTES.md#lp03) | S.COPRIME, B.MFIX |
| [`natural_pair_count`](../lean/PaperProofs/GlobalCounts.lean#L118) | theorem · proved theorem | [`CF18NaturalPairCount`](../lean/PaperTargets/GlobalCounts.lean#L22) | [LP23](../PROOF_NOTES.md#lp23) | DEF.POP, DEF.SOURCE, STD.ASYMPTOTIC, S.PAIR, Z.SHELL, Z.NAT, J01, J11, J12, P0365Subquarter.natural_pair_count |
| [`nonaxis_abc`](../lean/PaperProofs/PullbackNonpowers.lean#L146) | theorem · proved theorem | [`CF14NonaxisABC`](../lean/PaperTargets/PullbackNonpowers.lean#L52) | [LP16](../PROOF_NOTES.md#lp16) | STD.POLYABC |
| [`normal_form`](../lean/PaperProofs/CanonicalSource.lean#L72) | theorem · proved theorem | [`CF01NormalForm`](../lean/PaperTargets/CanonicalSource.lean#L34) | [LP01](../PROOF_NOTES.md#lp01) | S.NORMAL, J01 |
| [`normal_form_unique`](../lean/PaperProofs/CanonicalSource.lean#L58) | theorem · proved theorem | [`CF01NormalFormUnique`](../lean/PaperTargets/CanonicalSource.lean#L38) | [LP01](../PROOF_NOTES.md#lp01) | S.NORMAL |
| [`normalized_determinant_bound`](../lean/PaperProofs/DividedMinors.lean#L268) | theorem · proved theorem | [`CF11NormalizedDeterminantBound`](../lean/PaperTargets/DividedMinors.lean#L61) | [LP12](../PROOF_NOTES.md#lp12) | STD.REAL, R.MIXED |
| [`original_shell_source_count`](../lean/PaperProofs/GlobalCounts.lean#L52) | theorem · proved theorem | [`CF18OriginalShellSourceCount`](../lean/PaperTargets/GlobalCounts.lean#L12) | [LP22](../PROOF_NOTES.md#lp22) | DEF.BOX, STD.ASYMPTOTIC, B.INVENTORY, I.ABSORBED, Z.SHELL, J11, P0365Subquarter.original_shell_source_count |
| [`original_small_kernel_count`](../lean/PaperProofs/SmallKernels.lean#L136) | theorem · proved theorem | [`CF02OriginalSmallKernelCount`](../lean/PaperTargets/SmallKernels.lean#L36) | [LP02](../PROOF_NOTES.md#lp02) | B.KSMALL |
| [`original_small_kernel_subpower`](../lean/PaperProofs/SmallKernelScale.lean#L11) | theorem · proved theorem | [`CF02OriginalSmallKernelSubpower`](../lean/PaperTargets/SmallKernelScale.lean#L11) | [LP02](../PROOF_NOTES.md#lp02) | STD.ASYMPTOTIC, B.KSMALL |
| [`original_small_multiplier_count`](../lean/PaperProofs/SmallMultipliers.lean#L63) | theorem · proved theorem | [`CF03OriginalSmallMultiplierCount`](../lean/PaperTargets/SmallMultipliers.lean#L25) | [LP03](../PROOF_NOTES.md#lp03) | B.MFIX, B.MSMALL |
| [`original_small_multiplier_subpower`](../lean/PaperProofs/SmallMultipliers.lean#L92) | theorem · proved theorem | [`CF03OriginalSmallMultiplierSubpower`](../lean/PaperTargets/SmallMultipliers.lean#L32) | [LP03](../PROOF_NOTES.md#lp03) | STD.ASYMPTOTIC, B.MSMALL |
| [`pair_source_equivalence`](../lean/PaperProofs/CanonicalSource.lean#L85) | theorem · proved theorem | [`CF01PairSourceEquivalence`](../lean/PaperTargets/CanonicalSource.lean#L45) | [LP01](../PROOF_NOTES.md#lp01) | DEF.SOURCE, S.NORMAL, S.PAIR, J01 |
| [`pair_source_unique`](../lean/PaperProofs/CanonicalSource.lean#L97) | theorem · proved theorem | [`CF01PairSourceUnique`](../lean/PaperTargets/CanonicalSource.lean#L49) | [LP01](../PROOF_NOTES.md#lp01) | DEF.SOURCE, S.NORMAL, S.PAIR, J01 |
| [`polynomialValue`](../lean/PaperTargets/PrimeAssignment.lean#L24) | def · definition not a proof | — | [LP01](../PROOF_NOTES.md#lp01) | DEF.RATIO |
| [`polynomial_evaluation_determinant`](../lean/PaperProofs/SmoothSources.lean#L17) | theorem · proved theorem | [`CF10PolynomialEvaluationDeterminant`](../lean/PaperTargets/SmoothSources.lean#L67) | [LP11](../PROOF_NOTES.md#lp11) | STD.CB, V.FINITE |
| [`polynomial_height_divisor_growth`](../lean/PaperProofs/DivisorGrowth.lean#L96) | theorem · proved theorem | [`CF15PolynomialHeightDivisorGrowth`](../lean/PaperTargets/DivisorGrowth.lean#L22) | [LP18](../PROOF_NOTES.md#lp18) | STD.DIVISOR |
| [`primitive_factor_dispatch`](../lean/PaperProofs/FactorDispatch.lean#L133) | theorem · proved theorem | [`CF15PrimitiveFactorDispatch`](../lean/PaperTargets/FactorDispatch.lean#L36) | [LP16](../PROOF_NOTES.md#lp16) | A.DISPATCH |
| [`primitive_factor_inventory`](../lean/PaperProofs/FactorInventory.lean#L87) | theorem · proved theorem | [`CF05PrimitiveFactorInventory`](../lean/PaperTargets/FactorInventory.lean#L18) | [LP09](../PROOF_NOTES.md#lp09) | C.FACTOR |
| [`primitive_gcd_removal`](../lean/PaperProofs/GraphRulings.lean#L95) | theorem · proved theorem | [`CF13PrimitiveGCDRemoval`](../lean/PaperTargets/GraphRulings.lean#L44) | [LP14](../PROOF_NOTES.md#lp14) | A.NORMAL |
| [`primitive_ratios`](../lean/PaperProofs/CanonicalSource.lean#L123) | theorem · proved theorem | [`CF01PrimitiveRatios`](../lean/PaperTargets/CanonicalSource.lean#L63) | [LP01](../PROOF_NOTES.md#lp01) | DEF.RATIO, S.COPRIME |
| [`primitive_signed_recovery`](../lean/PaperProofs/SourceRecovery.lean#L10) | theorem · proved theorem | [`CF13PrimitiveSignedRecovery`](../lean/PaperTargets/SourceRecovery.lean#L64) | [LP15](../PROOF_NOTES.md#lp15) | A.PULLBACK |
| [`profileCentre`](../lean/PaperTargets/ExactProfiles.lean#L17) | def · definition not a proof | — | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE |
| [`profileErrorWeight`](../lean/PaperTargets/ExactProfiles.lean#L22) | def · definition not a proof | — | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE |
| [`profileM0`](../lean/PaperTargets/ExactProfiles.lean#L18) | def · definition not a proof | — | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE |
| [`profileRho`](../lean/PaperTargets/ExactProfiles.lean#L16) | def · definition not a proof | — | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE |
| [`profileTheta`](../lean/PaperTargets/ExactProfiles.lean#L15) | def · definition not a proof | — | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE |
| [`profileW`](../lean/PaperTargets/ExactProfiles.lean#L19) | def · definition not a proof | — | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE |
| [`profile_bounds`](../lean/PaperProofs/ExactProfiles.lean#L24) | theorem · proved theorem | [`CF16ProfileBounds`](../lean/PaperTargets/ExactProfiles.lean#L31) | [LP05](../PROOF_NOTES.md#lp05) | O.ENVELOPE |
| [`profile_envelope`](../lean/PaperProofs/ExactProfiles.lean#L62) | theorem · proved theorem | [`CF16Envelope`](../lean/PaperTargets/ExactProfiles.lean#L39) | [LP05](../PROOF_NOTES.md#lp05) | O.ENVELOPE |
| [`radical_support_bound`](../lean/PaperProofs/PullbackNonpowers.lean#L112) | theorem · proved theorem | [`CF14RadicalSupportBound`](../lean/PaperTargets/PullbackNonpowers.lean#L43) | [LP16](../PROOF_NOTES.md#lp16) | STD.POLYABC |
| [`real_pair_count`](../lean/PaperProofs/GlobalCounts.lean#L207) | theorem · proved theorem | [`CF18RealPairCount`](../lean/PaperTargets/GlobalCounts.lean#L27) | [LP24](../PROOF_NOTES.md#lp24) | DEF.POP, STD.ASYMPTOTIC, Z.NAT, Z.REAL, J01, J11, J12, P0365Subquarter.real_pair_count |
| [`real_scale_cancellation`](../lean/PaperProofs/RealSources.lean#L179) | theorem · proved theorem | [`CF11RealScaleCancellation`](../lean/PaperTargets/RealSources.lean#L80) | [LP12](../PROOF_NOTES.md#lp12) | R.SCALES |
| [`rectangular_scale_products`](../lean/PaperProofs/HeightDeterminants.lean#L44) | theorem · proved theorem | [`CF04RectangularScaleProducts`](../lean/PaperTargets/HeightDeterminants.lean#L17) | [LP07](../PROOF_NOTES.md#lp07) | B.SCALES |
| [`relationExponent`](../lean/PaperTargets/ClassRelations.lean#L12) | def · definition not a proof | — | [LP13](../PROOF_NOTES.md#lp13) | DEF.MINOR |
| [`relationPolynomial`](../lean/PaperTargets/ClassRelations.lean#L17) | def · definition not a proof | — | [LP13](../PROOF_NOTES.md#lp13) | DEF.MINOR |
| [`relation_polynomial`](../lean/PaperProofs/ClassRelations.lean#L198) | theorem · proved theorem | [`CF12RelationPolynomial`](../lean/PaperTargets/ClassRelations.lean#L42) | [LP13](../PROOF_NOTES.md#lp13) | D.HEIGHT |
| [`relation_sections`](../lean/PaperProofs/GraphRulings.lean#L44) | theorem · proved theorem | [`CF13RelationSections`](../lean/PaperTargets/GraphRulings.lean#L32) | [LP14](../PROOF_NOTES.md#lp14) | A.NORMAL |
| [`residual_box_source_count`](../lean/PaperProofs/BoxCounts.lean#L81) | theorem · proved theorem | [`CF17ResidualBoxSourceCount`](../lean/PaperTargets/BoxCounts.lean#L29) | [LP20](../PROOF_NOTES.md#lp20) | B.PROFILE, I.RAW, I.ABSORBED, J02, J10, J11 |
| [`residual_compact_profile`](../lean/PaperProofs/ResidualProfiles.lean#L38) | theorem · proved theorem | [`CF04ResidualCompactProfile`](../lean/PaperTargets/ResidualProfiles.lean#L19) | [LP04](../PROOF_NOTES.md#lp04) | B.SCALES, B.PROFILE, J02 |
| [`resultant_height`](../lean/PaperProofs/HomogeneousResultants.lean#L167) | theorem · proved theorem | [`CF13ResultantHeight`](../lean/PaperTargets/HomogeneousResultants.lean#L54) | [LP15](../PROOF_NOTES.md#lp15) | A.HEIGHT |
| [`resultant_level_charges`](../lean/PaperProofs/ResultantDivisors.lean#L73) | theorem · proved theorem | [`CF15ResultantLevelCharges`](../lean/PaperTargets/ResultantDivisors.lean#L38) | [LP18](../PROOF_NOTES.md#lp18) | A.DIVISORS |
| [`roundedHeight`](../lean/PaperTargets/RoundedProfiles.lean#L17) | def · definition not a proof | — | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE |
| [`roundedScale`](../lean/PaperTargets/RoundedProfiles.lean#L20) | def · definition not a proof | — | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE |
| [`rounded_actual_determinant_bound`](../lean/PaperProofs/DividedMinors.lean#L652) | theorem · proved theorem | [`CF11RoundedActualDeterminantBound`](../lean/PaperTargets/DividedMinors.lean#L98) | [LP12](../PROOF_NOTES.md#lp12) | STD.REAL, R.SCALES, R.BOUND, J05 |
| [`rounded_actual_minor_vanishing`](../lean/PaperProofs/DividedMinors.lean#L666) | theorem · proved theorem | [`CF11RoundedActualMinorVanishing`](../lean/PaperTargets/DividedMinors.lean#L111) | [LP13](../PROOF_NOTES.md#lp13) | DEF.PROFILE, DEF.MINOR, O.ROUND, C.CHART, V.INTEGER, R.BOUND, O.ABSORB, D.ZERO, J05 |
| [`rounded_class_graph_rulings`](../lean/PaperProofs/GraphRulings.lean#L358) | theorem · proved theorem | [`CF13RoundedClassGraphRulings`](../lean/PaperTargets/GraphRulings.lean#L83) | [LP14](../PROOF_NOTES.md#lp14) | D.RELATION, D.HEIGHT, A.NORMAL, J06, J08 |
| [`rounded_class_resultant_levels`](../lean/PaperProofs/SourceRecovery.lean#L266) | theorem · proved theorem | [`CF13RoundedClassResultantLevels`](../lean/PaperTargets/SourceRecovery.lean#L109) | [LP15](../PROOF_NOTES.md#lp15) | A.CONTENT |
| [`rounded_class_source_subpower`](../lean/PaperProofs/ClassCounts.lean#L88) | theorem · proved theorem | [`CF15RoundedClassSourceSubpower`](../lean/PaperTargets/ClassCounts.lean#L30) | [LP19](../PROOF_NOTES.md#lp19) | STD.BEZOUT, G.PROPER, A.COMPONENT, I.PROPER, I.COMMON, J07, J08, J10 |
| [`rounded_entire_class_relation`](../lean/PaperProofs/ClassRelations.lean#L319) | theorem · proved theorem | [`CF12RoundedEntireClassRelation`](../lean/PaperTargets/ClassRelations.lean#L75) | [LP13](../PROOF_NOTES.md#lp13) | DEF.MINOR, D.ZERO, D.RELATION, D.HEIGHT, J05, J06, J08 |
| [`rounded_error_absorption`](../lean/PaperProofs/RoundedProfiles.lean#L146) | theorem · proved theorem | [`CF17RoundedErrorAbsorption`](../lean/PaperTargets/RoundedProfiles.lean#L50) | [LP05](../PROOF_NOTES.md#lp05) | O.SLACK, O.ABSORB |
| [`rounded_height_bounds`](../lean/PaperProofs/RoundedProfiles.lean#L23) | theorem · proved theorem | [`CF16RoundedHeightBounds`](../lean/PaperTargets/RoundedProfiles.lean#L29) | [LP05](../PROOF_NOTES.md#lp05) | O.ROUND |
| [`rounded_mixed_term_bound`](../lean/PaperProofs/RoundedProfiles.lean#L107) | theorem · proved theorem | [`CF17RoundedMixedTermBound`](../lean/PaperTargets/RoundedProfiles.lean#L42) | [LP05](../PROOF_NOTES.md#lp05) | O.SLACK, O.ROUND |
| [`rounded_prime_scale`](../lean/PaperProofs/RoundedProfiles.lean#L38) | theorem · proved theorem | [`CF17RoundedPrimeScale`](../lean/PaperTargets/RoundedProfiles.lean#L36) | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE, O.SLACK, O.ROUND |
| [`rounded_shell_source_assignment`](../lean/PaperProofs/ShellPrimes.lean#L10) | theorem · proved theorem | [`CF08RoundedShellSourceAssignment`](../lean/PaperTargets/ShellPrimes.lean#L13) | [LP10](../PROOF_NOTES.md#lp10) | STD.PRIMES, STD.FP, O.ROUND, P.WITNESS, P.LIST, P.ASSIGN, P.LABELS, J04 |
| [`rounded_source_assignment`](../lean/PaperProofs/PrimeAssignment.lean#L403) | theorem · proved theorem | [`CF08RoundedSourceAssignment`](../lean/PaperTargets/PrimeAssignment.lean#L106) | [LP10](../PROOF_NOTES.md#lp10) | STD.PRIMES, STD.FP, P.WITNESS, P.ASSIGN |
| [`ruling_log_subpower`](../lean/PaperProofs/RulingCounts.lean#L178) | theorem · proved theorem | [`CF15RulingLogSubpower`](../lean/PaperTargets/RulingCounts.lean#L45) | [LP02](../PROOF_NOTES.md#lp02) | STD.ASYMPTOTIC |
| [`selectedRealChart`](../lean/PaperTargets/DividedMinors.lean#L47) | def · definition not a proof | — | [LP05](../PROOF_NOTES.md#lp05) | DEF.PROFILE |
| [`selected_factor_level_budget`](../lean/PaperProofs/ThueLevels.lean#L134) | theorem · proved theorem | [`CF15SelectedFactorLevelBudget`](../lean/PaperTargets/ThueLevels.lean#L53) | [LP17](../PROOF_NOTES.md#lp17) | A.THUE, A.LOW_DISJOINT, A.LOW_COUNT |
| [`singular_rational_point_count`](../lean/PaperProofs/SingularCounts.lean#L202) | theorem · proved theorem | [`CF06SingularRationalPointCount`](../lean/PaperTargets/SingularCounts.lean#L18) | [LP09](../PROOF_NOTES.md#lp09) | C.SINGULAR |
| [`small_kernel_product_count`](../lean/PaperProofs/SmallKernels.lean#L116) | theorem · proved theorem | [`CF02SmallKernelProductCount`](../lean/PaperTargets/SmallKernels.lean#L26) | [LP02](../PROOF_NOTES.md#lp02) | B.KFIX, B.KSMALL |
| [`small_multiplier_labels`](../lean/PaperProofs/SmallMultipliers.lean#L38) | theorem · proved theorem | [`CF03SmallMultiplierLabels`](../lean/PaperTargets/SmallMultipliers.lean#L18) | [LP03](../PROOF_NOTES.md#lp03) | B.MSMALL |
| [`smooth_label_budget`](../lean/PaperProofs/PrimeAssignment.lean#L392) | theorem · proved theorem | [`CF08SmoothLabelBudget`](../lean/PaperTargets/PrimeAssignment.lean#L97) | [LP10](../PROOF_NOTES.md#lp10) | STD.FP, P.LABELS |
| [`sourceIntegerRow`](../lean/PaperTargets/SmoothSources.lean#L29) | def · definition not a proof | — | [LP11](../PROOF_NOTES.md#lp11) | DEF.MINOR |
| [`sourcePoint`](../lean/PaperTargets/PrimeAssignment.lean#L18) | def · definition not a proof | — | [LP01](../PROOF_NOTES.md#lp01) | DEF.RATIO |
| [`sourceRowDenominator`](../lean/PaperTargets/SmoothSources.lean#L35) | def · definition not a proof | — | [LP11](../PROOF_NOTES.md#lp11) | DEF.MINOR |
| [`source_bounds`](../lean/PaperProofs/CanonicalSource.lean#L132) | theorem · proved theorem | [`CF01SourceBounds`](../lean/PaperTargets/CanonicalSource.lean#L67) | [LP01](../PROOF_NOTES.md#lp01) | B.SCALES |
| [`source_ratio_coordinate_injection`](../lean/PaperProofs/CanonicalSource.lean#L166) | theorem · proved theorem | [`CF01SourceRatioCoordinateInjection`](../lean/PaperTargets/CanonicalSource.lean#L82) | [LP01](../PROOF_NOTES.md#lp01) | DEF.RATIO, S.COPRIME, S.INJECT |
| [`source_ratio_injection`](../lean/PaperProofs/CanonicalSource.lean#L181) | theorem · proved theorem | [`CF01SourceRatioInjection`](../lean/PaperTargets/CanonicalSource.lean#L77) | [LP01](../PROOF_NOTES.md#lp01) | DEF.RATIO, S.INJECT |
| [`source_relation_evaluation`](../lean/PaperProofs/ClassRelations.lean#L257) | theorem · proved theorem | [`CF12SourceRelationEvaluation`](../lean/PaperTargets/ClassRelations.lean#L55) | [LP13](../PROOF_NOTES.md#lp13) | V.ROWS |
| [`source_row_height`](../lean/PaperProofs/ClassRelations.lean#L119) | theorem · proved theorem | [`CF12SourceRowHeight`](../lean/PaperTargets/ClassRelations.lean#L36) | [LP13](../PROOF_NOTES.md#lp13) | D.HEIGHT |
| [`source_row_identity`](../lean/PaperProofs/SmoothSources.lean#L351) | theorem · proved theorem | [`CF10SourceRowIdentity`](../lean/PaperTargets/SmoothSources.lean#L72) | [LP11](../PROOF_NOTES.md#lp11) | V.ROWS, J05 |
| [`thue_divisor_inventory`](../lean/PaperProofs/ResultantDivisors.lean#L100) | theorem · proved theorem | [`CF15ThueDivisorInventory`](../lean/PaperTargets/ResultantDivisors.lean#L47) | [LP18](../PROOF_NOTES.md#lp18) | A.DIVISORS |
| [`two_linear_levels`](../lean/PaperProofs/LowFactorLevels.lean#L183) | theorem · proved theorem | [`CF15TwoLinearLevels`](../lean/PaperTargets/LowFactorLevels.lean#L49) | [LP17](../PROOF_NOTES.md#lp17) | A.LOW_COUNT |
| [`two_quadratic_levels`](../lean/PaperProofs/LowFactorLevels.lean#L209) | theorem · proved theorem | [`CF15TwoQuadraticLevels`](../lean/PaperTargets/LowFactorLevels.lean#L61) | [LP17](../PROOF_NOTES.md#lp17) | A.LOW_COUNT |
| [`uniform_coarse_factor_height`](../lean/PaperProofs/CoarseFactors.lean#L117) | theorem · proved theorem | [`CF05UniformCoarseFactorHeight`](../lean/PaperTargets/CoarseFactors.lean#L34) | [LP09](../PROOF_NOTES.md#lp09) | STD.FACTOR_HEIGHT, C.FACTOR |
| [`uniform_primitive_factor_cover`](../lean/PaperProofs/FactorInventory.lean#L129) | theorem · proved theorem | [`CF05UniformPrimitiveFactorCover`](../lean/PaperTargets/FactorInventory.lean#L27) | [LP09](../PROOF_NOTES.md#lp09) | STD.FACTOR_HEIGHT, C.FACTOR |
| [`unrounded_slack`](../lean/PaperProofs/ExactProfiles.lean#L107) | theorem · proved theorem | [`CF16UnroundedSlack`](../lean/PaperTargets/ExactProfiles.lean#L48) | [LP05](../PROOF_NOTES.md#lp05) | O.ENVELOPE, O.SLACK |
| [`unrounded_strict_constraints`](../lean/PaperProofs/ExactProfiles.lean#L156) | theorem · proved theorem | [`CF16UnroundedStrictConstraints`](../lean/PaperTargets/ExactProfiles.lean#L61) | [LP05](../PROOF_NOTES.md#lp05) | O.ENVELOPE, O.SLACK |

## Historical bindings and joins

The disposition records what became of each earlier contract. The frozen data also names the implementing, replacement and consuming declarations. Seven literal contracts are unused on the selected route.

| Contract | Selected disposition | Producing steps | Consuming steps |
| --- | --- | --- | --- |
| `DEF.POP` · Original positive population | selected route supported | [LP01](../PROOF_NOTES.md#lp01) | [LP23](../PROOF_NOTES.md#lp23), [LP24](../PROOF_NOTES.md#lp24) |
| `DEF.SOURCE` · Canonical source | selected route supported | [LP01](../PROOF_NOTES.md#lp01) | [LP08](../PROOF_NOTES.md#lp08), [LP21](../PROOF_NOTES.md#lp21), [LP23](../PROOF_NOTES.md#lp23) |
| `DEF.RATIO` · Rational coordinates | selected route supported | [LP01](../PROOF_NOTES.md#lp01) | [LP09](../PROOF_NOTES.md#lp09), [LP18](../PROOF_NOTES.md#lp18), [LP20](../PROOF_NOTES.md#lp20) |
| `DEF.BOX` · Shell, scales and source inventory | selected route supported | [LP04](../PROOF_NOTES.md#lp04), [LP06](../PROOF_NOTES.md#lp06) | [LP06](../PROOF_NOTES.md#lp06), [LP20](../PROOF_NOTES.md#lp20), [LP22](../PROOF_NOTES.md#lp22) |
| `DEF.PROFILE` · Profile and exponent conventions | selected route supported | [LP05](../PROOF_NOTES.md#lp05) | [LP05](../PROOF_NOTES.md#lp05), [LP08](../PROOF_NOTES.md#lp08), [LP13](../PROOF_NOTES.md#lp13), [LP20](../PROOF_NOTES.md#lp20) |
| `DEF.MINOR` · One chart-specific integer minor | selected route supported | [LP11](../PROOF_NOTES.md#lp11), [LP13](../PROOF_NOTES.md#lp13) | [LP11](../PROOF_NOTES.md#lp11), [LP13](../PROOF_NOTES.md#lp13) |
| `DEF.GRAPH` · Graph, homogeneous forms and levels | selected route supported | [LP13](../PROOF_NOTES.md#lp13), [LP14](../PROOF_NOTES.md#lp14), [LP15](../PROOF_NOTES.md#lp15) | [LP14](../PROOF_NOTES.md#lp14), [LP15](../PROOF_NOTES.md#lp15), [LP18](../PROOF_NOTES.md#lp18) |
| `EXT.R` · Reuss source input | unused literal replaced on selected route | [LP06](../PROOF_NOTES.md#lp06), [LP08](../PROOF_NOTES.md#lp08) | — |
| `EXT.T` · Stewart source input | accepted published external boundary | [LP00](../PROOF_NOTES.md#lp00) | [LP03](../PROOF_NOTES.md#lp03), [LP17](../PROOF_NOTES.md#lp17) |
| `STD.BEZOUT` · Projective intersection bounds | unused literal replaced on selected route | [LP09](../PROOF_NOTES.md#lp09), [LP17](../PROOF_NOTES.md#lp17) | [LP09](../PROOF_NOTES.md#lp09), [LP17](../PROOF_NOTES.md#lp17), [LP19](../PROOF_NOTES.md#lp19) |
| `STD.FACTOR_HEIGHT` · Fixed-degree factor and coefficient heights | selected route supported | [LP09](../PROOF_NOTES.md#lp09), [LP14](../PROOF_NOTES.md#lp14) | [LP09](../PROOF_NOTES.md#lp09), [LP14](../PROOF_NOTES.md#lp14) |
| `STD.PRIMES` · Controlled finite prime lists | selected route supported | [LP10](../PROOF_NOTES.md#lp10) | [LP10](../PROOF_NOTES.md#lp10) |
| `STD.FP` · Finite-field polynomial zero bound | selected route supported | [LP10](../PROOF_NOTES.md#lp10) | [LP10](../PROOF_NOTES.md#lp10), [LP20](../PROOF_NOTES.md#lp20) |
| `STD.IMPLICIT` · Integral one-parameter lifting | selected route supported | [LP11](../PROOF_NOTES.md#lp11) | [LP11](../PROOF_NOTES.md#lp11) |
| `STD.CB` · Finite determinant expansion | selected route supported | [LP11](../PROOF_NOTES.md#lp11) | [LP11](../PROOF_NOTES.md#lp11) |
| `STD.REAL` · Real divided-difference estimate | selected route supported | [LP12](../PROOF_NOTES.md#lp12) | [LP12](../PROOF_NOTES.md#lp12) |
| `STD.LINEAR` · Integer row-space/null-vector facts | selected route supported | [LP08](../PROOF_NOTES.md#lp08), [LP13](../PROOF_NOTES.md#lp13) | [LP08](../PROOF_NOTES.md#lp08), [LP13](../PROOF_NOTES.md#lp13) |
| `STD.SYLVESTER` · Homogeneous resultant identities | selected route supported | [LP15](../PROOF_NOTES.md#lp15) | [LP15](../PROOF_NOTES.md#lp15) |
| `STD.POLYABC` · Axis-sensitive polynomial root support | selected route supported | [LP16](../PROOF_NOTES.md#lp16) | [LP16](../PROOF_NOTES.md#lp16) |
| `STD.DIVISOR` · Uniform divisor growth | selected route supported | [LP18](../PROOF_NOTES.md#lp18) | [LP18](../PROOF_NOTES.md#lp18) |
| `STD.ASYMPTOTIC` · Elementary analytic assembly | selected route supported | [LP02](../PROOF_NOTES.md#lp02), [LP03](../PROOF_NOTES.md#lp03), [LP22](../PROOF_NOTES.md#lp22), [LP23](../PROOF_NOTES.md#lp23), [LP24](../PROOF_NOTES.md#lp24) | [LP21](../PROOF_NOTES.md#lp21), [LP22](../PROOF_NOTES.md#lp22), [LP23](../PROOF_NOTES.md#lp23), [LP24](../PROOF_NOTES.md#lp24) |
| `S.NORMAL` · Normal-form equivalence | selected route supported | [LP01](../PROOF_NOTES.md#lp01) | [LP01](../PROOF_NOTES.md#lp01) |
| `S.COPRIME` · Cross-endpoint coprimality | selected route supported | [LP01](../PROOF_NOTES.md#lp01) | [LP01](../PROOF_NOTES.md#lp01), [LP02](../PROOF_NOTES.md#lp02), [LP03](../PROOF_NOTES.md#lp03) |
| `S.PAIR` · Starts and canonical sources | selected route supported | [LP01](../PROOF_NOTES.md#lp01) | [LP01](../PROOF_NOTES.md#lp01), [LP23](../PROOF_NOTES.md#lp23) |
| `S.INJECT` · Source-to-ratio injection | selected route supported | [LP01](../PROOF_NOTES.md#lp01) | [LP09](../PROOF_NOTES.md#lp09), [LP18](../PROOF_NOTES.md#lp18) |
| `B.KFIX` · Fixed-kernel counting fibre | selected route supported | [LP02](../PROOF_NOTES.md#lp02) | [LP02](../PROOF_NOTES.md#lp02) |
| `B.KSMALL` · Small kernel product | selected route supported | [LP02](../PROOF_NOTES.md#lp02) | [LP21](../PROOF_NOTES.md#lp21) |
| `B.MFIX` · Fixed-multiplier counting fibre | selected route supported | [LP03](../PROOF_NOTES.md#lp03) | [LP03](../PROOF_NOTES.md#lp03), [LP14](../PROOF_NOTES.md#lp14) |
| `B.MSMALL` · Small multiplier product | selected route supported | [LP03](../PROOF_NOTES.md#lp03) | [LP21](../PROOF_NOTES.md#lp21) |
| `B.PARTITION` · Paid sets versus residual set | discharged in enclosing proof | [LP21](../PROOF_NOTES.md#lp21) | [LP21](../PROOF_NOTES.md#lp21) |
| `B.SCALES` · Actual-to-nominal size comparison | selected route supported | [LP01](../PROOF_NOTES.md#lp01), [LP04](../PROOF_NOTES.md#lp04), [LP07](../PROOF_NOTES.md#lp07) | [LP04](../PROOF_NOTES.md#lp04), [LP07](../PROOF_NOTES.md#lp07) |
| `B.PROFILE` · Residual profile domain | selected route supported | [LP04](../PROOF_NOTES.md#lp04), [LP07](../PROOF_NOTES.md#lp07) | [LP08](../PROOF_NOTES.md#lp08), [LP20](../PROOF_NOTES.md#lp20) |
| `B.INVENTORY` · Dyadic box cover | discharged in enclosing proof | [LP22](../PROOF_NOTES.md#lp22) | [LP22](../PROOF_NOTES.md#lp22) |
| `O.ENVELOPE` · Real-profile envelope | selected route supported | [LP05](../PROOF_NOTES.md#lp05) | [LP05](../PROOF_NOTES.md#lp05) |
| `O.SLACK` · Positive prime exponent and strict slack | selected route supported | [LP05](../PROOF_NOTES.md#lp05) | [LP05](../PROOF_NOTES.md#lp05) |
| `O.ROUND` · Ceiling and scale comparison | selected route supported | [LP05](../PROOF_NOTES.md#lp05) | [LP10](../PROOF_NOTES.md#lp10), [LP13](../PROOF_NOTES.md#lp13), [LP20](../PROOF_NOTES.md#lp20) |
| `C.REUSS` · Source-faithful Reuss application | selected route supported | [LP06](../PROOF_NOTES.md#lp06), [LP07](../PROOF_NOTES.md#lp07), [LP08](../PROOF_NOTES.md#lp08) | [LP20](../PROOF_NOTES.md#lp20) |
| `C.FACTOR` · Factor instances and heights | selected route supported | [LP09](../PROOF_NOTES.md#lp09) | [LP20](../PROOF_NOTES.md#lp20) |
| `C.SINGULAR` · Singular-source count | selected route supported | [LP09](../PROOF_NOTES.md#lp09) | [LP20](../PROOF_NOTES.md#lp20) |
| `C.CHART` · Bounded chart localisation | selected route supported | [LP12](../PROOF_NOTES.md#lp12) | [LP12](../PROOF_NOTES.md#lp12), [LP13](../PROOF_NOTES.md#lp13) |
| `P.WITNESS` · Uniform nonzero witness | selected route supported | [LP10](../PROOF_NOTES.md#lp10) | [LP10](../PROOF_NOTES.md#lp10) |
| `P.LIST` · Fixed-length candidate prime list | selected route supported | [LP10](../PROOF_NOTES.md#lp10) | [LP10](../PROOF_NOTES.md#lp10), [LP20](../PROOF_NOTES.md#lp20) |
| `P.ASSIGN` · Every source gets a good prime | selected route supported | [LP10](../PROOF_NOTES.md#lp10) | [LP20](../PROOF_NOTES.md#lp20) |
| `P.LABELS` · O(T) smooth labels per factor | selected route supported | [LP10](../PROOF_NOTES.md#lp10) | [LP20](../PROOF_NOTES.md#lp20) |
| `V.ROWS` · Integer/rational row identity | selected route supported | [LP11](../PROOF_NOTES.md#lp11) | [LP11](../PROOF_NOTES.md#lp11), [LP13](../PROOF_NOTES.md#lp13) |
| `V.SERIES` · Integral smooth parametrisation | selected route supported | [LP11](../PROOF_NOTES.md#lp11) | [LP11](../PROOF_NOTES.md#lp11) |
| `V.FINITE` · Generic eight-series divisibility | selected route supported | [LP11](../PROOF_NOTES.md#lp11) | [LP11](../PROOF_NOTES.md#lp11) |
| `V.INTEGER` · p^28 divides the source minor | selected route supported | [LP11](../PROOF_NOTES.md#lp11) | [LP13](../PROOF_NOTES.md#lp13) |
| `R.MIXED` · All five real mixed terms | selected route supported | [LP12](../PROOF_NOTES.md#lp12) | [LP12](../PROOF_NOTES.md#lp12) |
| `R.SCALES` · Restore both integer scales | selected route supported | [LP12](../PROOF_NOTES.md#lp12) | [LP12](../PROOF_NOTES.md#lp12) |
| `R.BOUND` · Real bound for the selected minor | selected route supported | [LP12](../PROOF_NOTES.md#lp12) | [LP13](../PROOF_NOTES.md#lp13) |
| `O.ABSORB` · Uniform strict integer squeeze | selected route supported | [LP05](../PROOF_NOTES.md#lp05) | [LP13](../PROOF_NOTES.md#lp13) |
| `D.ZERO` · All eight-row minors vanish | selected route supported | [LP13](../PROOF_NOTES.md#lp13) | [LP13](../PROOF_NOTES.md#lp13) |
| `D.RELATION` · One relation for the whole class | selected route supported | [LP13](../PROOF_NOTES.md#lp13) | [LP14](../PROOF_NOTES.md#lp14) |
| `D.HEIGHT` · Polynomial height of second relation | selected route supported | [LP13](../PROOF_NOTES.md#lp13) | [LP14](../PROOF_NOTES.md#lp14) |
| `G.PROPER` · Generic proper-intersection lemma | unused literal replaced on selected route | [LP19](../PROOF_NOTES.md#lp19) | — |
| `G.BIDEGREE` · Generic inherited bidegree | unused literal replaced on selected route | [LP14](../PROOF_NOTES.md#lp14) | — |
| `A.NORMAL` · Low-bidegree graph/ruling normal form | selected route supported | [LP14](../PROOF_NOTES.md#lp14) | [LP14](../PROOF_NOTES.md#lp14), [LP19](../PROOF_NOTES.md#lp19) |
| `A.RULINGS` · Uniform arithmetic ruling count | selected route supported | [LP02](../PROOF_NOTES.md#lp02), [LP03](../PROOF_NOTES.md#lp03), [LP14](../PROOF_NOTES.md#lp14) | [LP19](../PROOF_NOTES.md#lp19) |
| `A.RESULTANT` · Positive resultant and evaluated gcd | selected route supported | [LP15](../PROOF_NOTES.md#lp15) | [LP15](../PROOF_NOTES.md#lp15), [LP18](../PROOF_NOTES.md#lp18) |
| `A.PULLBACK` · Exact source pullback and signs | selected route supported | [LP15](../PROOF_NOTES.md#lp15) | [LP15](../PROOF_NOTES.md#lp15) |
| `A.CONTENT` · Corrected content and reduced level | selected route supported | [LP15](../PROOF_NOTES.md#lp15) | [LP18](../PROOF_NOTES.md#lp18) |
| `A.DISPATCH` · Pullback factor dispatcher | selected route supported | [LP16](../PROOF_NOTES.md#lp16) | [LP17](../PROOF_NOTES.md#lp17) |
| `A.THUE` · Admissible factor-level Thue count | selected route supported | [LP17](../PROOF_NOTES.md#lp17) | [LP18](../PROOF_NOTES.md#lp18) |
| `A.LOW_DISJOINT` · Low-degree level curves have no common component | selected route supported | [LP16](../PROOF_NOTES.md#lp16) | [LP17](../PROOF_NOTES.md#lp17) |
| `A.LOW_COUNT` · Low-degree level-pair count | selected route supported | [LP17](../PROOF_NOTES.md#lp17) | [LP17](../PROOF_NOTES.md#lp17), [LP18](../PROOF_NOTES.md#lp18) |
| `A.DIVISORS` · Uniform divisor-level budget | selected route supported | [LP18](../PROOF_NOTES.md#lp18) | [LP18](../PROOF_NOTES.md#lp18) |
| `A.HEIGHT` · Graph resultant height | selected route supported | [LP15](../PROOF_NOTES.md#lp15), [LP18](../PROOF_NOTES.md#lp18) | [LP18](../PROOF_NOTES.md#lp18) |
| `A.GRAPH_SMALL` · Uniform nonconstant graph count | selected route supported | [LP18](../PROOF_NOTES.md#lp18) | [LP19](../PROOF_NOTES.md#lp19) |
| `A.COMPONENT` · Generic low-bidegree component count | selected route supported | [LP19](../PROOF_NOTES.md#lp19) | [LP20](../PROOF_NOTES.md#lp20) |
| `I.PROPER` · Proper-intersection class application | unused literal replaced on selected route | [LP19](../PROOF_NOTES.md#lp19) | — |
| `I.COMMON` · Common-component application on F | unused literal replaced on selected route | [LP19](../PROOF_NOTES.md#lp19) | — |
| `I.CASES` · Once-per-factor accounting split | unused literal replaced on selected route | [LP20](../PROOF_NOTES.md#lp20) | — |
| `I.RAW` · Complete raw box inventory | selected route supported | [LP20](../PROOF_NOTES.md#lp20) | [LP20](../PROOF_NOTES.md#lp20), [LP21](../PROOF_NOTES.md#lp21) |
| `I.ABSORBED` · Absorb component and singular costs | selected route supported | [LP20](../PROOF_NOTES.md#lp20), [LP21](../PROOF_NOTES.md#lp21) | [LP22](../PROOF_NOTES.md#lp22) |
| `Z.SHELL` · Full shell count | selected route supported | [LP21](../PROOF_NOTES.md#lp21), [LP22](../PROOF_NOTES.md#lp22) | [LP23](../PROOF_NOTES.md#lp23) |
| `Z.NAT` · Positive natural-cutoff theorem | selected route supported | [LP23](../PROOF_NOTES.md#lp23) | [LP24](../PROOF_NOTES.md#lp24) |
| `Z.REAL` · Real-cutoff manuscript adapter | selected route supported | [LP24](../PROOF_NOTES.md#lp24) | — |
| `J01` · Original population | selected route supported | [LP01](../PROOF_NOTES.md#lp01), [LP23](../PROOF_NOTES.md#lp23) | [LP23](../PROOF_NOTES.md#lp23), [LP24](../PROOF_NOTES.md#lp24) |
| `J02` · Actual box to analytic profile | selected route supported | [LP04](../PROOF_NOTES.md#lp04), [LP07](../PROOF_NOTES.md#lp07) | [LP08](../PROOF_NOTES.md#lp08), [LP20](../PROOF_NOTES.md#lp20) |
| `J03` · One original cover | selected route supported | [LP06](../PROOF_NOTES.md#lp06), [LP08](../PROOF_NOTES.md#lp08), [LP12](../PROOF_NOTES.md#lp12), [LP20](../PROOF_NOTES.md#lp20) | [LP20](../PROOF_NOTES.md#lp20) |
| `J04` · Uniform prime family | selected route supported | [LP10](../PROOF_NOTES.md#lp10) | [LP20](../PROOF_NOTES.md#lp20) |
| `J05` · One integer minor | selected route supported | [LP11](../PROOF_NOTES.md#lp11), [LP12](../PROOF_NOTES.md#lp12), [LP13](../PROOF_NOTES.md#lp13) | [LP13](../PROOF_NOTES.md#lp13) |
| `J06` · Whole class | selected route supported | [LP13](../PROOF_NOTES.md#lp13) | [LP14](../PROOF_NOTES.md#lp14) |
| `J07` · Geometric branch | selected route supported | [LP19](../PROOF_NOTES.md#lp19), [LP20](../PROOF_NOTES.md#lp20) | [LP20](../PROOF_NOTES.md#lp20) |
| `J08` · Graph input | selected route supported | [LP13](../PROOF_NOTES.md#lp13), [LP14](../PROOF_NOTES.md#lp14), [LP15](../PROOF_NOTES.md#lp15) | [LP19](../PROOF_NOTES.md#lp19) |
| `J09` · Arithmetic budget | selected route supported | [LP15](../PROOF_NOTES.md#lp15), [LP16](../PROOF_NOTES.md#lp16), [LP17](../PROOF_NOTES.md#lp17), [LP18](../PROOF_NOTES.md#lp18) | [LP18](../PROOF_NOTES.md#lp18) |
| `J10` · Component inventory | selected route supported | [LP19](../PROOF_NOTES.md#lp19), [LP20](../PROOF_NOTES.md#lp20) | [LP20](../PROOF_NOTES.md#lp20), [LP21](../PROOF_NOTES.md#lp21) |
| `J11` · Global uniformity | selected route supported | [LP08](../PROOF_NOTES.md#lp08), [LP20](../PROOF_NOTES.md#lp20), [LP21](../PROOF_NOTES.md#lp21), [LP22](../PROOF_NOTES.md#lp22), [LP23](../PROOF_NOTES.md#lp23) | [LP23](../PROOF_NOTES.md#lp23), [LP24](../PROOF_NOTES.md#lp24) |
| `J12` · Manuscript endpoint | selected route supported | [LP01](../PROOF_NOTES.md#lp01), [LP23](../PROOF_NOTES.md#lp23), [LP24](../PROOF_NOTES.md#lp24) | [LP24](../PROOF_NOTES.md#lp24) |
| `P0365Subquarter.original_shell_source_count` · original_shell_source_count | selected final target supported | [LP22](../PROOF_NOTES.md#lp22) | — |
| `P0365Subquarter.natural_pair_count` · natural_pair_count | selected final target supported | [LP23](../PROOF_NOTES.md#lp23) | — |
| `P0365Subquarter.real_pair_count` · real_pair_count | selected final target supported | [LP24](../PROOF_NOTES.md#lp24) | — |

Two annotations qualify the inherited contract wording.

- `DEF.BOX` — The carried source claim mentions a strict lower manuscript endpoint. That describes the earlier manuscript: current section3.3 and LP04 both use inclusive x <= n <= 2x, as does the selected Lean box. No current endpoint discrepancy remains.
- `STD.CB` — The historical Cauchy-Binet label is retained as an identifier. Current section6.2 and LP11 follow the actual monic-remainder/Vandermonde implementation; the row remains a sufficient scope or route variant.
