# Mission clusters and inter-cluster dependencies

## Cluster identification

Mission membership is determined from the server `created_at` timestamp in UTC,
not from the Lean declaration name. Names are not reliable: in particular, the
KN wave contains several declarations whose names begin with `MTT`.

The 1,386 theorem/definition records currently indexed in
`.server-sync/graph.json` occupy three disjoint creation windows:

| Cluster | Inclusive UTC creation window | Indexed records |
|---|---|---:|
| FLT | `2026-09-05T04:28:24.773853Z` through `2026-09-05T04:31:07.012926Z` | 1,107 |
| MTT | `2026-09-05T21:58:59.591522Z` through `2026-09-08T08:05:20.576447Z` | 109 |
| KN | `2026-09-17T06:41:45.397016Z` through `2026-09-25T15:04:44.381775Z` | 170 |

There are no indexed records in the two intervening gaps. A record outside
these inclusive windows should be treated as unclassified until the windows
are deliberately revised; it should not be classified from its name.

The FLT-to-MTT gap is 17 hours, 27 minutes, 52.578596 seconds. The MTT-to-KN
gap is 8 days, 22 hours, 36 minutes, 24.820569 seconds.

As supporting checks, all 1,107 records in the FLT window carry the `flt` tag and
were created by `Claude`. The MTT window contains non-`MTT` names such as
`ProfiniteMeasure.ext_of_clopen_masses` and
`CuspForm.finrank_lower_bound_of_weighted_forms`. Conversely, the KN window
contains 20 declarations beginning with `MTT`.

## Dependency criterion

This report lists **direct local imports**, not transitive dependencies. For
each locally present MTT or KN theorem statement, imports were collected from:

1. its `Theorems/<cluster>/Thm_*.lean` statement file; and
2. its local proof file, `Solutions/<cluster>/Sol_*`.

Both `Theorems.<cluster>.Thm_*` and `Definitions.<cluster>.Def_*` imports count
as dependencies.
Repeated imports of the same target by the same source are deduplicated. The
labels `statement` and `proof` below say where the direct import occurs.

Twelve imported definition records were initially absent from `graph.json`;
their exact metadata was fetched from the server to classify them by the same
timestamp criterion. They have since been added to the local graph index, along
with the other locally present definitions. There are no unresolved local imports.

## MTT sources depending on FLT

There are 13 MTT source theorems, 30 distinct source-target pairs, and 18
distinct FLT targets.

- `MTT.Cohomology.centralCoinduced_parabolicH1_add_fixed_finrank_le`
  - `Gamma0CoeffCohomology` — definition; proof
  - `HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self` — theorem; proof
  - `HeckeEis.finrank_coeffH1par_top_add_le` — theorem; proof
  - `Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul` — theorem; proof
- `MTT.Cohomology.cuspForm_finrank_lower_bound_level_four_odd`
  - `ModularForm.finiteDimensional_of_isArithmetic` — theorem; proof
- `MTT.Cohomology.cuspForm_finrank_lower_bound_level_three`
  - `ModularForm.finiteDimensional_of_isArithmetic` — theorem; proof
- `MTT.Cohomology.exists_nonzero_cuspForm_weight_five_level_four`
  - `CuspForm.exists_gamma0_four_apply_eq_eta_pow_mul` — theorem; proof
- `MTT.Cohomology.exists_weighted_cusp_seeds_level_three`
  - `CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three` — theorem; proof
  - `CuspForm.exists_gamma0_apply_eq_eta_mul_pow_twentyfour` — theorem; proof
  - `EisensteinSeries.exists_modularForm_coe_eq_eisensteinG` — theorem; proof
  - `EisensteinSeries.qExpansion_eisensteinG_coeff` — theorem; proof
  - `ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul` — theorem; proof
- `MTT.Cohomology.exists_weighted_modular_seeds_level_four`
  - `ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd` — theorem; proof
- `MTT.Cohomology.finrank_modularForm_le_cuspForm_add_doubleCosets`
  - `ModularForm.finiteDimensional_of_isArithmetic` — theorem; proof
- `MTT.Cohomology.gammaOne_cuspForm_dimension_lower_bound`
  - `ModularForm.exists_linearIndependent_gamma1_dimFormula_le_card` — theorem; proof
  - `ModularForm.finiteDimensional_of_isArithmetic` — theorem; proof
- `MTT.Cohomology.parabolicH1_finrank_le_centralCoinduced`
  - `Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul` — theorem; proof
- `MTT.Cohomology.parabolicH1_finrank_le_level_three_numeric`
  - `CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three` — theorem; proof
- `MTT.Cohomology.parabolicH1_finrank_le_level_two`
  - `Gamma0CoeffCohomology` — definition; proof
  - `HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL` — theorem; proof
  - `HeckeEis_BinaryFormRep` — definition; proof
  - `ModularForm.finiteDimensional_of_isArithmetic` — theorem; proof
- `MTT.Cohomology.parabolicH1_finrank_le_levels_three_four_even`
  - `Gamma0CoeffCohomology` — definition; proof
  - `HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL` — theorem; proof
  - `HeckeEis_BinaryFormRep` — definition; proof
  - `ModularCurve_PeriodMap` — definition; proof
  - `ModularForm.finiteDimensional_of_isArithmetic` — theorem; proof
- `MTT.Cohomology.parabolicH1_finrank_le_weight_two`
  - `ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree` — theorem; proof
  - `ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup` — theorem; proof
  - `ModularCurve_PeriodMap` — definition; proof

## KN sources depending on FLT

There are 10 KN source theorems, 21 distinct source-target pairs, and 17
distinct FLT targets.

- `AdicCompletion.exists_domain_dvr_complete`
  - `Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv` — theorem; statement and proof
  - `IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete` — theorem; statement and proof
- `FrobeniusDensity.chebotarev_natural_density`
  - `LanglandsTunnell_TowerCounting` — definition; statement and proof
- `FrobeniusDensity.chebotarev_natural_density_core`
  - `LanglandsTunnell_TowerCounting` — definition; statement
- `HorizontalPadicL.eigenform_residualGaloisRepresentation_exists_v2`
  - `NumberField.exists_isFrobenius_lift_arithFrobAt` — theorem; proof
  - `NumberField.exists_lift_mem_inertia_integralClosure` — theorem; proof
  - `NumberField.exists_valuationSubring_eq_localization` — theorem; proof
  - `TaylorWiles_Primes` — definition; proof
  - `ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn` — theorem; proof
  - `ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem` — theorem; proof
- `HorizontalPadicL.ellipticCurve_attachedForm_isNormalizedEigenform`
  - `FLTPrelim_Modularity` — definition; statement and proof
- `HorizontalPadicL.ellipticCurve_eigenform_specialization_v2`
  - `FLTPrelim_Modularity` — definition; proof
- `HorizontalPadicL.minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo`
  - `CongruenceSubgroup.Gamma0_le_closure_T_union_setOf_dvd` — theorem; proof
  - `CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero` — theorem; proof
  - `FLTPrelim_Modularity` — definition; proof
  - `FreyPackage_ModMCarrier_Rescale` — definition; proof
  - `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` — theorem; proof
  - `ModularForm_HeckeOperator` — definition; proof
- `MTT.Eigenform.exists_adic_matrix_representation`
  - `GaloisRep_Residual` — definition; statement and proof
- `MTT.Eigenform.exists_continuous_localField_representation`
  - `GaloisRep_Residual` — definition; statement
- `MonoidAlgebra.isUnit_iff_augmentation_of_isPGroup_v2`
  - `MonoidAlgebra.isLocalRing_of_isPGroup` — theorem; statement and proof

## KN sources depending on MTT

There are 13 KN source theorems, 32 distinct source-target pairs, and 15
distinct MTT targets.

- `HorizontalPadicL.algebraicSymbol_eq_signedModularSymbol_v3`
  - `MTT_Measures` — definition; proof
- `HorizontalPadicL.corollary_5_17_v2`
  - `MTT.periods_exist` — theorem; proof
- `HorizontalPadicL.ellipticCurve_eigenform_specialization_v2`
  - `MTT.hasSum_heckePrime` — theorem; proof
- `HorizontalPadicL.minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo`
  - `MTT.exists_cuspForm_heckePrime_pos` — theorem; proof
  - `MTT.hasSum_heckePrime` — theorem; proof
- `MTT.Cohomology.eigenform_hecke_stable_period_lattice`
  - `MTT.Cohomology.base_change` — theorem; proof
  - `MTT.Cohomology.eigenclass_descent` — theorem; proof
  - `MTT.Cohomology.evaluation_lattice` — theorem; proof
  - `MTT.Cohomology.integral_finite_generation` — theorem; proof
  - `MTT.Cohomology.integration_map` — theorem; proof
  - `MTT.Cohomology.signed_evaluation` — theorem; proof
  - `MTT.Cohomology.signed_packet_multiplicity_one` — theorem; proof
  - `MTT.period_vanishing` — theorem; proof
  - `MTT_Cohomology` — definition; statement
- `MTT.Cohomology.eigenform_uniform_hecke_stable_period_lattice`
  - `MTT.Cohomology.base_change` — theorem; proof
  - `MTT.Cohomology.eigenclass_descent` — theorem; proof
  - `MTT.Cohomology.evaluation_lattice` — theorem; proof
  - `MTT.Cohomology.integral_finite_generation` — theorem; proof
  - `MTT.Cohomology.integration_map` — theorem; proof
  - `MTT.Cohomology.signed_evaluation` — theorem; proof
  - `MTT.Cohomology.signed_packet_multiplicity_one` — theorem; proof
  - `MTT.period_vanishing` — theorem; proof
  - `MTT_Cohomology` — definition; statement
- `MTT.Eigenform.coeff_isIntegral`
  - `MTT.hasSum_heckePrime` — theorem; proof
  - `MTT_Arithmetic` — definition; statement
- `MTT.Eigenform.heckeEigenvalue_isIntegral`
  - `MTT_Arithmetic` — definition; statement
- `MTT.Eigenform.hecke_recurrence`
  - `MTT.hasSum_heckePrime` — theorem; proof
  - `MTT_Arithmetic` — definition; statement
- `MTT.algebraicSymbol_horizontal_distribution`
  - `MTT_Measures` — definition; statement and proof
- `MTT.algebraicSymbol_horizontal_unitFiber_distribution`
  - `MTT_Measures` — definition; statement
- `MTT.criticalLValue_ne_zero_iff_modularSymbol_sum_ne_zero`
  - `MTT.birch_mellin_formula` — theorem; statement and proof
- `NumberField.not_dvd_discr_sup_of_not_dvd_discr`
  - `MTT_Arithmetic` — definition; statement and proof
