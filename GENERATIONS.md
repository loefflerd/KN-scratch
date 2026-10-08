# File generations

This is a fast, textual classification of every Lean file under `Definitions`, `Theorems`, and `Solutions` in this extracted tree, covering the FLT, MTT, and KN subprojects. No Lean command was run.

Definitions are individual dependency nodes. Each matching `Thm_...`/`Sol_...` pair is one node, whose dependencies are the union of the imports in the two files; both files are consequently listed in the same generation. Already-merged or otherwise unmatched theorem and solution files remain individual nodes.

Generation 1 means that a node has no imports from this extracted local filetree: its imports are only external baseline modules (`Mathlib...`, Lean’s core `Lean` module, or the separately vendored `TauCeti...` library), or it has no imports. For generation *n* > 1, all local dependency nodes have generation at most *n − 1*, and at least one has generation *n − 1*. Equivalently, the generation is one plus the maximum generation of the node’s local dependencies.

The parser reads textual `import` and `public import` commands, resolves module names from file paths, and ignores comments after an import. This intentionally does not reproduce Lean’s elaboration or transitive module-loading behavior.

Classified files: **1416 / 1416** in **1400** dependency nodes, including **16** theorem/solution pairs. Cycles found: **0**. Files with unresolved non-baseline imports: **0**.

## Summary

| Generation | Total files | FLT | MTT | KN |
|---:|---:|---:|---:|---:|
| 1 | 53 | 44 | 6 | 3 |
| 2 | 271 | 261 | 6 | 4 |
| 3 | 187 | 162 | 16 | 9 |
| 4 | 160 | 135 | 17 | 8 |
| 5 | 119 | 94 | 21 | 4 |
| 6 | 77 | 61 | 9 | 7 |
| 7 | 73 | 64 | 6 | 3 |
| 8 | 57 | 51 | 3 | 3 |
| 9 | 57 | 48 | 2 | 7 |
| 10 | 51 | 35 | 3 | 13 |
| 11 | 33 | 24 | 3 | 6 |
| 12 | 33 | 26 | 3 | 4 |
| 13 | 38 | 32 | 0 | 6 |
| 14 | 23 | 23 | 0 | 0 |
| 15 | 13 | 13 | 0 | 0 |
| 16 | 6 | 6 | 0 | 0 |
| 17 | 8 | 8 | 0 | 0 |
| 18 | 7 | 7 | 0 | 0 |
| 19 | 21 | 21 | 0 | 0 |
| 20 | 16 | 15 | 1 | 0 |
| 21 | 7 | 7 | 0 | 0 |
| 22 | 9 | 9 | 0 | 0 |
| 23 | 7 | 7 | 0 | 0 |
| 24 | 12 | 12 | 0 | 0 |
| 25 | 11 | 11 | 0 | 0 |
| 26 | 7 | 7 | 0 | 0 |
| 27 | 5 | 5 | 0 | 0 |
| 28 | 3 | 3 | 0 | 0 |
| 29 | 3 | 3 | 0 | 0 |
| 30 | 4 | 4 | 0 | 0 |
| 31 | 3 | 2 | 1 | 0 |
| 32 | 1 | 1 | 0 | 0 |
| 33 | 1 | 1 | 0 | 0 |
| 34 | 1 | 1 | 0 | 0 |
| 35 | 1 | 1 | 0 | 0 |
| 36 | 2 | 0 | 2 | 0 |
| 37 | 1 | 0 | 1 | 0 |
| 38 | 1 | 0 | 1 | 0 |
| 39 | 1 | 0 | 1 | 0 |
| 40 | 1 | 0 | 1 | 0 |
| 41 | 1 | 0 | 1 | 0 |
| 42 | 1 | 0 | 1 | 0 |
| 43 | 1 | 0 | 1 | 0 |
| 44 | 1 | 0 | 1 | 0 |
| 45 | 3 | 0 | 1 | 2 |
| 46 | 3 | 0 | 1 | 2 |
| 47 | 2 | 0 | 0 | 2 |
| 48 | 3 | 0 | 0 | 3 |
| 49 | 1 | 0 | 0 | 1 |
| 50 | 2 | 0 | 0 | 2 |
| 51 | 3 | 0 | 0 | 3 |
| 52 | 2 | 0 | 0 | 2 |
| 53 | 2 | 0 | 0 | 2 |
| 54 | 2 | 0 | 0 | 2 |
| 55 | 2 | 0 | 0 | 2 |
| 56 | 1 | 0 | 0 | 1 |
| 57 | 2 | 0 | 0 | 2 |

## Generation 1

- `Definitions/FLT/Def_AdicCompletionLocalRing.lean`
- `Definitions/FLT/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `Definitions/FLT/Def_AutomorphicForm_HyperbolicMeasure.lean`
- `Definitions/FLT/Def_AutomorphicForm_SiegelSetCover.lean`
- `Definitions/FLT/Def_CohCarrier_Level.lean`
- `Definitions/FLT/Def_Compat_Mathlib430.lean`
- `Definitions/FLT/Def_CuspForm_Petersson.lean`
- `Definitions/FLT/Def_DedekindDomain_AdicValuation_InlineSpecific.lean`
- `Definitions/FLT/Def_DualIsogenyAPI.lean`
- `Definitions/FLT/Def_EisensteinSeries_EisensteinG.lean`
- `Definitions/FLT/Def_EisensteinSeries_WeierstrassZeta.lean`
- `Definitions/FLT/Def_EllipticCurve_DivisionPolynomialOmega.lean`
- `Definitions/FLT/Def_EllipticCurve_FunctionFieldPullback.lean`
- `Definitions/FLT/Def_EllipticCurve_PointReduction.lean`
- `Definitions/FLT/Def_FLTPrelim_FreyPackage.lean`
- `Definitions/FLT/Def_FLTPrelim_GaloisRep.lean`
- `Definitions/FLT/Def_FLTPrelim_Modularity.lean`
- `Definitions/FLT/Def_FieldTheory_RatAlgClosureGalois.lean`
- `Definitions/FLT/Def_Gamma0HeckeOperatorHom.lean`
- `Definitions/FLT/Def_HahnSeries_Monodromy.lean`
- `Definitions/FLT/Def_HahnSeries_RamificationBound.lean`
- `Definitions/FLT/Def_ModularCurve_CuspSpace.lean`
- `Definitions/FLT/Def_ModularCurve_LaurentCoeff.lean`
- `Definitions/FLT/Def_ModularCurve_PeriodMap.lean`
- `Definitions/FLT/Def_ModularCurve_ProjectiveLine.lean`
- `Definitions/FLT/Def_ModularCurve_QExpansionDiff.lean`
- `Definitions/FLT/Def_ModularCurve_X0.lean`
- `Definitions/FLT/Def_ModularForm_AtkinLehnerDatum.lean`
- `Definitions/FLT/Def_ModularForm_EisensteinChiNegThree.lean`
- `Definitions/FLT/Def_ModularForm_HeckeOperator.lean`
- `Definitions/FLT/Def_P2M_Util.lean`
- `Definitions/FLT/Def_PeriodPair_Uniformization.lean`
- `Definitions/FLT/Def_TaylorWiles_Primes.lean`
- `Definitions/FLT/Def_WeierstrassCurve_FunctionFieldQuadratic.lean`
- `Definitions/FLT/Def_WeierstrassCurve_OddOrderSummingSet.lean`
- `Definitions/FLT/Def_WeierstrassCurve_RatPointMap_probe.lean`
- `Definitions/FLT/Def_WeierstrassCurve_VariableChangePointEquiv.lean`
- `Definitions/FLT/Def_WeierstrassCurve_Velu.lean`
- `Definitions/KN/Def_MonoidAlgebra_Augmentation.lean`
- `Definitions/MTT/Def_MTT_Arithmetic.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower.lean`
- `Theorems/FLT/Thm_ModularForm_exists_coe_eq_of_levelOne.lean`
- `Theorems/FLT/Thm_MonoidAlgebra_isLocalRing_of_isPGroup.lean`
- `Theorems/FLT/Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero.lean`
- `Theorems/KN/Thm_IsCyclotomicExtension_Rat_prime_dvd_discr_dvd_conductor.lean`
- `Theorems/KN/Thm_WeierstrassCurve_minimal_baseChange_completion.lean`
- `Theorems/MTT/Thm_CuspForm_finrank_lower_bound_of_weighted_forms.lean`
- `Theorems/MTT/Thm_MTT_coeff_eq_of_hecke_recurrence.lean`
- `Theorems/MTT/Thm_MTT_sum_integral_wirtinger_smul_fd_eq_zero.lean`
- `Theorems/MTT/Thm_PadicMeasure_compatible_disk_values_vanish_of_decay.lean`
- `Theorems/MTT/Thm_ProfiniteMeasure_ext_of_clopen_masses.lean`

## Generation 2

- `Definitions/FLT/Def_AlgebraicCurve_BaseChangeGalois.lean`
- `Definitions/FLT/Def_AlgebraicCurve_Differentials.lean`
- `Definitions/FLT/Def_AlgebraicCurve_DivisorPushPull.lean`
- `Definitions/FLT/Def_AlgebraicCurve_IsCurveOver.lean`
- `Definitions/FLT/Def_AlgebraicCurve_PlaceEvaluation.lean`
- `Definitions/FLT/Def_AlgebraicCurve_RatFuncPlaceInfty.lean`
- `Definitions/FLT/Def_AlgebraicCurve_RatFuncPlaces.lean`
- `Definitions/FLT/Def_AlgebraicCurve_Repartitions.lean`
- `Definitions/FLT/Def_AutomorphicForm_FundamentalDomainVolume.lean`
- `Definitions/FLT/Def_CuspForm_IntegralStructure.lean`
- `Definitions/FLT/Def_EllipticCurve_WeilPairingFun.lean`
- `Definitions/FLT/Def_EllipticCurve_ZeroComponentAt.lean`
- `Definitions/FLT/Def_FLTPrelim_Ramification.lean`
- `Definitions/FLT/Def_FreyPackage_ModMCarrier_Rescale.lean`
- `Definitions/FLT/Def_Gamma0CoeffCohomology.lean`
- `Definitions/FLT/Def_HeckeEis_BinaryFormRep.lean`
- `Definitions/FLT/Def_LanglandsTunnell_TowerCounting.lean`
- `Definitions/FLT/Def_ModularCurve_CanonicalDivisor.lean`
- `Definitions/FLT/Def_ModularCurve_ComplexPlaceDictionary.lean`
- `Definitions/FLT/Def_ModularCurve_GenusNumerics.lean`
- `Definitions/FLT/Def_ModularCurve_GeometricBaseChange.lean`
- `Definitions/FLT/Def_ModularCurve_HeckeAlgebraHom.lean`
- `Definitions/FLT/Def_ModularCurve_JqCoeff.lean`
- `Definitions/FLT/Def_ModularCurve_KroneckerTransport.lean`
- `Definitions/FLT/Def_ModularCurve_LevelNFunctionField.lean`
- `Definitions/FLT/Def_ModularCurve_ModularUnit.lean`
- `Definitions/FLT/Def_ModularCurve_PeriodMapBundled.lean`
- `Definitions/FLT/Def_ModularCurve_PhiGen.lean`
- `Definitions/FLT/Def_ModularCurve_QAdicPlace.lean`
- `Definitions/FLT/Def_ModularCurve_RouteBCoordRing.lean`
- `Definitions/FLT/Def_ProjectiveLineMatrixAction.lean`
- `Definitions/FLT/Def_WeierstrassCurve_EDSEngine.lean`
- `Definitions/FLT/Def_WeierstrassCurve_GenusOnePic0.lean`
- `Definitions/FLT/Def_WeierstrassCurve_RatPointHom.lean`
- `Definitions/FLT/Def_WeierstrassCurve_VeluOrderTwo.lean`
- `Definitions/FLT/Def_WeierstrassCurve_VeluQuotientMap.lean`
- `Definitions/FLT/Def_WeierstrassCurve_VeluQuotientOfSums.lean`
- `Definitions/KN/Def_KN_HorizontalPadicL.lean`
- `Definitions/KN/Def_MTT_EigenformCoefficientField.lean`
- `Definitions/MTT/Def_MTT_Cohomology.lean`
- `Definitions/MTT/Def_MTT_Measures.lean`
- `Solutions/FLT/Sol_ValuationSubring_exists_inertiaSubgroup_restrictNormal_eq.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_hasGoodReduction_baseChange_of_valuation_lt_one.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_reducePoint_some.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_valuation_le_one_of_equation.lean`
- `Theorems/FLT/Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.lean`
- `Theorems/FLT/Thm_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_degree_eq_sum.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Pic0_mk_eq_zero_iff.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Pic0_zsmul_mk.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_adicValuation_isTrivialOn.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_order_eq_ord.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_forall_ord_eq.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_of_orderMap.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_of_valuationSubring.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_isSeparable.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_ord_eq_one.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_min_ord_le_ord_add.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_add_eq_of_lt.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_algebraMap.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isIntegral_adjoin_map_algHom.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_kaehlerRankOne_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean`
- `Theorems/FLT/Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index.lean`
- `Theorems/FLT/Thm_Complex_exists_hasDerivAt_of_starConvex.lean`
- `Theorems/FLT/Thm_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt.lean`
- `Theorems/FLT/Thm_CongruenceSubgroup_Gamma0_le_closure_T_union_setOf_dvd.lean`
- `Theorems/FLT/Thm_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three.lean`
- `Theorems/FLT/Thm_CongruenceSubgroup_conj_T_zpow_mem_Gamma1_of_mem_sup_zpowers_neg_one.lean`
- `Theorems/FLT/Thm_CongruenceSubgroup_eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq.lean`
- `Theorems/FLT/Thm_CongruenceSubgroup_index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul.lean`
- `Theorems/FLT/Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean`
- `Theorems/FLT/Thm_CuspFormClass_isZeroAt_heckeT.lean`
- `Theorems/FLT/Thm_CuspFormClass_isZeroAt_heckeU.lean`
- `Theorems/FLT/Thm_CuspForm_exists_degeneracy_Gamma0.lean`
- `Theorems/FLT/Thm_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean`
- `Theorems/FLT/Thm_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean`
- `Theorems/FLT/Thm_EisensteinSeries_qExpansion_eisensteinG_coeff.lean`
- `Theorems/FLT/Thm_EisensteinSeries_sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow.lean`
- `Theorems/FLT/Thm_EisensteinWeightOne_e1Chi3IsModular.lean`
- `Theorems/FLT/Thm_Field_nonempty_ringHom_complex_of_countable.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_exists_prime_gt_and_quadratic_root.lean`
- `Theorems/FLT/Thm_HahnSeries_HasRamBound_add.lean`
- `Theorems/FLT/Thm_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot.lean`
- `Theorems/FLT/Thm_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq.lean`
- `Theorems/FLT/Thm_HahnSeries_isAlgClosed_rat.lean`
- `Theorems/FLT/Thm_HahnSeries_mem_puiseuxRamSubfield_iff.lean`
- `Theorems/FLT/Thm_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.lean`
- `Theorems/FLT/Thm_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv.lean`
- `Theorems/FLT/Thm_IntermediateField_finrank_fieldRange_le_of_adjoin_pair_eq_top.lean`
- `Theorems/FLT/Thm_IsAddCyclic_of_squarefree_natCard.lean`
- `Theorems/FLT/Thm_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq.lean`
- `Theorems/FLT/Thm_IsDedekindDomain_HeightOneSpectrum_valuation_eq_exp_neg_count.lean`
- `Theorems/FLT/Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete.lean`
- `Theorems/FLT/Thm_IsIntegral_mem_span_of_adjoin_simple_constants.lean`
- `Theorems/FLT/Thm_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.lean`
- `Theorems/FLT/Thm_KaehlerDifferential_D_ne_zero_of_transcendental.lean`
- `Theorems/FLT/Thm_KaehlerDifferential_span_D_eq_top_of_transcendental.lean`
- `Theorems/FLT/Thm_LaurentSeries_exists_algHom_comp_map_eq_single.lean`
- `Theorems/FLT/Thm_LinearMap_charpoly_of_finrank_eq_two.lean`
- `Theorems/FLT/Thm_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.lean`
- `Theorems/FLT/Thm_ModularCurve_CuspSpace_exists_normalForm.lean`
- `Theorems/FLT/Thm_ModularCurve_E4_cube_div_discriminant_smul.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_isIntegral_jqN.lean`
- `Theorems/FLT/Thm_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_count.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_eisInt_not_dvd_num.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_eisInt_series.lean`
- `Theorems/FLT/Thm_ModularCurve_aeval_jq_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_coeffMap_injective.lean`
- `Theorems/FLT/Thm_ModularCurve_coeffMap_qExpand.lean`
- `Theorems/FLT/Thm_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean`
- `Theorems/FLT/Thm_ModularCurve_cosetPoly_smul.lean`
- `Theorems/FLT/Thm_ModularCurve_dedekindPsi_prime.lean`
- `Theorems/FLT/Thm_ModularCurve_dedekindPsi_prime_pow.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_perm_gamma0_cosetReps.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_functionFieldGeneration_iff_full_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_functionFieldGeneration_of_prime.lean`
- `Theorems/FLT/Thm_ModularCurve_gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_qParam_heckeMatrix_smul.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_qParam_mul.lean`
- `Theorems/FLT/Thm_ModularCurve_laurentBaseChange_adjoin.lean`
- `Theorems/FLT/Thm_ModularCurve_laurentBaseChange_mono.lean`
- `Theorems/FLT/Thm_ModularCurve_le_dedekindPsi.lean`
- `Theorems/FLT/Thm_ModularCurve_map_intCast_pow_char_eq_qExpand.lean`
- `Theorems/FLT/Thm_ModularCurve_one_le_coeff_jq.lean`
- `Theorems/FLT/Thm_ModularCurve_order_coeffEmb.lean`
- `Theorems/FLT/Thm_ModularCurve_order_qExpand.lean`
- `Theorems/FLT/Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4.lean`
- `Theorems/FLT/Thm_ModularCurve_qExpansion_E6_eq_map_mk.lean`
- `Theorems/FLT/Thm_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.lean`
- `Theorems/FLT/Thm_ModularCurve_qParam_coeff_unique.lean`
- `Theorems/FLT/Thm_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime.lean`
- `Theorems/FLT/Thm_ModularCurve_relfinrank_modularFunctionField.lean`
- `Theorems/FLT/Thm_ModularCurve_tendsto_atImInfty_of_hasSum_qParam.lean`
- `Theorems/FLT/Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean`
- `Theorems/FLT/Thm_ModularFormClass_eq_of_forall_qCoeff_eq.lean`
- `Theorems/FLT/Thm_ModularFormClass_isBoundedAt_heckeT.lean`
- `Theorems/FLT/Thm_ModularFormClass_isBoundedAt_heckeU.lean`
- `Theorems/FLT/Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.lean`
- `Theorems/FLT/Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean`
- `Theorems/FLT/Thm_ModularForm_coeffHeckeT_comm.lean`
- `Theorems/FLT/Thm_ModularForm_coeffHeckeU_comm.lean`
- `Theorems/FLT/Thm_ModularForm_exists_cuspForm_mul_eq_of_analyticOrderAt_le.lean`
- `Theorems/FLT/Thm_ModularForm_exists_degeneracy_Gamma0.lean`
- `Theorems/FLT/Thm_ModularForm_exists_modularForm_mul_eq_of_analyticOrderAt_le_of_finiteIndex.lean`
- `Theorems/FLT/Thm_ModularForm_exists_qExpansion_eq_aeval_mul_pow_levelOne.lean`
- `Theorems/FLT/Thm_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem.lean`
- `Theorems/FLT/Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean`
- `Theorems/FLT/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean`
- `Theorems/FLT/Thm_ModularForm_isBoundedAtImInfty_heckeT.lean`
- `Theorems/FLT/Thm_ModularForm_isBoundedAtImInfty_heckeU.lean`
- `Theorems/FLT/Thm_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean`
- `Theorems/FLT/Thm_ModularForm_levelOne_weight_four_qCoeff_one.lean`
- `Theorems/FLT/Thm_ModularForm_levelOne_weight_six_qCoeff_one.lean`
- `Theorems/FLT/Thm_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant.lean`
- `Theorems/FLT/Thm_ModularForm_mdifferentiable_heckeT.lean`
- `Theorems/FLT/Thm_ModularForm_mdifferentiable_heckeU.lean`
- `Theorems/FLT/Thm_ModularForm_periodic_heckeT_comp_ofComplex.lean`
- `Theorems/FLT/Thm_ModularForm_periodic_heckeU_comp_ofComplex.lean`
- `Theorems/FLT/Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.lean`
- `Theorems/FLT/Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.lean`
- `Theorems/FLT/Thm_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.lean`
- `Theorems/FLT/Thm_Monoid_CoprodI_isTree_cosetGraph.lean`
- `Theorems/FLT/Thm_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime.lean`
- `Theorems/FLT/Thm_Nat_exists_squarefree_sq_add.lean`
- `Theorems/FLT/Thm_NumberField_exists_isFrobenius_lift_arithFrobAt.lean`
- `Theorems/FLT/Thm_NumberField_exists_lift_mem_inertia_integralClosure.lean`
- `Theorems/FLT/Thm_NumberField_exists_valuationSubring_eq_localization.lean`
- `Theorems/FLT/Thm_P2M_Dup_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal.lean`
- `Theorems/FLT/Thm_P2M_Dup_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.lean`
- `Theorems/FLT/Thm_PeriodPair_discriminant_ne_zero.lean`
- `Theorems/FLT/Thm_PeriodPair_jLattice_ofTau.lean`
- `Theorems/FLT/Thm_PeriodPair_jLattice_surjective.lean`
- `Theorems/FLT/Thm_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq.lean`
- `Theorems/FLT/Thm_Polynomial_irreducible_of_transitive_ringAut.lean`
- `Theorems/FLT/Thm_Polynomial_mem_range_of_eval_eq_const.lean`
- `Theorems/FLT/Thm_Polynomial_mem_range_of_unique_common_root.lean`
- `Theorems/FLT/Thm_PowerSeries_mem_range_map_of_monic_of_mul_mem_range.lean`
- `Theorems/FLT/Thm_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul.lean`
- `Theorems/FLT/Thm_SimpleGraph_exists_walkConnected_transversal_of_preconnected.lean`
- `Theorems/FLT/Thm_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.lean`
- `Theorems/FLT/Thm_Subgroup_card_orbitRelQuotient_mul_card_eq_index.lean`
- `Theorems/FLT/Thm_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty.lean`
- `Theorems/FLT/Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean`
- `Theorems/FLT/Thm_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic.lean`
- `Theorems/FLT/Thm_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem.lean`
- `Theorems/FLT/Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul.lean`
- `Theorems/FLT/Thm_UpperHalfPlane_qCoeff_heckeT.lean`
- `Theorems/FLT/Thm_UpperHalfPlane_qCoeff_heckeU.lean`
- `Theorems/FLT/Thm_UpperHalfPlane_qExpansion_coeff_mul_width.lean`
- `Theorems/FLT/Thm_UpperHalfPlane_qExpansion_prod.lean`
- `Theorems/FLT/Thm_ValuationSubring_exists_inertiaSubgroup_restrictNormal_eq.lean`
- `Theorems/FLT/Thm_Valuation_eq_comap_of_valuationSubring_le_comap.lean`
- `Theorems/FLT/Thm_WLight_exists_analyticOnNhd_div_of_monicRel.lean`
- `Theorems/FLT/Thm_WLight_levelOne_hauptmodul_package.lean`
- `Theorems/FLT/Thm_WLight_linearIndependent_complex_of_qExpansion_rational.lean`
- `Theorems/FLT/Thm_WLight_qExpansion_sigmaTransport_package.lean`
- `Theorems/FLT/Thm_WLight_weierstrassP_qExpansion_package.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_eq_XYIdeal_iff.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_CoordinateRing_natDegree_norm_eq_finsum_count.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_FunctionField_adjoin_X_Y_eq_top.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_FunctionField_eq_valuationSubring_of_X_not_mem.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_FunctionField_exists_valuation_eq_exp_natDegree_norm.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_card_ker_eq_max_natDegree.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_natDegree_parallelogram_law.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_vcInvFun_add.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_adjoin_yCoord_eq_top.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_deg_ofHeightOneSpectrum_eq_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_evalEval_psi_sq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_valuation_placeOf_smul_of_algEquiv.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_valuation_transEquiv_le.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_valuation_transEquiv_le_self.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_addEquiv_point_variableChange.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_X_cube_powerSeries.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_isUnit_discriminant_and_c6_sq_eq_mul_X_sq_powerSeries.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_fiberAdd_asymWeight_cleared_sixteen.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_fiberAdd_veluGx_cleared_four.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_hasGoodReduction_baseChange_of_valuation_lt_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_j_mem_of_a_mem.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_reducePoint_some.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_valuation_le_one_of_equation.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_velu2_secant_negAddY_cleared_identity.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_velu2_tangent_addX_cleared_identity.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`
- `Theorems/KN/Thm_MonoidAlgebra_isUnit_iff_augmentation_of_isPGroup_v2.lean`
- `Theorems/KN/Thm_NumberField_not_dvd_discr_sup_of_not_dvd_discr.lean`
- `Theorems/MTT/Thm_MTT_exists_cuspForm_heckePrime_pos.lean`
- `Theorems/MTT/Thm_MTT_exists_cuspForm_slash_gamma0.lean`
- `Theorems/MTT/Thm_MTT_hasSum_heckePrime.lean`
- `Theorems/MTT/Thm_PadicMeasure_colmez_r0_moment_extension.lean`

## Generation 3

- `Definitions/FLT/Def_AlgebraicCurve_AdelicIndex.lean`
- `Definitions/FLT/Def_AlgebraicCurve_CanonicalDivisor.lean`
- `Definitions/FLT/Def_AlgebraicCurve_Correspondence.lean`
- `Definitions/FLT/Def_AlgebraicCurve_PlaceCompletion.lean`
- `Definitions/FLT/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `Definitions/FLT/Def_AlgebraicCurve_RatFuncPlaceClassification.lean`
- `Definitions/FLT/Def_AlgebraicCurve_RegularDifferentials.lean`
- `Definitions/FLT/Def_AutomorphicForm_Gamma0FundamentalSet.lean`
- `Definitions/FLT/Def_EllipticCurve_FrobeniusTrace.lean`
- `Definitions/FLT/Def_HeckeEis_EichlerIntegral.lean`
- `Definitions/FLT/Def_ModularCurve_ArithmeticGalois.lean`
- `Definitions/FLT/Def_ModularCurve_CanonicalDivisorUniformizer.lean`
- `Definitions/FLT/Def_ModularCurve_ComplexPlaceDictionaryOf.lean`
- `Definitions/FLT/Def_ModularCurve_FibrePoly.lean`
- `Definitions/FLT/Def_ModularCurve_MazurStepThree.lean`
- `Definitions/FLT/Def_ModularCurve_ModuliPoint.lean`
- `Definitions/FLT/Def_ModularCurve_PrimCosetReps.lean`
- `Definitions/FLT/Def_ModularCurve_TateFormal.lean`
- `Definitions/FLT/Def_ModularForm_HeckeOperatorForms.lean`
- `Definitions/FLT/Def_WeierstrassCurve_FullKernelQuotient.lean`
- `Definitions/FLT/Def_WeierstrassCurve_GenusOnePlaceGateCentred.lean`
- `Definitions/FLT/Def_WeierstrassCurve_VeluPointMap.lean`
- `Definitions/FLT/Def_WeierstrassCurve_VeluPointMap2.lean`
- `Definitions/KN/Def_HorizontalPadicL_LocalEulerFactorDegree.lean`
- `Definitions/KN/Def_KN_HorizontalPadicLAux.lean`
- `Definitions/KN/Def_MTT_EigenformCoefficientPrime.lean`
- `Definitions/MTT/Def_MTT_Cohomology_Boundary.lean`
- `Definitions/MTT/Def_MTT_Cohomology_Integration.lean`
- `Definitions/MTT/Def_MTT_ParabolicCohomology.lean`
- `Solutions/FLT/Sol_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_reducePoint_some_add_some_of_not_le_one.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_reducePoint_some_eq_zero_iff.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_evalFun_add.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_evalFun_ne_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_evalFun_zsmul.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_evalAt_algebraMap.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_evalAt_mul.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_eq_zero_of_isIntegral_adjoin.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_natCast.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_restrict_ofAlgAut_smul.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_divisor_forall_eq_weightFloor.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_twelve_mul_eq_of_sum_ordDiff_eq.lean`
- `Theorems/FLT/Thm_CuspForm_exists_gamma0_apply_eq_eta_mul_pow_twentyfour.lean`
- `Theorems/FLT/Thm_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean`
- `Theorems/FLT/Thm_HahnSeries_hasRamBound_C.lean`
- `Theorems/FLT/Thm_HahnSeries_hasRamBound_natCast.lean`
- `Theorems/FLT/Thm_HahnSeries_hasRamBound_single_one.lean`
- `Theorems/FLT/Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj.lean`
- `Theorems/FLT/Thm_HeckeEis_binaryFormRepSL_neg_one_apply.lean`
- `Theorems/FLT/Thm_HeckeEis_coeffH1par_map_heckeT_comm.lean`
- `Theorems/FLT/Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_coeffH1par_map_ringHom.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_coeffH1par_semilinearMap_starRingEnd.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self.lean`
- `Theorems/FLT/Thm_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.lean`
- `Theorems/FLT/Thm_HeckeEis_finrank_coeffH1par_top_add_le.lean`
- `Theorems/FLT/Thm_HeckeEis_le_finrank_fixed_S_and_ST_binaryFormRepSL.lean`
- `Theorems/FLT/Thm_HeckeEis_linearIndependent_coeffH1par_map_rat_complex.lean`
- `Theorems/FLT/Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one.lean`
- `Theorems/FLT/Thm_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.lean`
- `Theorems/FLT/Thm_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul.lean`
- `Theorems/FLT/Thm_LinearMap_charpoly_eq_iff_of_finrank_eq_two.lean`
- `Theorems/FLT/Thm_LinearMap_trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq.lean`
- `Theorems/FLT/Thm_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_CuspSpace_normalFormCriterion.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_conj_injective.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_exists_galoisPerm.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_mem_range_coeffEmb_of_forall_coeffMap_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_mem_range_coeffEmb_qExpand_of_mem_inter.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_closure.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_deltaNorm.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_delta_pow_ne.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_onePoint.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_starK.lean`
- `Theorems/FLT/Thm_ModularCurve_aeval_jqN_toAdjoin.lean`
- `Theorems/FLT/Thm_ModularCurve_coeffEmb_injective.lean`
- `Theorems/FLT/Thm_ModularCurve_coeffEmb_jq.lean`
- `Theorems/FLT/Thm_ModularCurve_coeffEmb_jqN.lean`
- `Theorems/FLT/Thm_ModularCurve_coeffEmb_qExpand.lean`
- `Theorems/FLT/Thm_ModularCurve_coeff_jqModC_neg_one.lean`
- `Theorems/FLT/Thm_ModularCurve_coeff_jqModC_pow_of_lt.lean`
- `Theorems/FLT/Thm_ModularCurve_coeff_jqModC_pow_self.lean`
- `Theorems/FLT/Thm_ModularCurve_dedekindPsi_mul_of_coprime.lean`
- `Theorems/FLT/Thm_ModularCurve_dedekindPsi_pos.lean`
- `Theorems/FLT/Thm_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_finiteDimensional_adjoin_jqNModC.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqNModC_le.lean`
- `Theorems/FLT/Thm_ModularCurve_frobenius_identity_geom_unconditional.lean`
- `Theorems/FLT/Thm_ModularCurve_full_eq_of_prime.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_qParam_mul_laurent.lean`
- `Theorems/FLT/Thm_ModularCurve_laurent_qParam_coeff_unique.lean`
- `Theorems/FLT/Thm_ModularCurve_mem_range_qExpand_of_qTwist_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_minpoly_jqN_eq_toAdjoin.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_fixedPoints_S_cosets_Gamma0_eq_nuTwo.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_qInftyPlaceBar.lean`
- `Theorems/FLT/Thm_ModularCurve_order_jqModC.lean`
- `Theorems/FLT/Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional.lean`
- `Theorems/FLT/Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.lean`
- `Theorems/FLT/Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb.lean`
- `Theorems/FLT/Thm_ModularCurve_transcendental_jq.lean`
- `Theorems/FLT/Thm_ModularCurve_transcendental_jqModC.lean`
- `Theorems/FLT/Thm_ModularFormClass_heckeT_heckeT_comm.lean`
- `Theorems/FLT/Thm_ModularFormClass_heckeT_heckeU_comm.lean`
- `Theorems/FLT/Thm_ModularFormClass_heckeU_heckeU_comm.lean`
- `Theorems/FLT/Thm_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.lean`
- `Theorems/FLT/Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne.lean`
- `Theorems/FLT/Thm_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.lean`
- `Theorems/FLT/Thm_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic.lean`
- `Theorems/FLT/Thm_ModularForm_weierstrassP_torsion_qExpansion_package.lean`
- `Theorems/FLT/Thm_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_adicValuation_valuationSubring.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_adicValuation_le_one.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean`
- `Theorems/FLT/Thm_PeriodPair_isUniformization_toPoint.lean`
- `Theorems/FLT/Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat.lean`
- `Theorems/FLT/Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn.lean`
- `Theorems/FLT/Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime.lean`
- `Theorems/FLT/Thm_WLight_exists_mdifferentiable_div_of_monicRel.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_exists_zsmul_some_eq_some_baseChange.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_exists_infinitePlace_deg_eq_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_finiteDimensional_ratFunc_functionField.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_valuation_placeOf_neg_transEquiv_algebraMap.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_isCoprime_Phi_PsiSq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_reducePoint_some_add_some_of_not_le_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_reducePoint_some_eq_zero_iff.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_veluQuotient2_Delta_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_veluQuotient_j_mem_of_mem.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_veluX_oddOrderSummingSet_injOn_psi2Sq_roots.lean`
- `Theorems/FLT/Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree.lean`
- `Theorems/FLT/Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo.lean`
- `Theorems/KN/Thm_AdicCompletion_exists_domain_dvr_complete.lean`
- `Theorems/KN/Thm_FrobeniusDensity_chebotarev_natural_density.lean`
- `Theorems/KN/Thm_HorizontalPadicL_friedberg_hoffstein_quadratic_twist_nonzero_anyParity_v2.lean`
- `Theorems/KN/Thm_MTT_Eigenform_hecke_recurrence.lean`
- `Theorems/KN/Thm_MTT_Eigenform_nebentype_mem_ringOfIntegers.lean`
- `Theorems/KN/Thm_MTT_algebraicSymbol_horizontal_distribution.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_eigenclass_descent.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_evaluation_faithful.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_evaluation_lattice.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_integral_finite_generation.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_manin_generation.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_manin_generation_span.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_reflection_class.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_reflection_involutive.lean`
- `Theorems/MTT/Thm_MTT_birch_mellin_formula.lean`
- `Theorems/MTT/Thm_MTT_character_integral_of_disk_moments.lean`
- `Theorems/MTT/Thm_MTT_distribution_relation.lean`
- `Theorems/MTT/Thm_MTT_ordinary_centered_disk_bound.lean`
- `Theorems/MTT/Thm_MTT_ordinary_root_exists_unique.lean`

## Generation 4

- `Definitions/FLT/Def_AlgebraicCurve_DifferentialPushPull.lean`
- `Definitions/FLT/Def_AlgebraicCurve_FrobeniusEndo.lean`
- `Definitions/FLT/Def_AlgebraicCurve_LocalResidue.lean`
- `Definitions/FLT/Def_AlgebraicCurve_PoleDivisorPackage.lean`
- `Definitions/FLT/Def_AlgebraicCurve_RiemannRochRows.lean`
- `Definitions/FLT/Def_EllipticCurve_FrobeniusEndo.lean`
- `Definitions/FLT/Def_FreyPackage_GaloisRep.lean`
- `Definitions/FLT/Def_GaloisRep_Residual.lean`
- `Definitions/FLT/Def_HeckeGalois_EichlerShimura.lean`
- `Definitions/FLT/Def_Isogeny_ConditionalCurrency.lean`
- `Definitions/FLT/Def_ModularCurve_AtkinLehner.lean`
- `Definitions/FLT/Def_ModularCurve_HeckeOperator.lean`
- `Definitions/FLT/Def_ModularCurve_IgusaFunctionField.lean`
- `Definitions/FLT/Def_ModularCurve_JLinePlaces.lean`
- `Definitions/FLT/Def_ModularCurve_QAdicPlaceMod.lean`
- `Definitions/FLT/Def_ModularCurve_TatePoint.lean`
- `Definitions/FLT/Def_ModularCurve_X0ModL.lean`
- `Definitions/FLT/Def_ModularCurve_X1.lean`
- `Definitions/KN/Def_KN_SeededHorizontalPadicLFunctionV2B.lean`
- `Definitions/KN/Def_KN_SeededPrimeGaloisDataV2.lean`
- `Definitions/MTT/Def_MTT_FullParabolicCohomology.lean`
- `Definitions/MTT/Def_MTT_LevelOnePeriodRelations.lean`
- `Definitions/MTT/Def_MTT_NormalizedParabolicCocycles.lean`
- `Definitions/MTT/Def_MTT_PeriodPairing.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_reducePoint_some_add_some_of_le_one.lean`
- `Theorems/FLT/Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree.lean`
- `Theorems/FLT/Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_degree_eq_sum_support.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_evalFun_mul.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_evalFun_single_sub_single.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_evalAt_congr.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_inertiaDegAlong_comp.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_ell_le_degree_add_ellZero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_finiteAlong_comp.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_finiteAlong_of_surjective.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_finiteDimensional_lSpace.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_finiteDimensional_lSpace_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_indexOfSpecialty_eq_zero_of_genusReached.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isCurveOver_ratFunc.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_omegaSpace_finite_of_genusReached.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_separableAlong_of_charZero.lean`
- `Theorems/FLT/Thm_CuspForm_exists_gamma0_four_apply_eq_eta_pow_mul.lean`
- `Theorems/FLT/Thm_CuspForm_heckeTLin_comm.lean`
- `Theorems/FLT/Thm_CuspForm_heckeTLin_heckeULin_comm.lean`
- `Theorems/FLT/Thm_CuspForm_heckeULin_comm.lean`
- `Theorems/FLT/Thm_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEichlerIntegral_add.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEichlerIntegral_exists_sub_eq_const.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEichlerIntegral_slash.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEichlerIntegral_smul.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries.lean`
- `Theorems/FLT/Thm_HeckeEis_coeffH1par_binaryFormRepSL_eq_zero_of_odd.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_isEichlerIntegral.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_ne_zero_smul_eq_coeffH1par_map_int_rat.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_pairing_binaryForm_linePow.lean`
- `Theorems/FLT/Thm_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL.lean`
- `Theorems/FLT/Thm_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL.lean`
- `Theorems/FLT/Thm_Matrix_SpecialLinearGroup_nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne.lean`
- `Theorems/FLT/Thm_ModularCurve_CuspSpace_classification.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion.lean`
- `Theorems/FLT/Thm_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_PhiGenDescends_c_top.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_PhiGenDescends_poleOrderLE.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_evalAtJ_injective.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_evalSymm_of_splits.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_phiIrreducible_of_splits.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_press.lean`
- `Theorems/FLT/Thm_ModularCurve_card_projectiveLine_zmod.lean`
- `Theorems/FLT/Thm_ModularCurve_card_roots_fibrePoly_of_monic.lean`
- `Theorems/FLT/Thm_ModularCurve_dedekindPsi_of_squarefree.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_jNum_qParam.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_modularUnitSeries_inv_qParam.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_modularUnitSeries_qParam.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_smul_modularUnitSeries_qParam.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_and_isIntegral_of_mem_riemannRochSpace_weightFloor.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_jqNModC_mul.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData.lean`
- `Theorems/FLT/Thm_ModularCurve_laurentBaseChange_modularFunctionField.lean`
- `Theorems/FLT/Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull.lean`
- `Theorems/FLT/Thm_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_realizeOf_eq_div.lean`
- `Theorems/FLT/Thm_ModularForm_finiteDimensional_of_isArithmetic.lean`
- `Theorems/FLT/Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty.lean`
- `Theorems/FLT/Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean`
- `Theorems/FLT/Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.lean`
- `Theorems/FLT/Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_prime_pow_eq_one.lean`
- `Theorems/FLT/Thm_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem.lean`
- `Theorems/FLT/Thm_WLight_frickeFunction_modularity_package.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_Point_zsmul_y_mul_psi_cube.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_fibSet_finite.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_zsmul_genericPoint_good.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_reducePoint_some_add_some_of_le_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_sum_eq_zero_of_forall_mem_iff_smul_eq_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_veluGx_ne_zero_of_two_torsion.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean`
- `Theorems/KN/Thm_HorizontalPadicL_localEulerFactorDegreeTwo_iff_not_degreeBelowTwo.lean`
- `Theorems/KN/Thm_HorizontalPadicL_positiveDensityPrimeSet_infinite_v2.lean`
- `Theorems/KN/Thm_MTT_Eigenform_coefficientPrime_isPrime.lean`
- `Theorems/KN/Thm_MTT_Eigenform_p_mem_coefficientPrime.lean`
- `Theorems/KN/Thm_MTT_algebraicSymbol_horizontal_unitFiber_distribution.lean`
- `Theorems/KN/Thm_MTT_criticalLValue_ne_zero_iff_modularSymbol_sum_ne_zero.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_boundary_hecke_cusp_sum_at_one.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_cuspPrimitive_slash_relation.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_exists_parabolic_coinduced_cocycle.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_exists_weighted_cusp_seeds_level_three.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_integral_classes_span.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_integration_cochain_hecke_equivariant.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_integration_cochain_integral_class.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finiteDimensional.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_primeHecke_boundary_datum.lean`
- `Theorems/MTT/Thm_MTT_cusp_log_weighted_square_summable.lean`
- `Theorems/MTT/Thm_MTT_interpolation_conductor_one_of_moments.lean`
- `Theorems/MTT/Thm_MTT_interpolation_positive_conductor_of_moments.lean`
- `Theorems/MTT/Thm_MTT_measure_extension.lean`

## Generation 5

- `Definitions/FLT/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean`
- `Definitions/FLT/Def_AlgebraicCurve_FrobeniusEndoPic0.lean`
- `Definitions/FLT/Def_AlgebraicCurve_TateResidueCurrency.lean`
- `Definitions/FLT/Def_AlgebraicCurve_WeilOfKaehler.lean`
- `Definitions/FLT/Def_CuspForm_HeckeAlgebra.lean`
- `Definitions/FLT/Def_GaloisRep_ResidualEquiv.lean`
- `Definitions/FLT/Def_ModularCurve_CuspidalClass.lean`
- `Definitions/FLT/Def_ModularCurve_DegeneracyTower.lean`
- `Definitions/FLT/Def_ModularCurve_EigenformIdeal.lean`
- `Definitions/FLT/Def_ModularCurve_HeckeDifferential.lean`
- `Definitions/FLT/Def_ModularCurve_HeckeOperatorTotal.lean`
- `Definitions/FLT/Def_ModularCurve_IgusaFunctionFieldX1.lean`
- `Definitions/FLT/Def_ModularCurve_JZeroNaiveHeight.lean`
- `Definitions/FLT/Def_WeierstrassCurve_ReductionMap.lean`
- `Definitions/KN/Def_KN_SeedCyclotomicGaloisCharactersV3B.lean`
- `Definitions/KN/Def_KN_SeededThetaConstructionV2B.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_reducePoint_add.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ordDiff_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_SemilinearAut_ramificationIndex_smul.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.lean`
- `Theorems/FLT/Thm_CuspForm_finiteDimensional_of_isArithmetic.lean`
- `Theorems/FLT/Thm_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_exists_x_linePencil_frobEnd_mul_collision_sq.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_frobCharEqOnPoints_of_charEq_on_torsion_of_trace_ne_zero.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_frobCharEqOnPoints_of_charEq_on_torsion_of_trace_zero.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_kerDeg_frobEnd_one_one.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const.lean`
- `Theorems/FLT/Thm_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval.lean`
- `Theorems/FLT/Thm_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero.lean`
- `Theorems/FLT/Thm_HeckeEis_eichlerShimuraMap_eq_coeffH1parMk.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_induced_binaryFormRepSL_top.lean`
- `Theorems/FLT/Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral.lean`
- `Theorems/FLT/Thm_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral.lean`
- `Theorems/FLT/Thm_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne.lean`
- `Theorems/FLT/Thm_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne.lean`
- `Theorems/FLT/Thm_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount.lean`
- `Theorems/FLT/Thm_ModularCurve_Gamma0_index.lean`
- `Theorems/FLT/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_deg_jLinePlace1728.lean`
- `Theorems/FLT/Thm_ModularCurve_deg_jLinePlaceZero.lean`
- `Theorems/FLT/Thm_ModularCurve_evalAtJGen_injective.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_isFrickeAut_of_modularPolynomialData.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.lean`
- `Theorems/FLT/Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring.lean`
- `Theorems/FLT/Thm_ModularCurve_hasSum_jq_qParam.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily.lean`
- `Theorems/FLT/Thm_ModularCurve_jqModC_mem_intFormRatiosC.lean`
- `Theorems/FLT/Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_cuspInftyBar.lean`
- `Theorems/FLT/Thm_ModularCurve_qExpand_image_intFormRatiosC_subset.lean`
- `Theorems/FLT/Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq.lean`
- `Theorems/FLT/Thm_ModularForm_exists_gamma1_isIntegralQExp_eisenstein_four_six.lean`
- `Theorems/FLT/Thm_ModularForm_exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty.lean`
- `Theorems/FLT/Thm_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction.lean`
- `Theorems/FLT/Thm_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction.lean`
- `Theorems/FLT/Thm_WLight_frickeFunction_orbit_package.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_sub.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_ncard_fibSet.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_valuation_weilNum.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_pow_three_eq_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_sq_eq_neg_one.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_reducePoint_add.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero.lean`
- `Theorems/FLT/Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean`
- `Theorems/KN/Thm_HorizontalPadicL_seededFrobeniusClass_positiveDensity_v2.lean`
- `Theorems/KN/Thm_MTT_Eigenform_coefficientPrime_ne_bot.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_base_change.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_boundary_hecke_scalar_at_one.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_centralCoinduced_T_fixed_cusp_lower_bound.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_centralCoinduced_elliptic_dimensions.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_centralCoinduced_parabolicH1_add_fixed_finrank_le.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_cuspForm_finrank_lower_bound_level_three.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_cuspPrimitive_analytic_relations.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_exists_nonzero_cuspForm_weight_five_level_four.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_finrank_modularForm_le_cuspForm_add_doubleCosets.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_gammaOne_has_finset_complement.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_integral_class_character_law_infty.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_mixed_period_test_functions_local_equivariant.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_normalizedParabolic_finrank.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_centralCoinduced.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_level_one.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_periodDensity_integrableOn_tile.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_periodPairing_eq_sum_tiles.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_period_pairing_petersson_definite.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_period_reflected_cusp_form.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_principal_period_equivariant_primitive.lean`
- `Theorems/MTT/Thm_MTT_interpolation_of_moments.lean`

## Generation 6

- `Definitions/FLT/Def_GaloisRep_Adic.lean`
- `Definitions/FLT/Def_ModularCurve_CharLFrobeniusGeomLevel.lean`
- `Definitions/FLT/Def_ModularCurve_Eisenstein.lean`
- `Definitions/FLT/Def_ModularCurve_HeckeModule.lean`
- `Definitions/FLT/Def_ModularCurve_JZeroHeightForm.lean`
- `Definitions/FLT/Def_ModularCurve_PeriodLattice.lean`
- `Definitions/FLT/Def_ValuationSubring_ReduceAt.lean`
- `Definitions/FLT/Def_WeierstrassCurve_TorsionIntegral.lean`
- `Definitions/KN/Def_KN_SeededHorizontalCharacterRealizationV2B.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_galoisRepUnramifiedAt_of_hasGoodReduction.lean`
- `Theorems/FLT/Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_eq_one.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ordDiff_smul.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_deg_ne_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_genus_eq_genusFF.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_tateAgreement.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_tateChainRule.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_tateCommFinite.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean`
- `Theorems/FLT/Thm_CuspForm_finiteDimensional_Gamma0.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_det_frobPencilEnd_eq_zero_iff_dvd_kerDeg.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_of_torsion.lean`
- `Theorems/FLT/Thm_HeckeEis_coeffH1par_map_int_rat_injective.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle.lean`
- `Theorems/FLT/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.lean`
- `Theorems/FLT/Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_complexPlaceDictionaryOf.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_intSeriesC_mul_ne_of_gamma0Units_not_mem.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_genusFormula.lean`
- `Theorems/FLT/Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand.lean`
- `Theorems/FLT/Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant.lean`
- `Theorems/FLT/Thm_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean`
- `Theorems/FLT/Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand.lean`
- `Theorems/FLT/Thm_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty.lean`
- `Theorems/FLT/Thm_WLight_exists_levelFraction_of_stable_family.lean`
- `Theorems/FLT/Thm_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.lean`
- `Theorems/FLT/Thm_WLight_frickeFunction_intBaseChange.lean`
- `Theorems/FLT/Thm_WLight_levelN_structure_package.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_abelTheorem.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_valuation_weilFun.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_weilNum_ne_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_hasGoodReduction.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero.lean`
- `Theorems/KN/Thm_HorizontalPadicL_SeedCyclotomicGaloisCharacterDataV2_exists_fullOrder_value_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_algebraicSymbol_eq_signedModularSymbol_v3.lean`
- `Theorems/KN/Thm_HorizontalPadicL_eigenform_period_lattice_uniformly_integral_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_horizontalFiniteGroup_isPGroup_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_seedCyclotomicGaloisCharacters_exist_v4.lean`
- `Theorems/KN/Thm_PadicComplexInt_natCast_prime_mem_maximalIdeal_v2.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_boundary_packet_zero.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_centralCoinduced_fixed_dimensions_large_level.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_integral_class_character_law.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_integration_linear_map_exists.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_mixed_period_test_functions_cusp_decay_of_pos_level.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_mixed_period_test_functions_tile_integrable_of_pos_level.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_add_one_le_level_four.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_level_three_numeric.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_periodPairing_eq_transversal_integral_of_weight_ge_two.lean`

## Generation 7

- `Definitions/FLT/Def_EllipticCurve_TateModule.lean`
- `Definitions/FLT/Def_GaloisRep_LocalConditions.lean`
- `Definitions/FLT/Def_ModularCurve_MazurStepThreeInputs.lean`
- `Definitions/FLT/Def_ModularCurve_PeriodOf.lean`
- `Definitions/FLT/Def_WeierstrassCurve_ReduceHom.lean`
- `Definitions/KN/Def_KN_SeededHorizontalPadicLFunctionV3B.lean`
- `Definitions/KN/Def_KN_SeededThetaConstructionV3.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_mem_regularDiffs_iff.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_residueTraceCompletionCommute.lean`
- `Theorems/FLT/Thm_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_trace_det_frob_of_line_of_isotropic.lean`
- `Theorems/FLT/Thm_HeckeEis_eichlerShimuraMap_add.lean`
- `Theorems/FLT/Thm_HeckeEis_eichlerShimuraMap_heckeTLin.lean`
- `Theorems/FLT/Thm_HeckeEis_eichlerShimuraMap_heckeULin.lean`
- `Theorems/FLT/Thm_HeckeEis_eichlerShimuraMap_smul.lean`
- `Theorems/FLT/Thm_HeckeEis_exists_basis_coeffH1par_int_complex.lean`
- `Theorems/FLT/Thm_HeckeEis_finrank_coeffH1par_le_two_mul_dimFormula.lean`
- `Theorems/FLT/Thm_HeckeEis_finrank_coeffH1par_zero_le_two_mul_genusFormula.lean`
- `Theorems/FLT/Thm_HeckeEis_range_eichlerShimuraMap_inf_range_conj_eq_bot.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_linearMap_regularDifferentials_mdifferentiable.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_isDomain_ring.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_isZeroAtImInfty_slash_of_mem_regularDifferentials.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_hassePolyDescent.lean`
- `Theorems/FLT/Thm_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq.lean`
- `Theorems/FLT/Thm_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq_pow.lean`
- `Theorems/FLT/Thm_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow.lean`
- `Theorems/FLT/Thm_ModularCurve_eventually_norm_slash_le_mul_of_isIntegral_adjoin_jqModC_inv_sq.lean`
- `Theorems/FLT/Thm_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_coeffEmb_jq_inv.lean`
- `Theorems/FLT/Thm_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_coeffEmb_jq_inv_pow.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant.lean`
- `Theorems/FLT/Thm_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant.lean`
- `Theorems/FLT/Thm_ModularCurve_nonempty_integralWeightOneForm.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand.lean`
- `Theorems/FLT/Thm_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_exists_ord_pos.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_mem_comap_iff_ord_nonneg.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg.lean`
- `Theorems/FLT/Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_valuation_transEquiv_weilFun.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_weilFun_ne_zero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed.lean`
- `Theorems/KN/Thm_HorizontalPadicL_horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_centralCoinduced_parabolicH1_dimension_upper_bound.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_exists_weighted_modular_seeds_level_four.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_mixed_period_test_functions_wirtinger_data_of_pos_level.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_level_three_odd.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_period_pairings_eq_wirtinger_sums_of_weight_ge_two.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_signed_evaluation.lean`

## Generation 8

- `Definitions/FLT/Def_ModularCurve_EMD.lean`
- `Definitions/FLT/Def_ModularCurve_JZeroTateModule.lean`
- `Definitions/FLT/Def_ModularCurve_XH.lean`
- `Definitions/KN/Def_KN_PrimePowerPropagationV2.lean`
- `Definitions/KN/Def_KN_SeededFiniteThetaCriticalZeroSetV2.lean`
- `Solutions/FLT/Sol_WeierstrassCurve_tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_pushforwardNormFormula.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_evalAt_inv.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_evalAt_ne_zero.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_inertiaDeg_pos.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_dvd_of_hahnSeries_embedding_of_isGalois.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_charEq_on_torsionBy_of_line_of_isotropic.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_kerDeg_frobEnd_line_one.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_ne_zero.lean`
- `Theorems/FLT/Thm_HeckeEis_existsEichlerShimuraMapLinear.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_place_ord_jGen_le_two_three_level.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_hasEquivariantPrimitiveOf.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion.lean`
- `Theorems/FLT/Thm_ModularCurve_isCusp_iff_ord_neg.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv.lean`
- `Theorems/FLT/Thm_ModularCurve_modularPolynomialFamily.lean`
- `Theorems/FLT/Thm_ModularCurve_modularUnitSeries_mem_modularFunctionField.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728.lean`
- `Theorems/FLT/Thm_ModularCurve_periodMapOf_mem_parabolicHoms.lean`
- `Theorems/FLT/Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf.lean`
- `Theorems/FLT/Thm_ModularCurve_three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree.lean`
- `Theorems/FLT/Thm_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo.lean`
- `Theorems/FLT/Thm_TateModule_exists_linearMap_apply_eq_of_addMonoidHom.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_smul.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_weilPairing0_self.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor.lean`
- `Theorems/KN/Thm_HorizontalPadicL_minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_equivariant_primitive_pairings_zero.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_exists_weighted_cusp_seeds_level_four.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_dimension_upper_bound_large_level.lean`

## Generation 9

- `Definitions/FLT/Def_ModularCurve_SpecialisationVocab.lean`
- `Definitions/KN/Def_KN_InverseSeedConventionV2.lean`
- `Definitions/KN/Def_KN_TruncatedHorizontalCoefficientsV2.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_evalAt_zpow.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_exists_restrict_eq.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_TranscendenceTower_poleDivisor_apply.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_constantsAreBase_of_exists_isRational.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_linearIndependent_pow_mul.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_normFormulaAlong.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_frobCharEqOnPoints_of_line.lean`
- `Theorems/FLT/Thm_HeckeEis_eichlerShimuraMap_injective.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic.lean`
- `Theorems/FLT/Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar.lean`
- `Theorems/FLT/Thm_ModularCurve_emd_of_beta_docks.lean`
- `Theorems/FLT/Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_isFrickeAut.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash.lean`
- `Theorems/FLT/Thm_ModularCurve_finite_cycSub.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean`
- `Theorems/FLT/Thm_ModularCurve_isCusp_cuspInftyBar.lean`
- `Theorems/FLT/Thm_ModularCurve_isCusp_cuspZeroBar.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_jqNModC_all.lean`
- `Theorems/FLT/Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean`
- `Theorems/FLT/Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne.lean`
- `Theorems/FLT/Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_quot_sameOrbit_cycSub_eq_natCard_moduliPoint_j_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_neg_width_le_ord_of_order_eq_mul_ord_of_qExpansion_slash.lean`
- `Theorems/FLT/Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree.lean`
- `Theorems/FLT/Thm_ModularCurve_periodMapOf_apply_eq_periodOf.lean`
- `Theorems/FLT/Thm_ModularCurve_place_eq_of_induces.lean`
- `Theorems/FLT/Thm_ModularCurve_sameOrbit_iff_eq_of_c4_ne_zero_of_c6_ne_zero.lean`
- `Theorems/FLT/Thm_TateModule_exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_weilPairing0_add_left.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_weilPairing0_add_right.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_weilPairing0_galois.lean`
- `Theorems/KN/Thm_HorizontalPadicL_CharacterCountingTransfer_logLowerBound_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo.lean`
- `Theorems/KN/Thm_HorizontalPadicL_primitiveCharacters_boundedConductor_finite_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_primitiveProductArithmetic_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_supportedPrimePowerCharacters_logLowerBound_v2.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_cuspForm_finrank_lower_bound_level_four_odd.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_period_cocycle_injective.lean`

## Generation 10

- `Definitions/FLT/Def_ModularCurve_HahnSpecialise.lean`
- `Definitions/KN/Def_KN_SeededThetaFullSupportInterpolationV3.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_evalFun_zpow_left.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_dvd_of_forall_hahnSeries_embedding_hasRamBound.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_restrictAlong_surjective.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_nonempty_place_of_ratFunc_tower.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_ord_X_nonneg_of_ne_placeInfty.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_instIsCurveOverRatFunc.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_linearIndependent_pow_of_transcendental.lean`
- `Theorems/FLT/Thm_FrobeniusEndo_frobCharEqOnPoints_of_frobenius.lean`
- `Theorems/FLT/Thm_ModularCurve_B3_exists_variableChange_specialFibre_goodModel.lean`
- `Theorems/FLT/Thm_ModularCurve_B3_goodModel_1728_spec.lean`
- `Theorems/FLT/Thm_ModularCurve_B3_goodModel_generic_spec.lean`
- `Theorems/FLT/Thm_ModularCurve_B3_goodModel_zero_spec.lean`
- `Theorems/FLT/Thm_ModularCurve_B3_isElliptic_specialFibre.lean`
- `Theorems/FLT/Thm_ModularCurve_B3_isElliptic_specialFibre_goodModel.lean`
- `Theorems/FLT/Thm_ModularCurve_B3_nearCurve_eq_ofJNe0Or1728.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_eq_of_prime.lean`
- `Theorems/FLT/Thm_ModularCurve_StarBank_starBank.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_isFrickeAutFull.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_phiIrreducible_of_finrank_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_pairing_torsionBy.lean`
- `Theorems/KN/Thm_HorizontalPadicL_HorizontalMeasure_truncatedFiniteLevel_norm_le_of_primitive_twists_vanish_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_SeededHorizontalCharacterRealizationV3_realizes_supported_pPower_character_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_SeededHorizontalPrimeSystemV3_orderExponent_le_exponent_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two.lean`
- `Theorems/KN/Thm_HorizontalPadicL_finiteCorrection_realization_countingTransfer_inverseSeed_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_goodReduction_minimal_of_not_modularConductor_dvd.lean`
- `Theorems/KN/Thm_HorizontalPadicL_positiveDensityOrderlySet_to_primeSystem_inverseSeed_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_seededEulerFactors_areUnits_v4.lean`
- `Theorems/KN/Thm_HorizontalPadicL_seededFrobeniusClass_isOrderly_inverseSeed_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_seededHorizontalPadicLFunction_assemble_v4.lean`
- `Theorems/KN/Thm_HorizontalPadicL_seededNormalizedThetaMeasure_trivial_interpolation_inverseSeed_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_unitNormRelationThetaSystem_to_normalizedMeasure_inverseSeed_v2.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_eichler_shimura_direct.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_three_four_odd.lean`
- `Theorems/MTT/Thm_MTT_period_vanishing.lean`

## Generation 11

- `Definitions/KN/Def_KN_SeededThetaFullSupportModularSymbolZeroSetV2.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_ord_X_sub_C.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean`
- `Theorems/FLT/Thm_ModularCurve_HahnSpecialise_specialiseCycSub_injective.lean`
- `Theorems/FLT/Thm_ModularCurve_HahnSpecialise_specialise_bijOn_torsion.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_splits_of_prime.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_apply_eq_of_forall_ord_eq_zero_tendsto_realizeOf.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero.lean`
- `Theorems/FLT/Thm_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull.lean`
- `Theorems/FLT/Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_algHom_ext_of_forall_restrictAlong_placeOfPoint_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_exists_algEquiv_restrictAlong_placeOfPoint_eq_add.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charZero.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_frobenius_cayleyHamilton_on_torsion.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_tateModuleRep_detIsCyclotomic.lean`
- `Theorems/KN/Thm_HorizontalPadicL_HorizontalMeasure_boundedExponent_finiteCorrection_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_ellipticCurve_attachedForm_isNormalizedEigenform.lean`
- `Theorems/KN/Thm_HorizontalPadicL_exists_good_integral_model_with_ap.lean`
- `Theorems/KN/Thm_HorizontalPadicL_fullSupportCriticalZeroSet_descends_inverseSeed_v3.lean`
- `Theorems/KN/Thm_HorizontalPadicL_seededHorizontalCharacterRealization_exists_v4.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_character_law_of_class.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_eichler_shimura_nebentype_compatible.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_integration_cochain_injective.lean`

## Generation 12

- `Definitions/KN/Def_KN_EllipticCurveAttachedEigenform.lean`
- `Definitions/KN/Def_KN_SeededInverseThetaSystemV2.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_ord_sub_algebraMap.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isCurveOver_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_le_genusFF_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_natCard_place_ord_sub_pos_le_natCard_doubleCoset.lean`
- `Theorems/FLT/Thm_ModularCurve_B3_exists_torsionBy_reduction_addEquiv.lean`
- `Theorems/FLT/Thm_ModularCurve_HahnSpecialise_specialiseCycSub_bijective.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_exists_place_ord_jGen_eq_three_two_and_stabilizer_subset_zpowers.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean`
- `Theorems/FLT/Thm_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean`
- `Theorems/FLT/Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar.lean`
- `Theorems/FLT/Thm_ModularCurve_eq_jLinePlace1728_iff_ord_jGen_sub_pos.lean`
- `Theorems/FLT/Thm_ModularCurve_eq_jLinePlaceInfty_iff_ord_jGen_neg.lean`
- `Theorems/FLT/Thm_ModularCurve_eq_jLinePlaceZero_iff_ord_jGen_pos.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean`
- `Theorems/FLT/Thm_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional.lean`
- `Theorems/FLT/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean`
- `Theorems/FLT/Thm_ModularCurve_index_le_relfinrank_qExpFunctionFieldC_gamma0_gammaH_of_charZero.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_jLinePlace1728_jGen_sub.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_jLinePlaceZero_jGen.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_tateModuleRep_det_frobenius.lean`
- `Theorems/KN/Thm_HorizontalPadicL_SeededHorizontalPadicLFunctionV4_primePower_propagation_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_ellipticCurve_eigenform_specialization_v2.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_eichler_shimura_hecke_compatible_char.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_image_packet_unique.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_integration_map.lean`

## Generation 13

- `Definitions/FLT/Def_ModularCurve_SpecialisationBridge.lean`
- `Solutions/KN/Sol_HorizontalPadicL_attachedEigenform_isNew.lean`
- `Solutions/KN/Sol_HorizontalPadicL_attachedEigenform_nonvanishingCount_eq.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_genusFF_le_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean`
- `Theorems/FLT/Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean`
- `Theorems/FLT/Thm_ModularCurve_full_eq_adjoin_full_div_prime.lean`
- `Theorems/FLT/Thm_ModularCurve_full_eq_adjoin_primes.lean`
- `Theorems/FLT/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional.lean`
- `Theorems/FLT/Thm_ModularCurve_jqNModC_prime_not_mem_fullC.lean`
- `Theorems/FLT/Thm_ModularCurve_jqN_div_mem_modularFunctionField.lean`
- `Theorems/FLT/Thm_ModularCurve_jqN_pow_not_mem_adjoin_full.lean`
- `Theorems/FLT/Thm_ModularCurve_jqN_prime_not_mem_adjoin.lean`
- `Theorems/FLT/Thm_ModularCurve_laurentBaseChange_adjoin_pair.lean`
- `Theorems/FLT/Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean`
- `Theorems/FLT/Thm_ModularCurve_modularFunctionField_eq_full_of.lean`
- `Theorems/FLT/Thm_ModularCurve_ramificationIndex_eq_ord_of_restrict_eq_jLinePlaceZero.lean`
- `Theorems/FLT/Thm_ModularCurve_ramificationIndex_eq_ord_sub_of_restrict_eq_jLinePlace1728.lean`
- `Theorems/FLT/Thm_ModularCurve_relfinrank_fullC_mul_prime_pow.lean`
- `Theorems/FLT/Thm_ModularCurve_restrict_eq_jLinePlace1728_iff.lean`
- `Theorems/FLT/Thm_ModularCurve_restrict_eq_jLinePlaceInfty_iff.lean`
- `Theorems/FLT/Thm_ModularCurve_restrict_eq_jLinePlaceZero_iff.lean`
- `Theorems/FLT/Thm_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_isCentred.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_tateModuleRep_charpoly_frobenius.lean`
- `Theorems/KN/Thm_HorizontalPadicL_attachedEigenform_isNew.lean`
- `Theorems/KN/Thm_HorizontalPadicL_attachedEigenform_nonvanishingCount_eq.lean`
- `Theorems/KN/Thm_HorizontalPadicL_fullSupport_atLevel_apply_eq_realized_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_realizedHorizontalCharacter_even_of_odd_prime_v2.lean`

## Generation 14

- `Theorems/FLT/Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_weilDualityAdelic_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_ModularCurve_B3_specialisationEquivariance_level.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange.lean`
- `Theorems/FLT/Thm_ModularCurve_isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1.lean`
- `Theorems/FLT/Thm_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean`
- `Theorems/FLT/Thm_ModularCurve_modularFunctionFieldBar_eq_restrictScalars.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index.lean`
- `Theorems/FLT/Thm_ModularCurve_relfinrank_full_eq_mul.lean`
- `Theorems/FLT/Thm_ModularCurve_relfinrank_full_of_squarefree.lean`
- `Theorems/FLT/Thm_ModularCurve_transcendental_coeffEmb_jq.lean`
- `Theorems/FLT/Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples_of_oddOrder.lean`

## Generation 15

- `Definitions/FLT/Def_ModularCurve_JLinePlacesBar.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_poleDivisor_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_regularDiffs_eq_regularDifferentials.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean`
- `Theorems/FLT/Thm_ModularCurve_finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqN_eq_of_squarefree.lean`
- `Theorems/FLT/Thm_ModularCurve_package_of_socket.lean`
- `Theorems/FLT/Thm_ModularCurve_relfinrank_laurentBaseChange.lean`
- `Theorems/FLT/Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int.lean`

## Generation 16

- `Theorems/FLT/Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean`
- `Theorems/FLT/Thm_ModularCurve_functionFieldGeneration_of_squarefree.lean`

## Generation 17

- `Theorems/FLT/Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_AlgebraicCurve_six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two.lean`
- `Theorems/FLT/Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_ModularCurve_jqN_prime_not_mem_full.lean`
- `Theorems/FLT/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean`
- `Theorems/FLT/Thm_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma.lean`
- `Theorems/FLT/Thm_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.lean`

## Generation 18

- `Theorems/FLT/Thm_ModularCurve_exists_phiIrreducible.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.lean`
- `Theorems/FLT/Thm_ModularCurve_functionFieldGeneration.lean`
- `Theorems/FLT/Thm_ModularCurve_modularFunctionField_eq_full.lean`
- `Theorems/FLT/Thm_ModularCurve_relfinrank_full_eq_dedekindPsi.lean`
- `Theorems/FLT/Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC.lean`

## Generation 19

- `Theorems/FLT/Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.lean`
- `Theorems/FLT/Thm_ModularCurve_PhiGen_sum_qTwist_coeff.lean`
- `Theorems/FLT/Thm_ModularCurve_adjoin_jBar_jNBar_eq_top.lean`
- `Theorems/FLT/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_algHom_laurentBaseChange_slot.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_algHom_of_isRoot.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_finset_ord_jBar_sub_pos.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_slot_of_isCusp.lean`
- `Theorems/FLT/Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_jAdjoin_modularFunctionField_eq_dedekindPsi.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.lean`
- `Theorems/FLT/Thm_ModularCurve_isRoot_map_Phi_apply_jBar.lean`
- `Theorems/FLT/Thm_ModularCurve_isSeparable_adjoin_coeffEmb_jq_full.lean`
- `Theorems/FLT/Thm_ModularCurve_nonempty_equiv_place_pos_ord_algHom_integralClosure.lean`
- `Theorems/FLT/Thm_ModularCurve_nonempty_modularPolynomialData.lean`
- `Theorems/FLT/Thm_ModularCurve_slot_ord_of_algHom_laurentBaseChange.lean`
- `Theorems/FLT/Thm_ModularCurve_slot_place_eq_iff_modEq.lean`
- `Theorems/FLT/Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi.lean`
- `Theorems/FLT/Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le.lean`

## Generation 20

- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag.lean`
- `Theorems/FLT/Thm_ModularCurve_card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg.lean`
- `Theorems/FLT/Thm_ModularCurve_deg_ne_zero_modularFunctionFieldC.lean`
- `Theorems/FLT/Thm_ModularCurve_diffQExpBar_injective_of_neZero.lean`
- `Theorems/FLT/Thm_ModularCurve_essFiniteType_modularFunctionFieldBar.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_emb_equiv_rootsAt.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_place_of_emb.lean`
- `Theorems/FLT/Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi.lean`
- `Theorems/FLT/Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_ord_jBar_eq_one_eq_nuThree.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo.lean`
- `Theorems/FLT/Thm_ModularCurve_theta_coeff.lean`
- `Theorems/FLT/Thm_ModularCurve_theta_mul.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_weight_two.lean`

## Generation 21

- `Definitions/FLT/Def_ModularCurve_OmegaOf.lean`
- `Theorems/FLT/Thm_ModularCurve_card_eq_natCard_quot_samePlace_of_forall_mem_iff_pos_ord.lean`
- `Theorems/FLT/Thm_ModularCurve_coe_qExpansion_normalizedDerivOfComplex.lean`
- `Theorems/FLT/Thm_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0.lean`
- `Theorems/FLT/Thm_ModularCurve_isCurveOver_modularFunctionFieldBar.lean`
- `Theorems/FLT/Thm_ModularCurve_samePlace_iff_exists_hahnTwist.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_transcendental_j.lean`

## Generation 22

- `Theorems/FLT/Thm_ModularCurve_card_eq_natCard_moduliPoint_j_eq_of_EMD.lean`
- `Theorems/FLT/Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar.lean`
- `Theorems/FLT/Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index.lean`
- `Theorems/FLT/Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar.lean`
- `Theorems/FLT/Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar.lean`
- `Theorems/FLT/Thm_ModularCurve_samePlace_iff_exists_monodromy.lean`
- `Theorems/FLT/Thm_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi.lean`
- `Theorems/FLT/Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_transcendental.lean`

## Generation 23

- `Definitions/FLT/Def_ModularCurve_CycSubRootBridge.lean`
- `Theorems/FLT/Thm_ModularCurve_LevelN_Descent_fixer_le.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd.lean`
- `Theorems/FLT/Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar.lean`
- `Theorems/FLT/Thm_ModularCurve_natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset.lean`
- `Theorems/FLT/Thm_ModularForm_qExpansion_E4_mul_theta_discriminant_sub.lean`
- `Theorems/FLT/Thm_omegaRow_T2.lean`

## Generation 24

- `Definitions/FLT/Def_ModularCurve_CycSubRootBridgeN.lean`
- `Definitions/FLT/Def_ModularCurve_CycSubRootBridgeOdd.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_hasRamBound_three_of_isRoot_at_zero_of_odd.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_hasRamBound_two_of_isRoot_at_1728_of_odd.lean`
- `Theorems/FLT/Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.lean`
- `Theorems/FLT/Thm_ModularCurve_degree_add_one_sub_genusFF_le_finrank_riemannRochSpace.lean`
- `Theorems/FLT/Thm_ModularCurve_eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_of_isIntegral.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_modularForm_gamma1_qExpansion_eq_mul_thetaL_pow_of_isIntegral.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure.lean`

## Generation 25

- `Theorems/FLT/Thm_ModularCurve_TatePoint_b3Act_dictN_of_monodromy.lean`
- `Theorems/FLT/Thm_ModularCurve_TatePoint_fullKernelDiscAt_of_odd.lean`
- `Theorems/FLT/Thm_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_cuspForm_qExpansion_eq_coeffMap_mul_thetaL_pow_of_isIntegral.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_jBar_sub_1728_dvd_two.lean`
- `Theorems/FLT/Thm_ModularCurve_thetaL_jq_mul_deltaSeries.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_fullKernelQuotient_eq_veluQuotient_of_odd.lean`

## Generation 26

- `Theorems/FLT/Thm_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1.lean`
- `Theorems/FLT/Thm_ModularCurve_TatePoint_fullKernelDiscAt.lean`
- `Theorems/FLT/Thm_ModularCurve_even_ord_add_ord_of_not_mem_toValuationSubring_laurentBaseChange_gamma1.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_jBar_dvd_three.lean`
- `Theorems/FLT/Thm_ModularCurve_thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6.lean`
- `Theorems/FLT/Thm_ModularCurve_twelve_mul_genusFF_laurentBaseChange_gamma1_add_six_mul_natCard_doubleCoset_eq_index_add_twelve.lean`
- `Theorems/FLT/Thm_WeierstrassCurve_exists_functionFieldHom_fullKernelQuotient_pointMapOfPushforward_ker_eq_zmultiples.lean`

## Generation 27

- `Theorems/FLT/Thm_ModularCurve_TatePoint_fullKernelInjAt.lean`
- `Theorems/FLT/Thm_ModularCurve_TatePoint_fullKernelIsRootAt.lean`
- `Theorems/FLT/Thm_ModularCurve_even_ord_add_weightFloor_of_mem_toValuationSubring_laurentBaseChange_gamma1.lean`
- `Theorems/FLT/Thm_ModularCurve_twelve_mul_genusFF_laurentBaseChange_gamma1_add_six_mul_natCard_doubleCoset_eq_index_add_twelve_of_isAlgClosed.lean`
- `Theorems/FLT/Thm_ModularForm_exists_gamma1_weightOne_ne_zero_and_mul_thetaL_eq_qExpansion_sq.lean`

## Generation 28

- `Theorems/FLT/Thm_ModularCurve_exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_elliptic_cycSub_orbitMap.lean`
- `Theorems/FLT/Thm_ModularForm_exists_linearIndependent_gamma1_dimFormula_le_card_of_even.lean`

## Generation 29

- `Theorems/FLT/Thm_ModularCurve_emd_holds.lean`
- `Theorems/FLT/Thm_ModularCurve_ord_jBar_sub_eq_one_of_ne_zero_of_ne.lean`
- `Theorems/FLT/Thm_ModularForm_exists_linearIndependent_gamma1_dimFormula_le_card_of_odd.lean`

## Generation 30

- `Theorems/FLT/Thm_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace.lean`
- `Theorems/FLT/Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula.lean`
- `Theorems/FLT/Thm_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar.lean`
- `Theorems/FLT/Thm_ModularForm_exists_linearIndependent_gamma1_dimFormula_le_card.lean`

## Generation 31

- `Theorems/FLT/Thm_CuspForm_dimFormula_le_finrank_gamma0.lean`
- `Theorems/FLT/Thm_ModularCurve_exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_gammaOne_cuspForm_dimension_lower_bound.lean`

## Generation 32

- `Theorems/FLT/Thm_CuspForm_genusFormula_le_finrank_gamma0_weight_two.lean`

## Generation 33

- `Theorems/FLT/Thm_HeckeEis_isCompl_range_eichlerShimuraMap_range_conj.lean`

## Generation 34

- `Theorems/FLT/Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime.lean`

## Generation 35

- `Theorems/FLT/Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL.lean`

## Generation 36

- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_level_two.lean`
- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_three_four_even.lean`

## Generation 37

- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_three_four.lean`

## Generation 38

- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_two_three_four.lean`

## Generation 39

- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le_higher_level_weight.lean`

## Generation 40

- `Theorems/MTT/Thm_MTT_Cohomology_parabolicH1_finrank_le.lean`

## Generation 41

- `Theorems/MTT/Thm_MTT_Cohomology_parabolic_period_cocycle_surjective.lean`

## Generation 42

- `Theorems/MTT/Thm_MTT_Cohomology_eichler_shimura_span.lean`

## Generation 43

- `Theorems/MTT/Thm_MTT_Cohomology_packet_span.lean`

## Generation 44

- `Theorems/MTT/Thm_MTT_Cohomology_signed_packet_multiplicity_one.lean`

## Generation 45

- `Theorems/KN/Thm_MTT_Cohomology_eigenform_hecke_stable_period_lattice.lean`
- `Theorems/KN/Thm_MTT_Cohomology_eigenform_uniform_hecke_stable_period_lattice.lean`
- `Theorems/MTT/Thm_MTT_periods_exist.lean`

## Generation 46

- `Theorems/KN/Thm_MTT_Eigenform_coefficientField_finiteDimensional.lean`
- `Theorems/KN/Thm_MTT_Eigenform_heckeEigenvalue_isIntegral.lean`
- `Theorems/MTT/Thm_MTT_goal.lean`

## Generation 47

- `Theorems/KN/Thm_MTT_Eigenform_coeff_isIntegral.lean`
- `Theorems/KN/Thm_MTT_numberField_coefficientField.lean`

## Generation 48

- `Theorems/KN/Thm_HorizontalPadicL_seededEigenform_padicPlace_exists_v2.lean`
- `Theorems/KN/Thm_MTT_Eigenform_coeff_mem_ringOfIntegers.lean`
- `Theorems/KN/Thm_MTT_Eigenform_coefficientPrime_isMaximal.lean`

## Generation 49

- `Definitions/KN/Def_MTT_EigenformCoefficientResidueField.lean`

## Generation 50

- `Definitions/KN/Def_KN_EigenformResidualGaloisRepresentationV2.lean`
- `Definitions/KN/Def_MTT_EigenformCoefficientCompletion.lean`

## Generation 51

- `Definitions/KN/Def_MTT_EigenformCoefficientLocalField.lean`
- `Theorems/KN/Thm_HorizontalPadicL_coprimeRamification_productFrobeniusClass_exists_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_residualKernel_discr_prime_dvd_level_mul_p.lean`

## Generation 52

- `Theorems/KN/Thm_HorizontalPadicL_coprimeDiscriminant_simultaneousSeededFrobeniusClass_exists_v2.lean`
- `Theorems/KN/Thm_MTT_Eigenform_exists_continuous_localField_representation.lean`

## Generation 53

- `Theorems/KN/Thm_HorizontalPadicL_corollary_5_17_conditional.lean`
- `Theorems/KN/Thm_MTT_Eigenform_exists_adic_matrix_representation.lean`

## Generation 54

- `Theorems/KN/Thm_HorizontalPadicL_eigenform_residualGaloisRepresentation_exists_v2.lean`
- `Theorems/KN/Thm_HorizontalPadicL_elliptic_curve_nonvanishing_conditional.lean`

## Generation 55

- `Theorems/KN/Thm_HorizontalPadicL_disjointRamification_seededFrobeniusClass_exists_v4.lean`
- `Theorems/KN/Thm_HorizontalPadicL_newEigenform_residualRepresentation_exists_v2.lean`

## Generation 56

- `Theorems/KN/Thm_HorizontalPadicL_corollary_5_17_v2.lean`

## Generation 57

- `Solutions/KN/Sol_HorizontalPadicL_elliptic_curve_nonvanishing.lean`
- `Theorems/KN/Thm_HorizontalPadicL_elliptic_curve_nonvanishing.lean`
