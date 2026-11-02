import Guralnick.SeedRankOneConvention
import Guralnick.SeedPolynomials
import Guralnick.SeedWebCoordinates
import Guralnick.CanonicalSchurEigenReduction
import Guralnick.FiniteFlagEnumerationExamples
import Guralnick.PolynomialOrbitCountingExamples
import Guralnick.FiniteDoubleCosetMaximum
import Guralnick.PolynomialCoordinateFlags
import Guralnick.CoordinateLatticeDegree
import Guralnick.PolynomialOrbitTransfer
import Guralnick.PolynomialFlags
import Guralnick.PolynomialWebLiterature
import Guralnick.ModelComparisonCounterexample
import Guralnick.CompletionIncidence
import Guralnick.LatticeTruncatedLift
import Guralnick.WebTraceExamples
import Guralnick.WebTraceSeamExample
import Guralnick.FidelityKL
import Guralnick.FidelityWeb
import Guralnick.FidelityWeights
import Guralnick.WebProof
import Guralnick.WebMasks
import Guralnick.Family
import Guralnick.WindowExamples
import Guralnick.Normalization
import Guralnick.WebExamples
import Guralnick.Positivity
import Guralnick.DegreeBounds
import Guralnick.Cohomology
import Guralnick.CentralQuotient
import Guralnick.CoordinateLiteratureTransfer
import Guralnick.SLCoordinateReduced
import Guralnick.SLCoordinateHopf
import Guralnick.PolynomialAffineCoordinates
import Guralnick.PolynomialLatticeBasis
import Guralnick.LatticeEquivariance

/- Diagnostic principal results, including the genuinely conditional endpoint.
The matching failing guards live in GuardedAudit.lean; both belong to the
separate GuralnickAudit build target, not to the mathematical library.
The standard foundational axioms are not mathematical assumptions about
KL polynomials or algebraic-group representations. Those assumptions are
visible arguments in the printed theorem. Original family obligations are
now discharged by WebProof; the general literature inputs remain unproved. -/

#print axioms Guralnick.AffinePermutation.onIntegers_periodic
#print axioms Guralnick.AffinePermutation.sum_entry
#print axioms Guralnick.AffinePermutation.inverse_dotZero
#print axioms Guralnick.WindowCertificate.check_sound
#print axioms Guralnick.WindowCertificate.toAffine
#print axioms Guralnick.Certificates.m2j2_family
#print axioms Guralnick.Certificates.m5j5_matrix
#print axioms Guralnick.Certificates.m5j5_dotZero
#print axioms Guralnick.Certificates.invalid_rejected
#print axioms Guralnick.Family.window_eq_familyWindow
#print axioms Guralnick.Family.inverse_dotZero_eq_coordinate
#print axioms Guralnick.Weights.sum_coordinates
#print axioms Guralnick.Weights.dynkin_bounds
#print axioms Guralnick.Weights.familyWeight_nonzero
#print axioms Guralnick.Weights.familyWeight_pRegular
#print axioms Guralnick.normalize_critical
#print axioms Guralnick.gapFormula_odd
#print axioms Guralnick.normalize_family_critical
#print axioms Guralnick.suppliedSeed_full
#print axioms Guralnick.Web.family_wellFormed
#print axioms Guralnick.Web.family_boundaries
#print axioms Guralnick.Web.family_incident_conservation
#print axioms Guralnick.Web.family_seam_degree
#print axioms Guralnick.Web.seed_matches_builder
#print axioms Guralnick.Web.rank_one_needs_zero_edge_contraction
#print axioms Guralnick.Positivity.isLowest_mul
#print axioms Guralnick.Positivity.cancel_lowerBound
#print axioms Guralnick.Positivity.cleared_support_bounds
#print axioms Guralnick.Positivity.cleared_constant_of_zero_bound
#print axioms Guralnick.Positivity.cleared_zero_or_one
#print axioms Guralnick.Positivity.positive_division_is_invalid
#print axioms Guralnick.DegreeBounds.six_positions_of_bounds
#print axioms Guralnick.DegreeBounds.boundary_position_of_bounds
#print axioms Guralnick.CentralQuotient.finiteKernelInflationLinearEquiv
#print axioms Guralnick.CentralQuotient.central_quotient_finrank
#print axioms Guralnick.CentralQuotient.representation_faithful_of_simple
#print axioms Guralnick.Cohomology.h1IsoExtFromTrivial
#print axioms Guralnick.Cohomology.rowSum_and_lowerBound
#print axioms Guralnick.Cohomology.exists_PSL_counterexample
#print axioms Guralnick.Cohomology.not_algebraicallyClosedBoundedness

#check Guralnick.Cohomology.exists_PSL_counterexample
#check Guralnick.Cohomology.rowSum_and_lowerBound
#check Guralnick.Cohomology.not_algebraicallyClosedBoundedness
#print Guralnick.Cohomology.DoubledRowSum
#print Guralnick.Cohomology.PrimeFieldTransfer

/- Complete original proof, conditional only on the printed general inputs. -/
#print axioms Guralnick.Family.upper_matrixEntry_eq_prescribedArray
#print axioms Guralnick.Hecke.family_length_gap
#print axioms Guralnick.Hecke.familyMu_inverse_canonical
#print axioms Guralnick.WebMasks.stage_masks
#print axioms Guralnick.ParabolicWeb.Family.raw_cleared
#print axioms Guralnick.ParabolicWeb.Family.raw_cleared_nonnegative
#print axioms Guralnick.MainGalleryCount.main_gallery_count
#print axioms Guralnick.MainSourceCoordinate.raw_source_coordinate
#print axioms Guralnick.MainPacketCoordinate.raw_packet_coordinate
#print axioms Guralnick.MainCanonicalSupport.raw_six_position_support
#print axioms Guralnick.MainFamilyCoordinate.marked_raw_coordinate
#print axioms Guralnick.PacketIndexClassification.typeF_index
#print axioms Guralnick.PacketIndexClassification.full_pattern_index
#print axioms Guralnick.PacketCoarsening.strong_doubleMaximal
#print axioms Guralnick.PacketCoarsening.weak_doubleMaximal
#print axioms Guralnick.CanonicalOneLineEvaluation.canonical_of_leading
#print axioms Guralnick.CanonicalOneLinePatterns.strong_canonical
#print axioms Guralnick.CanonicalOneLinePatterns.weakDual_canonical
#print axioms Guralnick.CanonicalSphericalTransition.transition_matrix
#print axioms Guralnick.CanonicalRefinement.spherical_at_family
#print axioms Guralnick.CanonicalAuxiliaryMargins.strong_source_product
#print axioms Guralnick.OneLineSpecialization.strong_at_marked_margin
#print axioms Guralnick.OneLineSpecialization.weak_at_spherical_margin
#print axioms Guralnick.Gaussian.normalized_Q_critical
#print axioms Guralnick.CanonicalFullCorrection.corrected_critical
#print axioms Guralnick.WebLiterature.auxiliary_family_bound
#print axioms Guralnick.WebLiterature.nonspherical_bound
#print axioms Guralnick.WebLiterature.auxiliary_source_bound
#print axioms Guralnick.WebProof.row_sum
#print axioms Guralnick.HighestWeight.root_lattice_center_trivial
#print axioms Guralnick.SLQuotient.center_order_invertible
#print axioms Guralnick.SLQuotient.descended_h1_dimension
#print axioms Guralnick.Cohomology.irreducible_absolutelyIrreducible
#print axioms Guralnick.LiteratureTransfer.familyModule_h1_dimension
#print axioms Guralnick.LiteratureTransfer.familyModule_absolutelyAdmissible
#print axioms Guralnick.WebProof.named_row_and_lower_bound
#print axioms Guralnick.WebProof.not_absoluteBoundedness

#check Guralnick.WebProof.row_sum
#check Guralnick.WebProof.named_row_and_lower_bound
#check Guralnick.WebProof.not_absoluteBoundedness
#print Guralnick.Cohomology.AbsoluteBoundedness
#print Guralnick.Cohomology.AbsoluteUniformH1Bound
#print Guralnick.Hecke.Theory
#print Guralnick.Hecke.WindowCoxeter
#print Guralnick.Hecke.KLRealization
#print Guralnick.WebLiterature
#print Guralnick.FlagConvolution.Input
#print Guralnick.OrbitMatrix.ThreeColumnLengthInput
#print Guralnick.GeneralLatticeFlagInput
#print Guralnick.LiteratureTransfer.Inputs
#print Guralnick.LiteratureTransfer.AndersenAJS
#print Guralnick.LiteratureTransfer.BNP

/- Independent semantic checks: no new mathematical inputs. -/
#print axioms Guralnick.FidelityKL.normalize_injective
#print axioms Guralnick.FidelityKL.standard_eq
#print axioms Guralnick.FidelityKL.bar_eq
#print axioms Guralnick.FidelityKL.bar_fixed_positive_zero
#print axioms Guralnick.FidelityKL.canonical_eq
#print axioms Guralnick.FidelityKL.polynomial_eq
#print axioms Guralnick.FidelityKL.familyMu_eq
#print axioms Guralnick.FidelityWeb.family_frontiers
#print axioms Guralnick.FidelityWeights.dynkin_eq_manuscript
#print axioms Guralnick.FidelityWeights.coordinate_eq_manuscript
#print axioms Guralnick.FidelityWeights.etaCoordinate_eq_fundamental
#print axioms Guralnick.FidelityWeights.etaCoordinate_sum
#print axioms Guralnick.FidelityWeights.m2_j1_labels
#print axioms Guralnick.FidelityWeights.m2_j2_labels

/- The fixed graph presentation and its entire integral module morphism. -/
#print axioms Guralnick.WebBoundary.Family.mem_index_iff
#print axioms Guralnick.WebBoundary.Family.local_relations
#print axioms Guralnick.WebTrace.family_step
#print axioms Guralnick.WebTrace.familyState_boundary
#print axioms Guralnick.WebTrace.family_graph
#print axioms Guralnick.WebTrace.family_frontier
#print axioms Guralnick.WebTraceWinding.step_mass
#print axioms Guralnick.WebTraceWinding.run_charge
#print axioms Guralnick.WebTraceWinding.run_zero_cut_seam
#print axioms Guralnick.WebTraceWinding.single_packet_turn_rejected
#print axioms Guralnick.WebTraceWinding.consecutive_right_rejected
#print axioms Guralnick.WebRecutPositions.step_right_positions
#print axioms Guralnick.WebRecutPositions.step_left_positions
#print axioms Guralnick.WebPresentedWinding.seamDegree_zero
#print axioms Guralnick.WebPresentedWinding.not_presentable_of_nonzero_seam
#print axioms Guralnick.WebEvaluation.merge_linear_unique
#print axioms Guralnick.WebEvaluation.merge_comp_unique
#print axioms Guralnick.WebEvaluationCompression.Resolution.fine_linear_eq_coarse
#print axioms Guralnick.WebTraceEvaluation.Program.replay
#print axioms Guralnick.WebTraceEvaluation.familyProgram_operations
#print axioms Guralnick.WebTraceEvaluation.familyPresentedGraph_replay
#print axioms Guralnick.WebTraceEvaluation.family_graph_evaluation_eq_raw
#print axioms Guralnick.WebRightLinearity.program_rightLinear
#print axioms Guralnick.WebRightLinearity.ext_generator
#print axioms Guralnick.WebProof.graph_morphism_eq_sixMaps
#print axioms Guralnick.WebProof.graph_standard_coordinates
#print axioms Guralnick.WebProof.graph_canonical_coordinates
#print axioms Guralnick.WebProof.graph_corrected_source
#print axioms Guralnick.WebProof.graph_corrected_critical
#print axioms Guralnick.WebProof.graph_critical_eq_row_sum
#print axioms Guralnick.WebTrace.seed_replay
#print axioms Guralnick.WebTrace.rank_one_rejected
#print axioms Guralnick.WebTrace.erased_graph_rejected
#print axioms Guralnick.WebTraceSeamExample.ordinary_merge_index
#print axioms Guralnick.WebTraceSeamExample.seam_merge_index
#print axioms Guralnick.WebTraceSeamExample.seam_channel_replay
#print axioms Guralnick.WebTraceSeamExample.seam_channel_winding

#check Guralnick.WebTraceEvaluation.family_graph_evaluation_eq_raw
#check Guralnick.WebProof.graph_morphism_eq_sixMaps
#check Guralnick.WebProof.graph_corrected_critical
#check Guralnick.WebProof.graph_critical_eq_row_sum
#print Guralnick.WebTraceEvaluation.PresentedGraph

/- Previously assumed generic facts, now derived from the actual objects. -/
#print axioms Guralnick.ParabolicWeb.scalar_ne_zero
#print axioms Guralnick.ParabolicWeb.Laws.scalar_bar
#print axioms Guralnick.LaurentLattice.interval_lift
#print axioms Guralnick.LaurentLattice.intervalLattice_source_eq
#print axioms Guralnick.LaurentLattice.intervalLattice_upper_module
#print Guralnick.ParabolicWeb.Laws
#print Guralnick.LaurentLattice.Theory
#check Guralnick.ParabolicWeb.scalar_ne_zero
#check Guralnick.LaurentLattice.interval_lift

/- Actual lattice theory is constructed, not supplied as a literature input. -/
#print axioms Guralnick.LaurentLattice.latticeBasis_card
#print axioms Guralnick.LaurentLattice.periodCoefficients_kernel
#print axioms Guralnick.LaurentLattice.periodEquiv
#print axioms Guralnick.LaurentLattice.period_finite
#print axioms Guralnick.LaurentLattice.period_dimension
#print axioms Guralnick.LaurentLattice.exists_X_pow_smul_le
#print axioms Guralnick.LaurentLattice.finite_quotient
#print axioms Guralnick.LaurentLattice.standardLattice
#print axioms Guralnick.LaurentLattice.interLattice
#print axioms Guralnick.LatticeGallery.relative_degree_difference
#print axioms Guralnick.LaurentLattice.dimension_degree
#print axioms Guralnick.LaurentLattice.provedTheory
#print axioms Guralnick.GeneralLatticeFlagInput.lattice_theory
#print axioms Guralnick.PowerSeriesCompletion.completionEquiv
#print axioms Guralnick.PowerSeriesCompletion.completion_parameter_mul
#print axioms Guralnick.PowerSeriesCompletion.stableSubspaceEquiv
#print axioms Guralnick.PowerSeriesCompletion.subspace_inf
#print axioms Guralnick.PowerSeriesCompletion.subspace_sup
#print axioms Guralnick.PowerSeriesCompletion.series_finrank
#print axioms Guralnick.PowerSeriesCompletion.quotient_finrank
#print axioms Guralnick.LaurentLattice.XStable_iff_lattice
#print axioms Guralnick.LaurentLattice.truncatedIntervalIso
#print axioms Guralnick.LaurentLattice.truncatedLattice_zero
#print axioms Guralnick.LaurentLattice.truncatedLattice_one
#check Guralnick.LaurentLattice.provedTheory
#check Guralnick.LaurentLattice.dimension_degree
#check Guralnick.LaurentLattice.periodEquiv

/- Global completion and the exact rational coordinate model comparisons. -/
#print axioms Guralnick.LatticeCompletion.algebraize_complete
#print axioms Guralnick.LatticeCompletion.complete_algebraize
#print axioms Guralnick.LatticeCompletion.orderIso
#print axioms Guralnick.LatticeCompletion.quotientEquiv
#print axioms Guralnick.LatticeCompletion.complete_degree
#print axioms Guralnick.LatticeCompletion.complete_cyclic_iff
#print axioms Guralnick.PolynomialLattice.vectorInclusion_monomial
#print axioms Guralnick.PolynomialAffineCoordinates.complete_coordinateLattice
#print axioms Guralnick.PolynomialAffineCoordinates.complete_window_coordinateModule
#print axioms Guralnick.SLCoordinate.evaluation_ker_eq_determinantIdeal
#print axioms Guralnick.SLCoordinate.quotientDeterminantEquiv
#print axioms Guralnick.SLCoordinate.comultiplication_coordinate
#print axioms Guralnick.SLCoordinate.antipode_apply
#print axioms Guralnick.SLCoordinate.coordinateHopfAlgebra
#print axioms Guralnick.CoordinateTensor.regularEquiv
#print axioms Guralnick.CoordinateTensor.linearEvaluation_injective
#print axioms Guralnick.RationalCoordinate.coaction_coassociative
#print axioms Guralnick.RationalCoordinate.dOne_dZero
#print axioms Guralnick.RationalCoordinate.h1Equiv
#print axioms Guralnick.RationalCoordinate.cocycle_identity
#print axioms Guralnick.RationalCoordinate.empty_rank_cocycles_subsingleton
#print axioms Guralnick.RationalCoordinate.toCoordinateRepresentation_pointRep
#print axioms Guralnick.RationalCoordinate.coordinateRepresentation_roundtrip_full
#print axioms Guralnick.RationalCoordinate.intertwiner_iff
#print axioms Guralnick.RationalCoordinate.invariant_subspace_iff
#print axioms Guralnick.CoordinateLiteratureTransfer.andersen_iff_function
#print axioms Guralnick.CoordinateLiteratureTransfer.bnp_iff_function
#print axioms Guralnick.CoordinateLiteratureTransfer.not_absoluteBoundedness
#check Guralnick.RationalCoordinate.h1Equiv
#check Guralnick.CoordinateLiteratureTransfer.not_absoluteBoundedness
#print Guralnick.CoordinateLiteratureTransfer.AndersenAJS
#print Guralnick.CoordinateLiteratureTransfer.BNP
#print axioms Guralnick.PolynomialLattice.exists_basis_extending
#print axioms Guralnick.LatticeEquivariance.subspaceQuotientEquiv
#print axioms Guralnick.LatticeEquivariance.degree_difference
#print axioms Guralnick.LatticeEquivariance.flagEquiv
#print axioms Guralnick.LatticeEquivariance.galleryEquiv

/- The final path starts in the cited polynomial and coordinate-ring models. -/
#print axioms Guralnick.PolynomialFlags.flagEquiv
#print axioms Guralnick.PolynomialFlags.galleryEquiv
#print axioms Guralnick.PolynomialFlags.gallery_finite
#print axioms Guralnick.PolynomialOrbitCoordinates.block_finite
#print axioms Guralnick.PolynomialOrbitCoordinates.cumulative_finite
#print axioms Guralnick.PolynomialOrbitCoordinates.blockEquiv
#print axioms Guralnick.PolynomialOrbitCoordinates.cumulativeEquiv
#print axioms Guralnick.PolynomialOrbitCoordinates.blockCompletionEquiv
#print axioms Guralnick.PolynomialOrbitCoordinates.cumulativeCompletionEquiv
#print axioms Guralnick.PolynomialOrbitCoordinates.Input.toCompleted
#print axioms Guralnick.PolynomialFlagConvolution.gallery_card_of_position
#print axioms Guralnick.PolynomialFlagConvolution.Input.toCompleted
#print axioms Guralnick.PolynomialWebLiterature.toWebLiterature
#print axioms Guralnick.ModelComparisonCounterexample.row_sum
#print axioms Guralnick.ModelComparisonCounterexample.named_row_and_lower_bound
#print axioms Guralnick.ModelComparisonCounterexample.not_absoluteBoundedness
#check Guralnick.ModelComparisonCounterexample.named_row_and_lower_bound
#check Guralnick.ModelComparisonCounterexample.not_absoluteBoundedness
#print Guralnick.PolynomialWebLiterature
#print Guralnick.PolynomialFlagConvolution.Input
#print Guralnick.PolynomialOrbitCoordinates.Input
#print Guralnick.CoordinateLiteratureTransfer.Inputs
#print axioms Guralnick.AffineLatticePosition.coordinateQuotientEquiv
#print axioms Guralnick.AffineLatticePosition.coordinateLattice_degree
#print axioms Guralnick.PolynomialCoordinateFlags.window_degree
#print axioms Guralnick.PolynomialCoordinateFlags.target_node_module
#print axioms Guralnick.PolynomialCoordinateFlags.source_node_module
#print axioms Guralnick.SLCoordinate.standardPairEvaluation_injective
#print axioms Guralnick.PolynomialFlagConvolution.canonicalPair_realization

-- Elementary inputs replaced by actual proofs.
#print axioms Guralnick.HeckeInversion.polynomial_inversion
#print axioms Guralnick.Hecke.Theory.inversion
#print axioms Guralnick.ElementaryCoxeterParabolic.longestData
#print axioms Guralnick.ElementaryCoxeterFinite.standardFiniteLongest
#print axioms Guralnick.ElementaryCoxeterDiagram.diagramInvariance
#print axioms Guralnick.CoordinateSubspace.quotientEquiv
#print axioms Guralnick.CoordinateSubspace.quotient_finrank
#print axioms Guralnick.PolynomialOrbitCounting.provedInput
#print axioms Guralnick.FiniteFlagEnumeration.provedFiniteFlagCounts
#print axioms Guralnick.FiniteFlagEnumeration.fano_flags
#print axioms Guralnick.GeneralLatticeFlagInput.proved
#print axioms Guralnick.SphericalMaps.mergeOfAbsorption
#print axioms Guralnick.ParabolicWeb.Laws.left_eigen
#print axioms Guralnick.ParabolicWeb.Laws.right_eigen
#print axioms Guralnick.ParabolicWeb.Laws.absorption
#print axioms Guralnick.ParabolicWeb.Laws.merge_exists
#print axioms Guralnick.FiniteDoubleCosetMaximum.exists_maximum

#print axioms Guralnick.Hecke.WindowCoxeter.finite_descent
#print axioms Guralnick.OrbitMatrixElementary.toThreeColumnLengthInput
#print Guralnick.OrbitMatrixElementary.DimensionLengthInput

#print axioms Guralnick.ElementaryCoxeterBlockLength.blockLength
#print axioms Guralnick.ElementaryCoxeterLongest.length_ge_of_right_descents
#print axioms Guralnick.ElementaryCoxeterLongest.eq_longest_of_right_descents
#print axioms Guralnick.Hecke.canonical_support_length_le
#print axioms Guralnick.ParabolicStandardSum.standard_sum
#print axioms Guralnick.ParabolicCosetFactorization.length_mul_of_minimal
#print axioms Guralnick.ParabolicIdealInclusion.inclusion

-- Actual complete-flag lifts and the elementary convolution normalization.
#print axioms Guralnick.ParabolicFlagStabilizer.canonical_forget_eq_iff
#print axioms Guralnick.FiniteFlagExtension.exists_full_flag
#print axioms Guralnick.PolynomialFlagExtension.lift_nonempty
#print axioms Guralnick.PolynomialFlagExtension.lift_card_pos
#print axioms Guralnick.PolynomialFlagExtension.full_lift_card
#print axioms Guralnick.FullFlagHeckeConvolution.forget_eq_iff
#print axioms Guralnick.FullFlagHeckeConvolution.value_symmetrizer
#print axioms Guralnick.FullFlagHeckeConvolution.symmetrizer_square_count
#print axioms Guralnick.PolynomialFullLiftCardinality.lift_card_eq
#print axioms Guralnick.PolynomialFullGallery.configurationEquiv
#print axioms Guralnick.PolynomialFullGallery.fullGallery_card
#print axioms Guralnick.FullFlagHeckeConvolution.numerator_coordinate_count
#print axioms Guralnick.PolynomialConvolutionNormalization.scalar_specialize
#print axioms Guralnick.PolynomialConvolutionNormalization.denominator_specialize
#print axioms Guralnick.PolynomialConvolutionNormalization.normalized_raw_of_fullGallery_count
#print axioms Guralnick.PolynomialCanonicalFullFlags.forget_pair
#print axioms Guralnick.PolynomialConvolutionConstruction.fromFullFlag
#print Guralnick.FullFlagHeckeConvolution.OrbitClassification
#print Guralnick.FullFlagHeckeConvolution.Input

-- The remaining matrix dimension identity is also an internal finite sum proof.
#print axioms Guralnick.OrbitDimensionInversions.length_gap
#print axioms Guralnick.OrbitDimensionPairs.matrix_pair_sum
#print axioms Guralnick.OrbitDimensionLabels.compositionEntries_eq
#print axioms Guralnick.OrbitDimensionHistogram.dimension_histogram
#print axioms Guralnick.OrbitDimensionLength.dimensionLength
#print axioms Guralnick.OrbitDimensionLength.threeColumnLength

-- Explicit bridge from the source's symmetrizer ideals to the eigen-corner.
#print axioms Guralnick.FiniteSymmetrizerEigen.left_absorption
#print axioms Guralnick.CanonicalSchurEigenReduction.product_cleared
#print axioms Guralnick.CanonicalSchurEigenReduction.toCompatibility
#print Guralnick.CanonicalSchurEigenReduction.ProductCompatibility

-- Necessity audit: redundant source premises replaced by internal proofs.
#print axioms Guralnick.KLDerivedBar.bar_involutive
#print axioms Guralnick.HeckeEigenCoordinates.eigen_top_doubleMaximal
#print axioms Guralnick.HeckeRefinement.schurCorner_le_corner
#print axioms Guralnick.CanonicalSchurFromRefinement.toCompatibility
#print axioms Guralnick.HighestWeight.family_restrictPrime_nontrivial
#print Guralnick.Hecke.KLRealization
#print Guralnick.LiteratureTransfer.Steinberg

-- Actual seed web coordinates, distinct from supplied KL normalization.
#print axioms Guralnick.SeedWebCoordinates.raw_source
#print axioms Guralnick.SeedWebCoordinates.one_line_source
#print axioms Guralnick.SeedWebCoordinates.corrected_graph_source
#print axioms Guralnick.SeedWebCoordinates.reflected_one_line_source

-- The actual seed Hecke expansion and KL normalization bridge.
#print axioms Guralnick.SeedCosets.length_mul
#print axioms Guralnick.SeedCosets.top_endpoint
#print axioms Guralnick.SeedOneLineIndex.oneLine_eq_canonical
#print axioms Guralnick.SeedRankOne.canonical_identity
#print axioms Guralnick.SeedRankOne.canonical_source
#print axioms Guralnick.SeedRankOne.raw_source
#print axioms Guralnick.SeedRankOne.raw_inverse_convention
#print axioms Guralnick.SeedRankOneConvention.canonical_inverse_identity
#print axioms Guralnick.SeedDecomposition.strong_multiplicity
#print axioms Guralnick.SeedDecomposition.reflected_strong_multiplicity
#print axioms Guralnick.SeedDecomposition.canonical_expansion
#print axioms Guralnick.SeedDecomposition.web_expansion
#print axioms Guralnick.FamilyPolynomialReadout.of_source_coordinate

-- Full seed KL polynomial identities are proved conclusions.
#print axioms Guralnick.SeedPolynomials.rank_one_polynomial
#print axioms Guralnick.SeedPolynomials.rank_one_mu
#print axioms Guralnick.SeedPolynomials.four_web_identity
#print axioms Guralnick.SeedPolynomials.diagonal_source
#print axioms Guralnick.SeedPolynomials.diagonal_polynomial
#print axioms Guralnick.SeedPolynomials.diagonal_mu

#check Guralnick.SeedPolynomials.rank_one_polynomial
#check Guralnick.SeedPolynomials.diagonal_polynomial
#check Guralnick.SeedPolynomials.four_web_identity
