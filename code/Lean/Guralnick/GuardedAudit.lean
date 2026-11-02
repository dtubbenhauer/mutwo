import Guralnick

/-!
# Failing regression checks for the manuscript's verification

The diagnostic audit prints its results for human inspection. These guards
also make the audit target fail if any audited declaration acquires an
unexpected foundational axiom. The typed applications below separately
protect the final theorem interfaces against extra mathematical hypotheses.

Neither check proves the external literature inputs, nor establishes the
faithfulness of their mathematical interpretation. That remains a source
audit recorded in `literature-inputs.md`.
-/

/-- info: 'Guralnick.AffinePermutation.onIntegers_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.AffinePermutation.onIntegers_periodic

/-- info: 'Guralnick.AffinePermutation.sum_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.AffinePermutation.sum_entry

/-- info: 'Guralnick.AffinePermutation.inverse_dotZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.AffinePermutation.inverse_dotZero

/-- info: 'Guralnick.WindowCertificate.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WindowCertificate.check_sound

/-- info: 'Guralnick.WindowCertificate.toAffine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WindowCertificate.toAffine

/-- info: 'Guralnick.Certificates.m2j2_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Certificates.m2j2_family

/-- info: 'Guralnick.Certificates.m5j5_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Certificates.m5j5_matrix

/-- info: 'Guralnick.Certificates.m5j5_dotZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Certificates.m5j5_dotZero

/-- info: 'Guralnick.Certificates.invalid_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Certificates.invalid_rejected

/-- info: 'Guralnick.Family.window_eq_familyWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Family.window_eq_familyWindow

/-- info: 'Guralnick.Family.inverse_dotZero_eq_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Family.inverse_dotZero_eq_coordinate

/-- info: 'Guralnick.Weights.sum_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Weights.sum_coordinates

/-- info: 'Guralnick.Weights.dynkin_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Weights.dynkin_bounds

/-- info: 'Guralnick.Weights.familyWeight_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Weights.familyWeight_nonzero

/-- info: 'Guralnick.Weights.familyWeight_pRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Weights.familyWeight_pRegular

/-- info: 'Guralnick.normalize_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.normalize_critical

/-- info: 'Guralnick.gapFormula_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.gapFormula_odd

/-- info: 'Guralnick.normalize_family_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.normalize_family_critical

/-- info: 'Guralnick.suppliedSeed_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.suppliedSeed_full

/-- info: 'Guralnick.Web.family_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Web.family_wellFormed

/-- info: 'Guralnick.Web.family_boundaries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Web.family_boundaries

/-- info: 'Guralnick.Web.family_incident_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Web.family_incident_conservation

/-- info: 'Guralnick.Web.family_seam_degree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Web.family_seam_degree

/-- info: 'Guralnick.Web.seed_matches_builder' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Web.seed_matches_builder

/-- info: 'Guralnick.Web.rank_one_needs_zero_edge_contraction' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Web.rank_one_needs_zero_edge_contraction

/-- info: 'Guralnick.Positivity.isLowest_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Positivity.isLowest_mul

/-- info: 'Guralnick.Positivity.cancel_lowerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Positivity.cancel_lowerBound

/-- info: 'Guralnick.Positivity.cleared_support_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Positivity.cleared_support_bounds

/-- info: 'Guralnick.Positivity.cleared_constant_of_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Positivity.cleared_constant_of_zero_bound

/-- info: 'Guralnick.Positivity.cleared_zero_or_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Positivity.cleared_zero_or_one

/-- info: 'Guralnick.Positivity.positive_division_is_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Positivity.positive_division_is_invalid

/-- info: 'Guralnick.DegreeBounds.six_positions_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.DegreeBounds.six_positions_of_bounds

/-- info: 'Guralnick.DegreeBounds.boundary_position_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.DegreeBounds.boundary_position_of_bounds

/-- info: 'Guralnick.CentralQuotient.finiteKernelInflationLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CentralQuotient.finiteKernelInflationLinearEquiv

/-- info: 'Guralnick.CentralQuotient.central_quotient_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CentralQuotient.central_quotient_finrank

/-- info: 'Guralnick.CentralQuotient.representation_faithful_of_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CentralQuotient.representation_faithful_of_simple

/-- info: 'Guralnick.Cohomology.h1IsoExtFromTrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Cohomology.h1IsoExtFromTrivial

/-- info: 'Guralnick.Cohomology.rowSum_and_lowerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Cohomology.rowSum_and_lowerBound

/-- info: 'Guralnick.Cohomology.exists_PSL_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Cohomology.exists_PSL_counterexample

/-- info: 'Guralnick.Cohomology.not_algebraicallyClosedBoundedness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Cohomology.not_algebraicallyClosedBoundedness

/-- info: 'Guralnick.Family.upper_matrixEntry_eq_prescribedArray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Family.upper_matrixEntry_eq_prescribedArray

/-- info: 'Guralnick.Hecke.family_length_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Hecke.family_length_gap

/-- info: 'Guralnick.Hecke.familyMu_inverse_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Hecke.familyMu_inverse_canonical

/-- info: 'Guralnick.WebMasks.stage_masks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebMasks.stage_masks

/-- info: 'Guralnick.ParabolicWeb.Family.raw_cleared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicWeb.Family.raw_cleared

/-- info: 'Guralnick.ParabolicWeb.Family.raw_cleared_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicWeb.Family.raw_cleared_nonnegative

/-- info: 'Guralnick.MainGalleryCount.main_gallery_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.MainGalleryCount.main_gallery_count

/-- info: 'Guralnick.MainSourceCoordinate.raw_source_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.MainSourceCoordinate.raw_source_coordinate

/-- info: 'Guralnick.MainPacketCoordinate.raw_packet_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.MainPacketCoordinate.raw_packet_coordinate

/-- info: 'Guralnick.MainCanonicalSupport.raw_six_position_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.MainCanonicalSupport.raw_six_position_support

/-- info: 'Guralnick.MainFamilyCoordinate.marked_raw_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.MainFamilyCoordinate.marked_raw_coordinate

/-- info: 'Guralnick.PacketIndexClassification.typeF_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PacketIndexClassification.typeF_index

/-- info: 'Guralnick.PacketIndexClassification.full_pattern_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PacketIndexClassification.full_pattern_index

/-- info: 'Guralnick.PacketCoarsening.strong_doubleMaximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PacketCoarsening.strong_doubleMaximal

/-- info: 'Guralnick.PacketCoarsening.weak_doubleMaximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PacketCoarsening.weak_doubleMaximal

/-- info: 'Guralnick.CanonicalOneLineEvaluation.canonical_of_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalOneLineEvaluation.canonical_of_leading

/-- info: 'Guralnick.CanonicalOneLinePatterns.strong_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalOneLinePatterns.strong_canonical

/-- info: 'Guralnick.CanonicalOneLinePatterns.weakDual_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalOneLinePatterns.weakDual_canonical

/-- info: 'Guralnick.CanonicalSphericalTransition.transition_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalSphericalTransition.transition_matrix

/-- info: 'Guralnick.CanonicalRefinement.spherical_at_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalRefinement.spherical_at_family

/-- info: 'Guralnick.CanonicalAuxiliaryMargins.strong_source_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalAuxiliaryMargins.strong_source_product

/-- info: 'Guralnick.OneLineSpecialization.strong_at_marked_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.OneLineSpecialization.strong_at_marked_margin

/-- info: 'Guralnick.OneLineSpecialization.weak_at_spherical_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.OneLineSpecialization.weak_at_spherical_margin

/-- info: 'Guralnick.Gaussian.normalized_Q_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Gaussian.normalized_Q_critical

/-- info: 'Guralnick.CanonicalFullCorrection.corrected_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalFullCorrection.corrected_critical

/-- info: 'Guralnick.WebLiterature.auxiliary_family_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebLiterature.auxiliary_family_bound

/-- info: 'Guralnick.WebLiterature.nonspherical_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebLiterature.nonspherical_bound

/-- info: 'Guralnick.WebLiterature.auxiliary_source_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebLiterature.auxiliary_source_bound

/-- info: 'Guralnick.WebProof.row_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebProof.row_sum

/-- info: 'Guralnick.HighestWeight.root_lattice_center_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.HighestWeight.root_lattice_center_trivial

/-- info: 'Guralnick.SLQuotient.center_order_invertible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SLQuotient.center_order_invertible

/-- info: 'Guralnick.SLQuotient.descended_h1_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SLQuotient.descended_h1_dimension

/-- info: 'Guralnick.Cohomology.irreducible_absolutelyIrreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Cohomology.irreducible_absolutelyIrreducible

/-- info: 'Guralnick.LiteratureTransfer.familyModule_h1_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LiteratureTransfer.familyModule_h1_dimension

/-- info: 'Guralnick.LiteratureTransfer.familyModule_absolutelyAdmissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LiteratureTransfer.familyModule_absolutelyAdmissible

/-- info: 'Guralnick.WebProof.named_row_and_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebProof.named_row_and_lower_bound

/-- info: 'Guralnick.WebProof.not_absoluteBoundedness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebProof.not_absoluteBoundedness

/-- info: 'Guralnick.FidelityKL.normalize_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityKL.normalize_injective

/-- info: 'Guralnick.FidelityKL.standard_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityKL.standard_eq

/-- info: 'Guralnick.FidelityKL.bar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityKL.bar_eq

/-- info: 'Guralnick.FidelityKL.bar_fixed_positive_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityKL.bar_fixed_positive_zero

/-- info: 'Guralnick.FidelityKL.canonical_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityKL.canonical_eq

/-- info: 'Guralnick.FidelityKL.polynomial_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityKL.polynomial_eq

/-- info: 'Guralnick.FidelityKL.familyMu_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityKL.familyMu_eq

/-- info: 'Guralnick.FidelityWeb.family_frontiers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityWeb.family_frontiers

/-- info: 'Guralnick.FidelityWeights.dynkin_eq_manuscript' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityWeights.dynkin_eq_manuscript

/-- info: 'Guralnick.FidelityWeights.coordinate_eq_manuscript' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityWeights.coordinate_eq_manuscript

/-- info: 'Guralnick.FidelityWeights.etaCoordinate_eq_fundamental' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityWeights.etaCoordinate_eq_fundamental

/-- info: 'Guralnick.FidelityWeights.etaCoordinate_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityWeights.etaCoordinate_sum

/-- info: 'Guralnick.FidelityWeights.m2_j1_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityWeights.m2_j1_labels

/-- info: 'Guralnick.FidelityWeights.m2_j2_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FidelityWeights.m2_j2_labels

/-- info: 'Guralnick.WebBoundary.Family.mem_index_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebBoundary.Family.mem_index_iff

/-- info: 'Guralnick.WebBoundary.Family.local_relations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebBoundary.Family.local_relations

/-- info: 'Guralnick.WebTrace.family_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTrace.family_step

/-- info: 'Guralnick.WebTrace.familyState_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTrace.familyState_boundary

/-- info: 'Guralnick.WebTrace.family_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTrace.family_graph

/-- info: 'Guralnick.WebTrace.family_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTrace.family_frontier

/-- info: 'Guralnick.WebTraceWinding.step_mass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceWinding.step_mass

/-- info: 'Guralnick.WebTraceWinding.run_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceWinding.run_charge

/-- info: 'Guralnick.WebTraceWinding.run_zero_cut_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceWinding.run_zero_cut_seam

/-- info: 'Guralnick.WebTraceWinding.single_packet_turn_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceWinding.single_packet_turn_rejected

/-- info: 'Guralnick.WebTraceWinding.consecutive_right_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceWinding.consecutive_right_rejected

/-- info: 'Guralnick.WebRecutPositions.step_right_positions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebRecutPositions.step_right_positions

/-- info: 'Guralnick.WebRecutPositions.step_left_positions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebRecutPositions.step_left_positions

/-- info: 'Guralnick.WebPresentedWinding.seamDegree_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebPresentedWinding.seamDegree_zero

/-- info: 'Guralnick.WebPresentedWinding.not_presentable_of_nonzero_seam' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebPresentedWinding.not_presentable_of_nonzero_seam

/-- info: 'Guralnick.WebEvaluation.merge_linear_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebEvaluation.merge_linear_unique

/-- info: 'Guralnick.WebEvaluation.merge_comp_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebEvaluation.merge_comp_unique

/-- info: 'Guralnick.WebEvaluationCompression.Resolution.fine_linear_eq_coarse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebEvaluationCompression.Resolution.fine_linear_eq_coarse

/-- info: 'Guralnick.WebTraceEvaluation.Program.replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceEvaluation.Program.replay

/-- info: 'Guralnick.WebTraceEvaluation.familyProgram_operations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceEvaluation.familyProgram_operations

/-- info: 'Guralnick.WebTraceEvaluation.familyPresentedGraph_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceEvaluation.familyPresentedGraph_replay

/-- info: 'Guralnick.WebTraceEvaluation.family_graph_evaluation_eq_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceEvaluation.family_graph_evaluation_eq_raw

/-- info: 'Guralnick.WebRightLinearity.program_rightLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebRightLinearity.program_rightLinear

/-- info: 'Guralnick.WebRightLinearity.ext_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebRightLinearity.ext_generator

/-- info: 'Guralnick.WebProof.graph_morphism_eq_sixMaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebProof.graph_morphism_eq_sixMaps

/-- info: 'Guralnick.WebProof.graph_standard_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebProof.graph_standard_coordinates

/-- info: 'Guralnick.WebProof.graph_canonical_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebProof.graph_canonical_coordinates

/-- info: 'Guralnick.WebProof.graph_corrected_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebProof.graph_corrected_source

/-- info: 'Guralnick.WebProof.graph_corrected_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebProof.graph_corrected_critical

/-- info: 'Guralnick.WebProof.graph_critical_eq_row_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebProof.graph_critical_eq_row_sum

/-- info: 'Guralnick.WebTrace.seed_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTrace.seed_replay

/-- info: 'Guralnick.WebTrace.rank_one_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTrace.rank_one_rejected

/-- info: 'Guralnick.WebTrace.erased_graph_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTrace.erased_graph_rejected

/-- info: 'Guralnick.WebTraceSeamExample.ordinary_merge_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceSeamExample.ordinary_merge_index

/-- info: 'Guralnick.WebTraceSeamExample.seam_merge_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceSeamExample.seam_merge_index

/-- info: 'Guralnick.WebTraceSeamExample.seam_channel_replay' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceSeamExample.seam_channel_replay

/-- info: 'Guralnick.WebTraceSeamExample.seam_channel_winding' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.WebTraceSeamExample.seam_channel_winding

/-- info: 'Guralnick.ParabolicWeb.scalar_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicWeb.scalar_ne_zero

/-- info: 'Guralnick.ParabolicWeb.Laws.scalar_bar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicWeb.Laws.scalar_bar

/-- info: 'Guralnick.LaurentLattice.interval_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.interval_lift

/-- info: 'Guralnick.LaurentLattice.intervalLattice_source_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.intervalLattice_source_eq

/-- info: 'Guralnick.LaurentLattice.intervalLattice_upper_module' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.intervalLattice_upper_module

/-- info: 'Guralnick.LaurentLattice.latticeBasis_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.latticeBasis_card

/-- info: 'Guralnick.LaurentLattice.periodCoefficients_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.periodCoefficients_kernel

/-- info: 'Guralnick.LaurentLattice.periodEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.periodEquiv

/-- info: 'Guralnick.LaurentLattice.period_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.period_finite

/-- info: 'Guralnick.LaurentLattice.period_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.period_dimension

/-- info: 'Guralnick.LaurentLattice.exists_X_pow_smul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.exists_X_pow_smul_le

/-- info: 'Guralnick.LaurentLattice.finite_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.finite_quotient

/-- info: 'Guralnick.LaurentLattice.standardLattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.standardLattice

/-- info: 'Guralnick.LaurentLattice.interLattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.interLattice

/-- info: 'Guralnick.LatticeGallery.relative_degree_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeGallery.relative_degree_difference

/-- info: 'Guralnick.LaurentLattice.dimension_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.dimension_degree

/-- info: 'Guralnick.LaurentLattice.provedTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.provedTheory

/-- info: 'Guralnick.GeneralLatticeFlagInput.lattice_theory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.GeneralLatticeFlagInput.lattice_theory

/-- info: 'Guralnick.PowerSeriesCompletion.completionEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PowerSeriesCompletion.completionEquiv

/-- info: 'Guralnick.PowerSeriesCompletion.completion_parameter_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PowerSeriesCompletion.completion_parameter_mul

/-- info: 'Guralnick.PowerSeriesCompletion.stableSubspaceEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PowerSeriesCompletion.stableSubspaceEquiv

/-- info: 'Guralnick.PowerSeriesCompletion.subspace_inf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PowerSeriesCompletion.subspace_inf

/-- info: 'Guralnick.PowerSeriesCompletion.subspace_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PowerSeriesCompletion.subspace_sup

/-- info: 'Guralnick.PowerSeriesCompletion.series_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PowerSeriesCompletion.series_finrank

/-- info: 'Guralnick.PowerSeriesCompletion.quotient_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PowerSeriesCompletion.quotient_finrank

/-- info: 'Guralnick.LaurentLattice.XStable_iff_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.XStable_iff_lattice

/-- info: 'Guralnick.LaurentLattice.truncatedIntervalIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.truncatedIntervalIso

/-- info: 'Guralnick.LaurentLattice.truncatedLattice_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.truncatedLattice_zero

/-- info: 'Guralnick.LaurentLattice.truncatedLattice_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LaurentLattice.truncatedLattice_one

/-- info: 'Guralnick.LatticeCompletion.algebraize_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeCompletion.algebraize_complete

/-- info: 'Guralnick.LatticeCompletion.complete_algebraize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeCompletion.complete_algebraize

/-- info: 'Guralnick.LatticeCompletion.orderIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeCompletion.orderIso

/-- info: 'Guralnick.LatticeCompletion.quotientEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeCompletion.quotientEquiv

/-- info: 'Guralnick.LatticeCompletion.complete_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeCompletion.complete_degree

/-- info: 'Guralnick.LatticeCompletion.complete_cyclic_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeCompletion.complete_cyclic_iff

/-- info: 'Guralnick.PolynomialLattice.vectorInclusion_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialLattice.vectorInclusion_monomial

/-- info: 'Guralnick.PolynomialAffineCoordinates.complete_coordinateLattice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialAffineCoordinates.complete_coordinateLattice

/-- info: 'Guralnick.PolynomialAffineCoordinates.complete_window_coordinateModule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialAffineCoordinates.complete_window_coordinateModule

/-- info: 'Guralnick.SLCoordinate.evaluation_ker_eq_determinantIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SLCoordinate.evaluation_ker_eq_determinantIdeal

/-- info: 'Guralnick.SLCoordinate.quotientDeterminantEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SLCoordinate.quotientDeterminantEquiv

/-- info: 'Guralnick.SLCoordinate.comultiplication_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SLCoordinate.comultiplication_coordinate

/-- info: 'Guralnick.SLCoordinate.antipode_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SLCoordinate.antipode_apply

/-- info: 'Guralnick.SLCoordinate.coordinateHopfAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SLCoordinate.coordinateHopfAlgebra

/-- info: 'Guralnick.CoordinateTensor.regularEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CoordinateTensor.regularEquiv

/-- info: 'Guralnick.CoordinateTensor.linearEvaluation_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CoordinateTensor.linearEvaluation_injective

/-- info: 'Guralnick.RationalCoordinate.coaction_coassociative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.RationalCoordinate.coaction_coassociative

/-- info: 'Guralnick.RationalCoordinate.dOne_dZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.RationalCoordinate.dOne_dZero

/-- info: 'Guralnick.RationalCoordinate.h1Equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.RationalCoordinate.h1Equiv

/-- info: 'Guralnick.RationalCoordinate.cocycle_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.RationalCoordinate.cocycle_identity

/-- info: 'Guralnick.RationalCoordinate.empty_rank_cocycles_subsingleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.RationalCoordinate.empty_rank_cocycles_subsingleton

/-- info: 'Guralnick.RationalCoordinate.toCoordinateRepresentation_pointRep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.RationalCoordinate.toCoordinateRepresentation_pointRep

/-- info: 'Guralnick.RationalCoordinate.coordinateRepresentation_roundtrip_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.RationalCoordinate.coordinateRepresentation_roundtrip_full

/-- info: 'Guralnick.RationalCoordinate.intertwiner_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.RationalCoordinate.intertwiner_iff

/-- info: 'Guralnick.RationalCoordinate.invariant_subspace_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.RationalCoordinate.invariant_subspace_iff

/-- info: 'Guralnick.CoordinateLiteratureTransfer.andersen_iff_function' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CoordinateLiteratureTransfer.andersen_iff_function

/-- info: 'Guralnick.CoordinateLiteratureTransfer.bnp_iff_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CoordinateLiteratureTransfer.bnp_iff_function

/-- info: 'Guralnick.CoordinateLiteratureTransfer.not_absoluteBoundedness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CoordinateLiteratureTransfer.not_absoluteBoundedness

/-- info: 'Guralnick.PolynomialLattice.exists_basis_extending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialLattice.exists_basis_extending

/-- info: 'Guralnick.LatticeEquivariance.subspaceQuotientEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeEquivariance.subspaceQuotientEquiv

/-- info: 'Guralnick.LatticeEquivariance.degree_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeEquivariance.degree_difference

/-- info: 'Guralnick.LatticeEquivariance.flagEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeEquivariance.flagEquiv

/-- info: 'Guralnick.LatticeEquivariance.galleryEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.LatticeEquivariance.galleryEquiv

/-- info: 'Guralnick.PolynomialFlags.flagEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFlags.flagEquiv

/-- info: 'Guralnick.PolynomialFlags.galleryEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFlags.galleryEquiv

/-- info: 'Guralnick.PolynomialFlags.gallery_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFlags.gallery_finite

/-- info: 'Guralnick.PolynomialOrbitCoordinates.block_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialOrbitCoordinates.block_finite

/-- info: 'Guralnick.PolynomialOrbitCoordinates.cumulative_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialOrbitCoordinates.cumulative_finite

/-- info: 'Guralnick.PolynomialOrbitCoordinates.blockEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialOrbitCoordinates.blockEquiv

/-- info: 'Guralnick.PolynomialOrbitCoordinates.cumulativeEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialOrbitCoordinates.cumulativeEquiv

/-- info: 'Guralnick.PolynomialOrbitCoordinates.blockCompletionEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialOrbitCoordinates.blockCompletionEquiv

/-- info: 'Guralnick.PolynomialOrbitCoordinates.cumulativeCompletionEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialOrbitCoordinates.cumulativeCompletionEquiv

/-- info: 'Guralnick.PolynomialOrbitCoordinates.Input.toCompleted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialOrbitCoordinates.Input.toCompleted

/-- info: 'Guralnick.PolynomialFlagConvolution.gallery_card_of_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFlagConvolution.gallery_card_of_position

/-- info: 'Guralnick.PolynomialFlagConvolution.Input.toCompleted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFlagConvolution.Input.toCompleted

/-- info: 'Guralnick.PolynomialWebLiterature.toWebLiterature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialWebLiterature.toWebLiterature

/-- info: 'Guralnick.ModelComparisonCounterexample.row_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ModelComparisonCounterexample.row_sum

/-- info: 'Guralnick.ModelComparisonCounterexample.named_row_and_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ModelComparisonCounterexample.named_row_and_lower_bound

/-- info: 'Guralnick.ModelComparisonCounterexample.not_absoluteBoundedness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ModelComparisonCounterexample.not_absoluteBoundedness

/-- info: 'Guralnick.AffineLatticePosition.coordinateQuotientEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.AffineLatticePosition.coordinateQuotientEquiv

/-- info: 'Guralnick.AffineLatticePosition.coordinateLattice_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.AffineLatticePosition.coordinateLattice_degree

/-- info: 'Guralnick.PolynomialCoordinateFlags.window_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialCoordinateFlags.window_degree

/-- info: 'Guralnick.PolynomialCoordinateFlags.target_node_module' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialCoordinateFlags.target_node_module

/-- info: 'Guralnick.PolynomialCoordinateFlags.source_node_module' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialCoordinateFlags.source_node_module

/-- info: 'Guralnick.SLCoordinate.standardPairEvaluation_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SLCoordinate.standardPairEvaluation_injective

/-- info: 'Guralnick.PolynomialFlagConvolution.canonicalPair_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFlagConvolution.canonicalPair_realization

/-- info: 'Guralnick.HeckeInversion.polynomial_inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.HeckeInversion.polynomial_inversion

/-- info: 'Guralnick.Hecke.Theory.inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Hecke.Theory.inversion

/-- info: 'Guralnick.ElementaryCoxeterParabolic.longestData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ElementaryCoxeterParabolic.longestData

/-- info: 'Guralnick.ElementaryCoxeterFinite.standardFiniteLongest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ElementaryCoxeterFinite.standardFiniteLongest

/-- info: 'Guralnick.ElementaryCoxeterDiagram.diagramInvariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ElementaryCoxeterDiagram.diagramInvariance

/-- info: 'Guralnick.CoordinateSubspace.quotientEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CoordinateSubspace.quotientEquiv

/-- info: 'Guralnick.CoordinateSubspace.quotient_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CoordinateSubspace.quotient_finrank

/-- info: 'Guralnick.PolynomialOrbitCounting.provedInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialOrbitCounting.provedInput

/-- info: 'Guralnick.FiniteFlagEnumeration.provedFiniteFlagCounts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FiniteFlagEnumeration.provedFiniteFlagCounts

/-- info: 'Guralnick.FiniteFlagEnumeration.fano_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FiniteFlagEnumeration.fano_flags

/-- info: 'Guralnick.GeneralLatticeFlagInput.proved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.GeneralLatticeFlagInput.proved

/-- info: 'Guralnick.SphericalMaps.mergeOfAbsorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SphericalMaps.mergeOfAbsorption

/-- info: 'Guralnick.ParabolicWeb.Laws.left_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicWeb.Laws.left_eigen

/-- info: 'Guralnick.ParabolicWeb.Laws.right_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicWeb.Laws.right_eigen

/-- info: 'Guralnick.ParabolicWeb.Laws.absorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicWeb.Laws.absorption

/-- info: 'Guralnick.ParabolicWeb.Laws.merge_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicWeb.Laws.merge_exists

/-- info: 'Guralnick.FiniteDoubleCosetMaximum.exists_maximum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FiniteDoubleCosetMaximum.exists_maximum

/-- info: 'Guralnick.Hecke.WindowCoxeter.finite_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Hecke.WindowCoxeter.finite_descent

/-- info: 'Guralnick.OrbitMatrixElementary.toThreeColumnLengthInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.OrbitMatrixElementary.toThreeColumnLengthInput

/-- info: 'Guralnick.ElementaryCoxeterBlockLength.blockLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ElementaryCoxeterBlockLength.blockLength

/-- info: 'Guralnick.ElementaryCoxeterLongest.length_ge_of_right_descents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ElementaryCoxeterLongest.length_ge_of_right_descents

/-- info: 'Guralnick.ElementaryCoxeterLongest.eq_longest_of_right_descents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ElementaryCoxeterLongest.eq_longest_of_right_descents

/-- info: 'Guralnick.Hecke.canonical_support_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.Hecke.canonical_support_length_le

/-- info: 'Guralnick.ParabolicStandardSum.standard_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicStandardSum.standard_sum

/-- info: 'Guralnick.ParabolicCosetFactorization.length_mul_of_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicCosetFactorization.length_mul_of_minimal

/-- info: 'Guralnick.ParabolicIdealInclusion.inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicIdealInclusion.inclusion

/-- info: 'Guralnick.ParabolicFlagStabilizer.canonical_forget_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ParabolicFlagStabilizer.canonical_forget_eq_iff

/-- info: 'Guralnick.FiniteFlagExtension.exists_full_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FiniteFlagExtension.exists_full_flag

/-- info: 'Guralnick.PolynomialFlagExtension.lift_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFlagExtension.lift_nonempty

/-- info: 'Guralnick.PolynomialFlagExtension.lift_card_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFlagExtension.lift_card_pos

/-- info: 'Guralnick.PolynomialFlagExtension.full_lift_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFlagExtension.full_lift_card

/-- info: 'Guralnick.FullFlagHeckeConvolution.forget_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FullFlagHeckeConvolution.forget_eq_iff

/-- info: 'Guralnick.FullFlagHeckeConvolution.value_symmetrizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FullFlagHeckeConvolution.value_symmetrizer

/-- info: 'Guralnick.FullFlagHeckeConvolution.symmetrizer_square_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FullFlagHeckeConvolution.symmetrizer_square_count

/-- info: 'Guralnick.PolynomialFullLiftCardinality.lift_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFullLiftCardinality.lift_card_eq

/-- info: 'Guralnick.PolynomialFullGallery.configurationEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFullGallery.configurationEquiv

/-- info: 'Guralnick.PolynomialFullGallery.fullGallery_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialFullGallery.fullGallery_card

/-- info: 'Guralnick.FullFlagHeckeConvolution.numerator_coordinate_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FullFlagHeckeConvolution.numerator_coordinate_count

/-- info: 'Guralnick.PolynomialConvolutionNormalization.scalar_specialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialConvolutionNormalization.scalar_specialize

/-- info: 'Guralnick.PolynomialConvolutionNormalization.denominator_specialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialConvolutionNormalization.denominator_specialize

/-- info: 'Guralnick.PolynomialConvolutionNormalization.normalized_raw_of_fullGallery_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialConvolutionNormalization.normalized_raw_of_fullGallery_count

/-- info: 'Guralnick.PolynomialCanonicalFullFlags.forget_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialCanonicalFullFlags.forget_pair

/-- info: 'Guralnick.PolynomialConvolutionConstruction.fromFullFlag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.PolynomialConvolutionConstruction.fromFullFlag

/-- info: 'Guralnick.OrbitDimensionInversions.length_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.OrbitDimensionInversions.length_gap

/-- info: 'Guralnick.OrbitDimensionPairs.matrix_pair_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.OrbitDimensionPairs.matrix_pair_sum

/-- info: 'Guralnick.OrbitDimensionLabels.compositionEntries_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.OrbitDimensionLabels.compositionEntries_eq

/-- info: 'Guralnick.OrbitDimensionHistogram.dimension_histogram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.OrbitDimensionHistogram.dimension_histogram

/-- info: 'Guralnick.OrbitDimensionLength.dimensionLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.OrbitDimensionLength.dimensionLength

/-- info: 'Guralnick.OrbitDimensionLength.threeColumnLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.OrbitDimensionLength.threeColumnLength

/-- info: 'Guralnick.FiniteSymmetrizerEigen.left_absorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FiniteSymmetrizerEigen.left_absorption

/-- info: 'Guralnick.CanonicalSchurEigenReduction.product_cleared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalSchurEigenReduction.product_cleared

/-- info: 'Guralnick.CanonicalSchurEigenReduction.toCompatibility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalSchurEigenReduction.toCompatibility

/-- info: 'Guralnick.KLDerivedBar.bar_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.KLDerivedBar.bar_involutive

/-- info: 'Guralnick.HeckeEigenCoordinates.eigen_top_doubleMaximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.HeckeEigenCoordinates.eigen_top_doubleMaximal

/-- info: 'Guralnick.HeckeRefinement.schurCorner_le_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.HeckeRefinement.schurCorner_le_corner

/-- info: 'Guralnick.CanonicalSchurFromRefinement.toCompatibility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.CanonicalSchurFromRefinement.toCompatibility

/-- info: 'Guralnick.HighestWeight.family_restrictPrime_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.HighestWeight.family_restrictPrime_nontrivial

noncomputable section
open scoped BigOperators
namespace Guralnick.Verification

/-- This application has exactly the original three literature arguments.
An added row-sum, family-transfer, or other explicit mathematical premise
in the final theorem makes this declaration fail to elaborate. -/
theorem finalStatement (T : Hecke.TheoryFamily)
    (W : ∀ m hm, PolynomialWebLiterature (T m hm))
    (I : CoordinateLiteratureTransfer.Inputs T) :
    ¬Cohomology.AbsoluteBoundedness :=
  ModelComparisonCounterexample.not_absoluteBoundedness T W I

/-- The row theorem retains the actual fixed-source ordinary KL family. -/
theorem rowStatement {m : ℕ} (hm : 2 ≤ m) (T : Hecke.Theory (2*m+1))
    (W : PolynomialWebLiterature T) :
    (∑ j : Fin m, Hecke.familyMu hm (show 1 ≤ j.val+1 by omega)
      (show j.val+1 ≤ m by omega) T.kl) = (Nat.choose (m+1) 2 : ℤ) :=
  ModelComparisonCounterexample.row_sum hm T W

/-- The named-module statement retains both characteristic bounds,
absolute admissibility, actual H¹, its row sum and its lower bound. -/
theorem namedFamilyStatement (T : Hecke.TheoryFamily)
    (W : ∀ m hm, PolynomialWebLiterature (T m hm))
    (I : CoordinateLiteratureTransfer.Inputs T)
    (m : ℕ) (hm : 2 ≤ m) (p : ℕ) [Fact p.Prime] (hp : 2*m+1 < p)
    (hp₀ : LiteratureTransfer.threshold I.toFunctionInputs m hm ≤ p)
    (hBNP : 5*(2*m) ≤ p) :
    let A (j : Fin m) := LiteratureTransfer.familyModule I.toFunctionInputs hm
      (show 1 ≤ j.val+1 by omega) (show j.val+1 ≤ m by omega) hp
    (∀ j, Cohomology.AbsolutelyAdmissible (A j)) ∧
    (∀ j, FiniteDimensional (Cohomology.PrimeClosure p) (Cohomology.H1 (A j))) ∧
    2*(∑ j : Fin m, Cohomology.h1Dimension (A j)) = m*(m+1) ∧
    ∃ j : Fin m, m/2+1 ≤ Cohomology.h1Dimension (A j) :=
  ModelComparisonCounterexample.named_row_and_lower_bound T W I m hm p hp hp₀ hBNP

end Guralnick.Verification


/- The displayed types/bodies of the literature interfaces are guarded as
well. Exact endpoint applications alone would not detect an extra field
silently added inside T, W, or I. These guards protect the present bundle
fields and their named substantive predicates; they do not validate the
sources or protect against every possible change in a nested definition. -/

/--
info: structure Guralnick.Hecke.Theory (n : ℕ) : Type
number of parameters: 1
fields:
  Guralnick.Hecke.Theory.coxeter : Guralnick.Hecke.WindowCoxeter n
  Guralnick.Hecke.Theory.kl : Guralnick.Hecke.KLRealization self.coxeter
  Guralnick.Hecke.Theory.positivity : Guralnick.Hecke.PositivityInput self.kl
constructor:
  Guralnick.Hecke.Theory.mk {n : ℕ} (coxeter : Guralnick.Hecke.WindowCoxeter n)
    (kl : Guralnick.Hecke.KLRealization coxeter) (positivity : Guralnick.Hecke.PositivityInput kl) :
    Guralnick.Hecke.Theory n
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.Hecke.Theory

/--
info: structure Guralnick.Hecke.WindowCoxeter (n : ℕ) : Type
number of parameters: 1
fields:
  Guralnick.Hecke.WindowCoxeter.system : CoxeterSystem (Guralnick.AffineCoxeter.matrix n)
      (Guralnick.AffinePermutation n)
  Guralnick.Hecke.WindowCoxeter.simple_window : ∀ (s i : Fin n),
      (self.system.simple s).entry i = Guralnick.Hecke.simpleEntry s i
  Guralnick.Hecke.WindowCoxeter.length_formula : ∀ (w : Guralnick.AffinePermutation n),
      self.system.length w = w.inversionCount
constructor:
  Guralnick.Hecke.WindowCoxeter.mk {n : ℕ}
    (system : CoxeterSystem (Guralnick.AffineCoxeter.matrix n) (Guralnick.AffinePermutation n))
    (simple_window : ∀ (s i : Fin n), (system.simple s).entry i = Guralnick.Hecke.simpleEntry s i)
    (length_formula : ∀ (w : Guralnick.AffinePermutation n), system.length w = w.inversionCount) :
    Guralnick.Hecke.WindowCoxeter n
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.Hecke.WindowCoxeter

/--
info: structure Guralnick.Hecke.KLRealization {n : ℕ} (c : Guralnick.Hecke.WindowCoxeter n) : Type
number of parameters: 2
fields:
  Guralnick.Hecke.KLRealization.standard : Basis (Guralnick.AffinePermutation n) Guralnick.Hecke.R
      (Guralnick.Hecke.Algebra n)
  Guralnick.Hecke.KLRealization.standard_reduced : ∀ (l : List (Fin n)),
      c.system.IsReduced l → self.standard (c.system.wordProd l) = Guralnick.Hecke.word l
  Guralnick.Hecke.KLRealization.bar : Guralnick.Hecke.Algebra n ≃+* Guralnick.Hecke.Algebra n
  Guralnick.Hecke.KLRealization.bar_scalar : ∀ (r : Guralnick.Hecke.R),
      self.bar ((algebraMap Guralnick.Hecke.R (Guralnick.Hecke.Algebra n)) r) =
        (algebraMap Guralnick.Hecke.R (Guralnick.Hecke.Algebra n)) (LaurentPolynomial.invert r)
  Guralnick.Hecke.KLRealization.bar_generator : ∀ (i : Fin n),
      self.bar (Guralnick.Hecke.H i) =
        Guralnick.Hecke.H i +
          (algebraMap Guralnick.Hecke.R (Guralnick.Hecke.Algebra n)) (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1))
  Guralnick.Hecke.KLRealization.canonical : Basis (Guralnick.AffinePermutation n) Guralnick.Hecke.R
      (Guralnick.Hecke.Algebra n)
  Guralnick.Hecke.KLRealization.bar_canonical : ∀ (w : Guralnick.AffinePermutation n),
      self.bar (self.canonical w) = self.canonical w
  Guralnick.Hecke.KLRealization.canonical_diagonal : ∀ (w : Guralnick.AffinePermutation n),
      (self.standard.repr (self.canonical w)) w = 1
  Guralnick.Hecke.KLRealization.canonical_lower : ∀ (y w : Guralnick.AffinePermutation n),
      y ≠ w → Guralnick.Positivity.LowerBound ((self.standard.repr (self.canonical w)) y) 1
  Guralnick.Hecke.KLRealization.canonical_support : ∀ (y w : Guralnick.AffinePermutation n),
      (self.standard.repr (self.canonical w)) y ≠ 0 → Guralnick.Hecke.Bruhat c y w
  Guralnick.Hecke.KLRealization.polynomial : Guralnick.AffinePermutation n →
      Guralnick.AffinePermutation n → Polynomial ℤ
  Guralnick.Hecke.KLRealization.polynomial_normalization : ∀ (y w : Guralnick.AffinePermutation n),
      (self.standard.repr (self.canonical w)) y =
        Guralnick.normalize (↑(c.system.length w) - ↑(c.system.length y)) (self.polynomial y w)
constructor:
  Guralnick.Hecke.KLRealization.mk {n : ℕ} {c : Guralnick.Hecke.WindowCoxeter n}
    (standard : Basis (Guralnick.AffinePermutation n) Guralnick.Hecke.R (Guralnick.Hecke.Algebra n))
    (standard_reduced :
      ∀ (l : List (Fin n)), c.system.IsReduced l → standard (c.system.wordProd l) = Guralnick.Hecke.word l)
    (bar : Guralnick.Hecke.Algebra n ≃+* Guralnick.Hecke.Algebra n)
    (bar_scalar :
      ∀ (r : Guralnick.Hecke.R),
        bar ((algebraMap Guralnick.Hecke.R (Guralnick.Hecke.Algebra n)) r) =
          (algebraMap Guralnick.Hecke.R (Guralnick.Hecke.Algebra n)) (LaurentPolynomial.invert r))
    (bar_generator :
      ∀ (i : Fin n),
        bar (Guralnick.Hecke.H i) =
          Guralnick.Hecke.H i +
            (algebraMap Guralnick.Hecke.R (Guralnick.Hecke.Algebra n))
              (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)))
    (canonical : Basis (Guralnick.AffinePermutation n) Guralnick.Hecke.R (Guralnick.Hecke.Algebra n))
    (bar_canonical : ∀ (w : Guralnick.AffinePermutation n), bar (canonical w) = canonical w)
    (canonical_diagonal : ∀ (w : Guralnick.AffinePermutation n), (standard.repr (canonical w)) w = 1)
    (canonical_lower :
      ∀ (y w : Guralnick.AffinePermutation n),
        y ≠ w → Guralnick.Positivity.LowerBound ((standard.repr (canonical w)) y) 1)
    (canonical_support :
      ∀ (y w : Guralnick.AffinePermutation n), (standard.repr (canonical w)) y ≠ 0 → Guralnick.Hecke.Bruhat c y w)
    (polynomial : Guralnick.AffinePermutation n → Guralnick.AffinePermutation n → Polynomial ℤ)
    (polynomial_normalization :
      ∀ (y w : Guralnick.AffinePermutation n),
        (standard.repr (canonical w)) y =
          Guralnick.normalize (↑(c.system.length w) - ↑(c.system.length y)) (polynomial y w)) :
    Guralnick.Hecke.KLRealization c
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.Hecke.KLRealization

/--
info: structure Guralnick.Hecke.PositivityInput {n : ℕ} {c : Guralnick.Hecke.WindowCoxeter n}
  (K : Guralnick.Hecke.KLRealization c) : Prop
number of parameters: 3
fields:
  Guralnick.Hecke.PositivityInput.standard_nonnegative : ∀ (y w : Guralnick.AffinePermutation n),
      Guralnick.Positivity.Nonnegative ((K.standard.repr (K.canonical w)) y)
  Guralnick.Hecke.PositivityInput.product_nonnegative : ∀ (x y z : Guralnick.AffinePermutation n),
      Guralnick.Positivity.Nonnegative ((K.canonical.repr (K.canonical x * K.canonical y)) z)
constructor:
  Guralnick.Hecke.PositivityInput.mk {n : ℕ} {c : Guralnick.Hecke.WindowCoxeter n} {K : Guralnick.Hecke.KLRealization c}
    (standard_nonnegative :
      ∀ (y w : Guralnick.AffinePermutation n), Guralnick.Positivity.Nonnegative ((K.standard.repr (K.canonical w)) y))
    (product_nonnegative :
      ∀ (x y z : Guralnick.AffinePermutation n),
        Guralnick.Positivity.Nonnegative ((K.canonical.repr (K.canonical x * K.canonical y)) z)) :
    Guralnick.Hecke.PositivityInput K
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.Hecke.PositivityInput

/--
info: structure Guralnick.CanonicalRefinement.StandardCompatibility {n : ℕ} {c : Guralnick.Hecke.WindowCoxeter n}
  (K : Guralnick.Hecke.KLRealization c)
  (D : (I : Guralnick.ParabolicWeb.Index n) → Guralnick.ParabolicWeb.LongestData c I) : Prop
number of parameters: 4
fields:
  Guralnick.CanonicalRefinement.StandardCompatibility.canonical_span : ∀ (I J : Guralnick.ParabolicWeb.Index n)
      (w : Guralnick.AffinePermutation n),
      Guralnick.CanonicalSchur.DoubleMaximal c I J w →
        K.canonical w ∈
          Guralnick.HeckeRefinement.SchurCorner K (Guralnick.ParabolicWeb.subgroup c I)
            (Guralnick.ParabolicWeb.subgroup c J)
constructor:
  Guralnick.CanonicalRefinement.StandardCompatibility.mk {n : ℕ} {c : Guralnick.Hecke.WindowCoxeter n}
    {K : Guralnick.Hecke.KLRealization c}
    {D : (I : Guralnick.ParabolicWeb.Index n) → Guralnick.ParabolicWeb.LongestData c I}
    (canonical_span :
      ∀ (I J : Guralnick.ParabolicWeb.Index n) (w : Guralnick.AffinePermutation n),
        Guralnick.CanonicalSchur.DoubleMaximal c I J w →
          K.canonical w ∈
            Guralnick.HeckeRefinement.SchurCorner K (Guralnick.ParabolicWeb.subgroup c I)
              (Guralnick.ParabolicWeb.subgroup c J)) :
    Guralnick.CanonicalRefinement.StandardCompatibility K D
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.CanonicalRefinement.StandardCompatibility

/--
info: structure Guralnick.PolynomialWebLiterature {n : ℕ} [NeZero n] (T : Guralnick.Hecke.Theory n) : Prop
number of parameters: 3
fields:
  Guralnick.PolynomialWebLiterature.refinement : Guralnick.CanonicalRefinement.StandardCompatibility T.kl
      (Guralnick.polynomialLongest T)
  Guralnick.PolynomialWebLiterature.full_flag : ∀ (p : ℕ) (hp : Nat.Prime p),
      Guralnick.FullFlagHeckeConvolution.Input T.kl p hp
constructor:
  Guralnick.PolynomialWebLiterature.mk {n : ℕ} [NeZero n] {T : Guralnick.Hecke.Theory n}
    (refinement : Guralnick.CanonicalRefinement.StandardCompatibility T.kl (Guralnick.polynomialLongest T))
    (full_flag : ∀ (p : ℕ) (hp : Nat.Prime p), Guralnick.FullFlagHeckeConvolution.Input T.kl p hp) :
    Guralnick.PolynomialWebLiterature T
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.PolynomialWebLiterature

/--
info: def Guralnick.FullFlagHeckeConvolution.OrbitClassification : (k : Type) → [Field k] → (n : ℕ) → [NeZero n] → Prop :=
fun k [Field k] n [NeZero n] =>
  ∀ (target source : Guralnick.PolynomialFullGallery.FullFlag k n),
    ∃! w, Guralnick.FullFlagHeckeConvolution.RelativePosition target source w
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.FullFlagHeckeConvolution.OrbitClassification

/--
info: structure Guralnick.FullFlagHeckeConvolution.Input {n : ℕ} [NeZero n] {c : Guralnick.Hecke.WindowCoxeter n}
  (K : Guralnick.Hecke.KLRealization c) (p : ℕ) [Fact (Nat.Prime p)] (hp : Nat.Prime p) : Prop
number of parameters: 7
fields:
  Guralnick.FullFlagHeckeConvolution.Input.orbits : Guralnick.FullFlagHeckeConvolution.OrbitClassification
      (GaloisField p 2) n
  Guralnick.FullFlagHeckeConvolution.Input.convolution : ∀ (x y : Guralnick.Hecke.Algebra n)
      (target source : Guralnick.PolynomialFullGallery.FullFlag (GaloisField p 2) n),
      Guralnick.FullFlagHeckeConvolution.value K p hp ⋯ (x * y) target source =
        ∑ᶠ (middle : Guralnick.PolynomialFullGallery.FullFlag (GaloisField p 2) n),
          Guralnick.FullFlagHeckeConvolution.value K p hp ⋯ x target middle *
            Guralnick.FullFlagHeckeConvolution.value K p hp ⋯ y middle source
constructor:
  Guralnick.FullFlagHeckeConvolution.Input.mk {n : ℕ} [NeZero n] {c : Guralnick.Hecke.WindowCoxeter n}
    {K : Guralnick.Hecke.KLRealization c} {p : ℕ} [Fact (Nat.Prime p)] {hp : Nat.Prime p}
    (orbits : Guralnick.FullFlagHeckeConvolution.OrbitClassification (GaloisField p 2) n)
    (convolution :
      ∀ (x y : Guralnick.Hecke.Algebra n)
        (target source : Guralnick.PolynomialFullGallery.FullFlag (GaloisField p 2) n),
        Guralnick.FullFlagHeckeConvolution.value K p hp orbits (x * y) target source =
          ∑ᶠ (middle : Guralnick.PolynomialFullGallery.FullFlag (GaloisField p 2) n),
            Guralnick.FullFlagHeckeConvolution.value K p hp orbits x target middle *
              Guralnick.FullFlagHeckeConvolution.value K p hp orbits y middle source) :
    Guralnick.FullFlagHeckeConvolution.Input K p hp
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.FullFlagHeckeConvolution.Input

/--
info: structure Guralnick.CoordinateLiteratureTransfer.Inputs (T : Guralnick.Hecke.TheoryFamily) : Prop
number of parameters: 1
fields:
  Guralnick.CoordinateLiteratureTransfer.Inputs.existence : Guralnick.LiteratureTransfer.HighestWeightExistence
  Guralnick.CoordinateLiteratureTransfer.Inputs.andersen : Guralnick.CoordinateLiteratureTransfer.AndersenAJS T
  Guralnick.CoordinateLiteratureTransfer.Inputs.bnp : Guralnick.CoordinateLiteratureTransfer.BNP
  Guralnick.CoordinateLiteratureTransfer.Inputs.steinberg : Guralnick.LiteratureTransfer.Steinberg
  Guralnick.CoordinateLiteratureTransfer.Inputs.simple : Guralnick.LiteratureTransfer.PSLSimplicity
constructor:
  Guralnick.CoordinateLiteratureTransfer.Inputs.mk {T : Guralnick.Hecke.TheoryFamily}
    (existence : Guralnick.LiteratureTransfer.HighestWeightExistence)
    (andersen : Guralnick.CoordinateLiteratureTransfer.AndersenAJS T) (bnp : Guralnick.CoordinateLiteratureTransfer.BNP)
    (steinberg : Guralnick.LiteratureTransfer.Steinberg) (simple : Guralnick.LiteratureTransfer.PSLSimplicity) :
    Guralnick.CoordinateLiteratureTransfer.Inputs T
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.CoordinateLiteratureTransfer.Inputs

/--
info: def Guralnick.CoordinateLiteratureTransfer.AndersenAJS : Guralnick.Hecke.TheoryFamily → Prop :=
fun T =>
  ∀ (m : ℕ) (hm : 2 ≤ m),
    ∃ p₀,
      ∀ (p : ℕ) (hp : Nat.Prime p),
        p₀ ≤ p →
          2 * m + 1 < p →
            ∀ (wt : Guralnick.Weights.RootLattice (2 * m + 1))
              (A : Guralnick.LiteratureTransfer.SimpleModule (Guralnick.Cohomology.PrimeClosure p) (2 * m + 1) wt)
              (b : Guralnick.AffinePermutation (2 * m + 1)),
              Guralnick.LiteratureTransfer.finiteLeftMinimal (T m hm).coxeter b →
                Guralnick.DominantRestricted ↑p ↑wt →
                  ↑wt = b.dotZero (↑p) (Guralnick.Weights.rho m) →
                    ↑(Module.finrank (Guralnick.Cohomology.PrimeClosure p)
                          (Guralnick.RationalCoordinate.CoordinateH1 ⋯)) =
                      (((T m hm).kl.standard.repr
                            ((T m hm).kl.canonical (Guralnick.AffinePermutation.longest (2 * m + 1) * b)))
                          (Guralnick.AffinePermutation.longest (2 * m + 1)))
                        1
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.CoordinateLiteratureTransfer.AndersenAJS

/--
info: def Guralnick.CoordinateLiteratureTransfer.BNP : Prop :=
∀ (m : ℕ),
  2 ≤ m →
    ∀ (p : ℕ) (hp : Nat.Prime p),
      5 * (2 * m) ≤ p →
        ∀ (wt : Guralnick.Weights.RootLattice (2 * m + 1))
          (A : Guralnick.LiteratureTransfer.SimpleModule (Guralnick.Cohomology.PrimeClosure p) (2 * m + 1) wt)
          (b : Guralnick.AffinePermutation (2 * m + 1)),
          Guralnick.DominantRestricted ↑p ↑wt →
            ↑wt = b.dotZero (↑p) (Guralnick.Weights.rho m) →
              Nonempty
                (Guralnick.RationalCoordinate.CoordinateH1 ⋯ ≃ₗ[Guralnick.Cohomology.PrimeClosure p]
                  ↑(Guralnick.Cohomology.H1 (Guralnick.HighestWeight.restrictPrime (2 * m + 1) p A.rep)))
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.CoordinateLiteratureTransfer.BNP

/--
info: def Guralnick.LiteratureTransfer.HighestWeightExistence : Prop :=
∀ (m : ℕ),
  2 ≤ m →
    ∀ (p : ℕ) (hp : Nat.Prime p) (wt : Guralnick.Weights.RootLattice (2 * m + 1)),
      Guralnick.DominantRestricted ↑p ↑wt →
        Nonempty (Guralnick.LiteratureTransfer.SimpleModule (Guralnick.Cohomology.PrimeClosure p) (2 * m + 1) wt)
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.LiteratureTransfer.HighestWeightExistence

/--
info: def Guralnick.LiteratureTransfer.Steinberg : Prop :=
∀ (m : ℕ),
  2 ≤ m →
    ∀ (p : ℕ) (hp : Nat.Prime p) (wt : Guralnick.Weights.RootLattice (2 * m + 1))
      (A : Guralnick.LiteratureTransfer.SimpleModule (Guralnick.Cohomology.PrimeClosure p) (2 * m + 1) wt),
      Guralnick.DominantRestricted ↑p ↑wt →
        Guralnick.Cohomology.Irreducible (Guralnick.HighestWeight.restrictPrime (2 * m + 1) p A.rep)
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.LiteratureTransfer.Steinberg

/--
info: def Guralnick.LiteratureTransfer.PSLSimplicity : Prop :=
∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ), Nat.Prime p → 5 * (2 * m) ≤ p → IsSimpleGroup (Guralnick.Cohomology.PSL m p)
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.LiteratureTransfer.PSLSimplicity

/--
info: def Guralnick.Cohomology.AbsoluteBoundedness : Prop :=
∃ C, Guralnick.Cohomology.AbsoluteUniformH1Bound C
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.Cohomology.AbsoluteBoundedness

/--
info: def Guralnick.Cohomology.AbsoluteUniformH1Bound : ℕ → Prop :=
fun C =>
  ∀ (k : Type) [inst : Field k] (G : Type) [inst_1 : Group G] [Finite G] (A : Rep k G),
    Guralnick.Cohomology.AbsolutelyAdmissible A → Guralnick.Cohomology.h1Dimension A ≤ C
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.Cohomology.AbsoluteUniformH1Bound

/--
info: def Guralnick.Cohomology.AbsolutelyAdmissible : {k G : Type} → [inst : Field k] → [inst_1 : Group G] → Rep k G → Prop :=
fun {k G} [Field k] [Group G] A =>
  FiniteDimensional k ↑A.V ∧ Guralnick.Cohomology.Faithful A ∧ Guralnick.Cohomology.AbsolutelyIrreducible A
-/
#guard_msgs (whitespace := lax) in
#print Guralnick.Cohomology.AbsolutelyAdmissible


/- Actual seed web coordinate evaluations. -/

/-- info: 'Guralnick.SeedWebCoordinates.raw_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedWebCoordinates.raw_source

/-- info: 'Guralnick.SeedWebCoordinates.one_line_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedWebCoordinates.one_line_source

/-- info: 'Guralnick.SeedWebCoordinates.corrected_graph_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedWebCoordinates.corrected_graph_source

/-- info: 'Guralnick.SeedWebCoordinates.reflected_one_line_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedWebCoordinates.reflected_one_line_source


namespace Guralnick.Verification

/-- The rank-one calibration is the actual ordinary KL polynomial at the
prescribed source and family endpoint, using only the framework inputs. -/
theorem seedRankOnePolynomialStatement (T : Hecke.Theory 5)
    (W : PolynomialWebLiterature T) :
    T.kl.polynomial (AffinePermutation.longest 5)
      (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 1) (by decide : 1 ≤ 2)) =
      (1 + Polynomial.X : Polynomial ℤ) :=
  SeedPolynomials.rank_one_polynomial T W

/-- This full seed KL polynomial is a conclusion; neither its coefficients
nor the seed decomposition is permitted as an extra premise. -/
theorem seedDiagonalPolynomialStatement (T : Hecke.Theory 5)
    (W : PolynomialWebLiterature T) :
    T.kl.polynomial (AffinePermutation.longest 5)
      (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 2) (by decide : 2 ≤ 2)) =
      (1 + 4*Polynomial.X + 5*Polynomial.X^2 +
        4*Polynomial.X^3 + 2*Polynomial.X^4 : Polynomial ℤ) :=
  SeedPolynomials.diagonal_polynomial T W

end Guralnick.Verification


/- The actual seed Hecke expansion and KL normalization bridge. -/

/-- info: 'Guralnick.SeedCosets.length_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedCosets.length_mul

/-- info: 'Guralnick.SeedCosets.top_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedCosets.top_endpoint

/-- info: 'Guralnick.SeedOneLineIndex.oneLine_eq_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedOneLineIndex.oneLine_eq_canonical

/-- info: 'Guralnick.SeedRankOne.canonical_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedRankOne.canonical_identity

/-- info: 'Guralnick.SeedRankOne.canonical_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedRankOne.canonical_source

/-- info: 'Guralnick.SeedRankOne.raw_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedRankOne.raw_source

/-- info: 'Guralnick.SeedRankOne.raw_inverse_convention' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedRankOne.raw_inverse_convention

/-- info: 'Guralnick.SeedRankOneConvention.canonical_inverse_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedRankOneConvention.canonical_inverse_identity

/-- info: 'Guralnick.SeedDecomposition.strong_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedDecomposition.strong_multiplicity

/-- info: 'Guralnick.SeedDecomposition.reflected_strong_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedDecomposition.reflected_strong_multiplicity

/-- info: 'Guralnick.SeedDecomposition.canonical_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedDecomposition.canonical_expansion

/-- info: 'Guralnick.SeedDecomposition.web_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedDecomposition.web_expansion

/-- info: 'Guralnick.FamilyPolynomialReadout.of_source_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.FamilyPolynomialReadout.of_source_coordinate



/- Full seed KL polynomial identities are proved conclusions. -/

/-- info: 'Guralnick.SeedPolynomials.rank_one_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedPolynomials.rank_one_polynomial

/-- info: 'Guralnick.SeedPolynomials.rank_one_mu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedPolynomials.rank_one_mu

/-- info: 'Guralnick.SeedPolynomials.four_web_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedPolynomials.four_web_identity

/-- info: 'Guralnick.SeedPolynomials.diagonal_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedPolynomials.diagonal_source

/-- info: 'Guralnick.SeedPolynomials.diagonal_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedPolynomials.diagonal_polynomial

/-- info: 'Guralnick.SeedPolynomials.diagonal_mu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.SeedPolynomials.diagonal_mu

