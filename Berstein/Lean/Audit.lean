import Berstein

/- Axiom output and theorem signatures are checked by scripts/verify.py.
The new main theorem has only the executable certificate-acceptance premise. -/

#print axioms Berstein.constant_order
#print axioms Berstein.S_mem_bin_minus20
#print axioms Berstein.IntervalCover.check_sound
#print axioms Berstein.IntervalCover.rootBands_affine_cover
#print axioms Berstein.IntervalCover.missing_left_rejected
#print axioms Berstein.IntervalCover.missing_right_rejected
#print axioms Berstein.IntervalCover.internal_gap_rejected
#print axioms Berstein.QBounds.mul_sound
#print axioms Berstein.QBounds.checkedDiv_sound
#print axioms Berstein.IntervalExpression.enclose_sound
#print axioms Berstein.IntervalExpression.leq_sound
#print axioms Berstein.IntervalExpression.verifiedCheckCover_sound
#print axioms Berstein.IntervalExpression.parameter_varying_cover_accepted
#print axioms Berstein.NumericalTable.check_sound
#print axioms Berstein.FiniteCover.check_sound_uniform
#print axioms Berstein.FiniteCover.one_direction_overlap_rejected
#print axioms Berstein.FiniteTable.check_sound
#print axioms Berstein.FiniteTable.closed_cover_of_check
#print axioms Berstein.FiniteTable.missing_destination_rejected
#print axioms Berstein.FiniteTable.missing_root_rejected
#print axioms Berstein.RatioGrid.check_sound
#print axioms Berstein.RatioGrid.missing_bin_rejected
#print axioms Berstein.nested_compact_realizes
#print axioms Berstein.ClosedCoverSystem.realizes
#print axioms Berstein.balanced_growth
#print axioms Berstein.isCompact_admissible322
#print axioms Berstein.isCompact_admissible431
#print axioms Berstein.nonempty_admissible431
#print axioms Berstein.prefix322_coefficients
#print axioms Berstein.prefix431_coefficients
#print axioms Berstein.continuants_ge_fibonacci
#print axioms Berstein.nine_digit_value_bound
#print axioms Berstein.mem_markovSpectrum_of_dominant
#print axioms Berstein.localValue_perturbation_left_nine
#print axioms Berstein.localValue_perturbation_right_nine
#print axioms Berstein.interval_subset_markovSpectrum_of_filling_and_bound

-- Show the mathematical premises as well as the logical axiom dependencies.

#print axioms Berstein.Quadratic462.le_sound
#print axioms Berstein.GraphMeaning.shape_transport
#print axioms Berstein.GraphMeaning.derivative_transport
#print axioms Berstein.GraphMeaning.derivative_constant
#print axioms Berstein.GraphCertificate.checkCell_coverage
#print axioms Berstein.GraphCertificate.checkVertex_destinations
#print axioms Berstein.GraphCertificate.checkGeometry_cell
#print axioms Berstein.GraphMeaning.verified_successor
#print axioms Berstein.GraphMeaning.root_hull_sums
#print axioms Berstein.GraphMeaning.filling_of_checked_roots_and_successors
#print axioms Berstein.SpectralVerified.far_checked
#print axioms Berstein.SpectralVerified.near322_checked
#print axioms Berstein.SpectralVerified.near431_checked
#print axioms Berstein.SpectralVerified.adjacent_four_checked
#print axioms Berstein.SpectralVerified.noncentral_bound
#print axioms Berstein.Certificate.check_sound
#print axioms Berstein.Certificate.filling_of_accepted
#print axioms Berstein.Certificate.target_interval_subset_of_check
#print axioms Berstein.Certificate.open_interval_subset_interior_of_check
#print axioms Berstein.Certificate.interior_below_freiman_nonempty_of_check
#check Berstein.Certificate.target_interval_subset_of_check
#check Berstein.Certificate.interior_below_freiman_nonempty_of_check

#print axioms Berstein.target_interval_subset
#print axioms Berstein.open_interval_subset_interior
#print axioms Berstein.interior_below_freiman_nonempty
#check Berstein.target_interval_subset
#check Berstein.interior_below_freiman_nonempty
