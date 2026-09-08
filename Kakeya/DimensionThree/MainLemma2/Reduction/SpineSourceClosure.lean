/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceIndex
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteWitnessProducer
public import Kakeya.DimensionThree.MainLemma2.Cap.SeamDischarge

/-!
# Chosen-source closure and the conditional scalar profile gap

The actual ambient TrialSupplier remains an explicit producer obligation.
These interfaces preserve the source anchor and the existing free-cap route.
-/

@[expose] public section

namespace Kakeya.ML2Assembly

universe u

open Filter Topology ML2Core


/-- The free-cap theorem converts the existing pointwise core to a pointwise drop. -/
theorem pointwiseDrop_of_pointwiseCore_free (hcore : PointwiseCore.{u}) :
    PointwiseDrop.{u} := by
  intro beta hbeta0 hbeta1 hKT hF
  obtain ⟨c, hc, hcBeta, eta, heta0, heta1, hdich⟩ := hcore beta hbeta0 hbeta1 hKT hF
  exact ⟨c, hc, ML2Cap.katzTaoEstimate_sub_of_dichotomy_free hc hcBeta
    (by linarith) heta0 heta1 le_rfl hdich⟩

/-- The existing pointwise envelope gives the unchanged Main Lemma 2 proposition. -/
theorem mainLemma2Statement_of_pointwiseCore_free (hcore : PointwiseCore.{u}) :
    VNSUniform.MainLemma2Statement.{u} := by
  exact VNSUniform.mainLemma2Statement_of_pointwise_drop
    (pointwiseDrop_of_pointwiseCore_free hcore)

end Kakeya.ML2Assembly
