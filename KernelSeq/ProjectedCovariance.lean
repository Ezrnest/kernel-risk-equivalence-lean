import KernelSeq.CovarianceCompression
import KernelSeq.FiniteBernstein

/-!
# Projected covariance and the genuine finite-compression trace

Compression of the actual feature covariance is the actual covariance of the
adjoint-projected feature. Its trace in a countable Hilbert basis is therefore
the integrated projected-feature energy, bounded by the original energy. The
finite spectral space has a constructed finite Hilbert basis; no compressed
trace or intrinsic-dimension certificate is assumed.
-/

open MeasureTheory Submodule
open scoped BigOperators

namespace KernelSeq

variable {H ι κ X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace X] {μ : Measure X}

/-- A concrete finite Hilbert basis exists on the constructed finite spectral
space, with a manifestly finite index, even if the original basis is uncountable. -/
noncomputable def finiteCompressionBasis (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    HilbertBasis (Fin (Module.finrank ℝ (FiniteSpectralSubspace b s))) ℝ (FiniteSpectralSubspace b s) :=
  (stdOrthonormalBasis ℝ (FiniteSpectralSubspace b s)).toHilbertBasis

section Subspace

variable (U : Submodule ℝ H) [CompleteSpace U]

noncomputable local instance projectedSubspaceContinuousENorm : ContinuousENorm (U →L[ℝ] U) := by
  letI : NormedAddCommGroup (U →L[ℝ] U) := ContinuousLinearMap.toNormedAddCommGroup
  infer_instance

/-- The actual adjoint-projected feature remains in L². -/
theorem memLp_adjoint_projectedFeature (u : X → H) (hu : MemLp u 2 μ) :
    MemLp (fun x => U.subtypeL.adjoint (u x)) 2 μ :=
  U.subtypeL.adjoint.comp_memLp' hu

theorem adjoint_projectedFeature_norm_le (v : H) : ‖U.subtypeL.adjoint v‖ ≤ ‖v‖ := by
  simpa only [Submodule.adjoint_subtypeL] using U.norm_orthogonalProjectionOnto_apply_le v

theorem adjoint_projectedFeature_norm_sq_le (v : H) : ‖U.subtypeL.adjoint v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (adjoint_projectedFeature_norm_le U v) 2

/-- Compression of a genuine rank-one feature operator is the genuine
rank-one operator of its actual adjoint-projected feature. -/
theorem subspaceCompression_rankOne (v : H) :
    subspaceCompression U (InnerProductSpace.rankOne ℝ v v) =
      InnerProductSpace.rankOne ℝ (U.subtypeL.adjoint v) (U.subtypeL.adjoint v) := by
  apply ContinuousLinearMap.ext
  intro u
  change U.subtypeL.adjoint (inner ℝ v (u : H) • v) = _
  rw [map_smul]
  simp only [InnerProductSpace.rankOne_apply, U.subtypeL.adjoint_inner_left]
  rfl

/-- The compressed population operator is identified with a genuine feature
covariance by the actual Bochner integral, without a covariance certificate. -/
theorem subspaceCompression_populationCovariance (u : X → H) (hu : MemLp u 2 μ) :
    subspaceCompression U (populationCovariance (featureEmbedding μ u hu)) =
      populationCovariance (featureEmbedding μ (fun x => U.subtypeL.adjoint (u x))
        (U.subtypeL.adjoint.comp_memLp' hu)) := by
  rw [populationCovariance_eq_integral,
    ← integral_subspaceCompression U _ (integrable_rankOne_feature u hu)]
  simp_rw [subspaceCompression_rankOne]
  exact (populationCovariance_eq_integral _ (U.subtypeL.adjoint.comp_memLp' hu)).symm

/-- Actual centered rank-one covariance increments commute with compression,
including the centering by the genuine projected population covariance. -/
theorem subspaceCompression_centeredRankOne [IsProbabilityMeasure μ]
    (u : X → H) (hu : MemLp u 2 μ) (x : X) :
    subspaceCompression U (centeredRankOne u hu x) =
      centeredRankOne (fun y => U.subtypeL.adjoint (u y))
        (memLp_adjoint_projectedFeature U u hu) x := by
  unfold centeredRankOne
  have hsub := map_sub (subspaceCompressionL U) (InnerProductSpace.rankOne ℝ (u x) (u x))
    (populationCovariance (featureEmbedding μ u hu))
  change subspaceCompression U (InnerProductSpace.rankOne ℝ (u x) (u x) -
    populationCovariance (featureEmbedding μ u hu)) =
      subspaceCompression U (InnerProductSpace.rankOne ℝ (u x) (u x)) -
        subspaceCompression U (populationCovariance (featureEmbedding μ u hu)) at hsub
  rw [hsub, subspaceCompression_rankOne, subspaceCompression_populationCovariance]

/-- The compressed covariance has a summable diagonal and its actual trace
equals integrated projected-feature energy in every countable Hilbert basis. -/
theorem subspaceCompression_populationCovariance_basisTrace [Countable κ]
    (e : HilbertBasis κ ℝ U) (u : X → H) (hu : MemLp u 2 μ) :
    Summable (fun i => inner ℝ (e i)
      (subspaceCompression U (populationCovariance (featureEmbedding μ u hu)) (e i))) ∧
      basisTrace e (subspaceCompression U (populationCovariance (featureEmbedding μ u hu))) =
        ∫ x, ‖U.subtypeL.adjoint (u x)‖ ^ 2 ∂μ := by
  rw [subspaceCompression_populationCovariance U u hu]
  exact populationCovariance_basisTrace e _ (U.subtypeL.adjoint.comp_memLp' hu)

/-- The actual projection contraction gives the uniform compression trace
bound required by the intrinsic Bernstein prefactor. -/
theorem subspaceCompression_populationCovariance_trace_le_integral [Countable κ]
    (e : HilbertBasis κ ℝ U) (u : X → H) (hu : MemLp u 2 μ) :
    basisTrace e (subspaceCompression U (populationCovariance (featureEmbedding μ u hu))) ≤
      ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [(subspaceCompression_populationCovariance_basisTrace U e u hu).2]
  have hp := U.subtypeL.adjoint.comp_memLp' hu
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hp.1).mp hp)
    ((memLp_two_iff_integrable_sq_norm hu.1).mp hu)
  intro x
  have hn : ‖U.subtypeL.adjoint (u x)‖ ≤ ‖u x‖ := by
    simpa only [Submodule.adjoint_subtypeL] using U.norm_orthogonalProjectionOnto_apply_le (u x)
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- The same bound expressed entirely as actual operator traces. Countability
is required only for the two integrated-Parseval trace representations. -/
theorem subspaceCompression_populationCovariance_trace_le [Countable ι] [Countable κ]
    (b : HilbertBasis ι ℝ H) (e : HilbertBasis κ ℝ U) (u : X → H) (hu : MemLp u 2 μ) :
    basisTrace e (subspaceCompression U (populationCovariance (featureEmbedding μ u hu))) ≤
      basisTrace b (populationCovariance (featureEmbedding μ u hu)) := by
  rw [(populationCovariance_basisTrace b u hu).2]
  exact subspaceCompression_populationCovariance_trace_le_integral U e u hu

end Subspace

/-- The finite Bernstein basis has genuinely summable covariance diagonal. -/
theorem finiteCovarianceCompression_population_basisTrace (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (u : X → H) (hu : MemLp u 2 μ) :
    Summable (fun i => inner ℝ (finiteCompressionBasis b s i)
      (finiteCovarianceCompression b s (populationCovariance (featureEmbedding μ u hu))
        (finiteCompressionBasis b s i))) ∧
      basisTrace (finiteCompressionBasis b s)
        (finiteCovarianceCompression b s (populationCovariance (featureEmbedding μ u hu))) =
          ∫ x, ‖(finiteSpectralInclusion b s).adjoint (u x)‖ ^ 2 ∂μ := by
  exact subspaceCompression_populationCovariance_basisTrace (FiniteSpectralSubspace b s)
    (finiteCompressionBasis b s) u hu

/-- The finite-dimensional prefactor trace is bounded by the original feature
energy, with no countability assumption on the original basis or space. -/
theorem finiteCovarianceCompression_population_trace_le_integral
    (b : HilbertBasis ι ℝ H) (s : Finset ι) (u : X → H) (hu : MemLp u 2 μ) :
    basisTrace (finiteCompressionBasis b s)
      (finiteCovarianceCompression b s (populationCovariance (featureEmbedding μ u hu))) ≤
        ∫ x, ‖u x‖ ^ 2 ∂μ :=
  subspaceCompression_populationCovariance_trace_le_integral (FiniteSpectralSubspace b s)
    (finiteCompressionBasis b s) u hu

/-- The actual finite-space projected feature has the original L² moment. -/
theorem memLp_finiteProjectedFeature (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (u : X → H) (hu : MemLp u 2 μ) :
    MemLp (fun x => (finiteSpectralInclusion b s).adjoint (u x)) 2 μ :=
  memLp_adjoint_projectedFeature (FiniteSpectralSubspace b s) u hu

theorem finiteProjectedFeature_norm_le (b : HilbertBasis ι ℝ H) (s : Finset ι) (v : H) :
    ‖(finiteSpectralInclusion b s).adjoint v‖ ≤ ‖v‖ :=
  adjoint_projectedFeature_norm_le (FiniteSpectralSubspace b s) v

theorem finiteProjectedFeature_norm_sq_le (b : HilbertBasis ι ℝ H) (s : Finset ι) (v : H) :
    ‖(finiteSpectralInclusion b s).adjoint v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
  adjoint_projectedFeature_norm_sq_le (FiniteSpectralSubspace b s) v

/-- The exact finite covariance identity, in the orientation used by the
finite Bernstein application to projected features. -/
theorem populationCovariance_finiteProjectedFeature (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (u : X → H) (hu : MemLp u 2 μ) :
    populationCovariance (featureEmbedding μ (fun x => (finiteSpectralInclusion b s).adjoint (u x))
      (memLp_finiteProjectedFeature b s u hu)) =
      finiteCovarianceCompression b s (populationCovariance (featureEmbedding μ u hu)) :=
  (subspaceCompression_populationCovariance (FiniteSpectralSubspace b s) u hu).symm

/-- The finite Bernstein random increments are exactly actual compressed
increments, not a second unrelated centered feature family. -/
theorem centeredRankOne_finiteProjectedFeature [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H) (s : Finset ι) (u : X → H) (hu : MemLp u 2 μ) (x : X) :
    centeredRankOne (fun y => (finiteSpectralInclusion b s).adjoint (u y))
      (memLp_finiteProjectedFeature b s u hu) x =
        finiteCovarianceCompression b s (centeredRankOne u hu x) :=
  (subspaceCompression_centeredRankOne (FiniteSpectralSubspace b s) u hu x).symm

end KernelSeq
