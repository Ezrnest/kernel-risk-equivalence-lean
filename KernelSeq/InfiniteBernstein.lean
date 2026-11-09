import KernelSeq.FiniteBernstein
import KernelSeq.CovarianceCompression
import KernelSeq.TopEigenCompression
import KernelSeq.CompressionTail
import KernelSeq.HSCovariance
import KernelSeq.ProjectedCovariance

/-!
# Intrinsic covariance tails through actual finite spectral compressions

The only external mathematical premise is the displayed finite-dimensional
Bernstein proposition, for the constructed finite spaces. Approximation and
all covariance inputs belong to the local checked development.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace KernelSeq

noncomputable section

variable {H X Ω ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace X] [MeasurableSpace Ω]

/-- The modular finite Bernstein interface is required only on actual finite
spectral subspaces. Its constructor is proved separately in `ProvedBernstein`. -/
def FiniteSpectralBernstein (b : HilbertBasis ι ℝ H) (P : Measure Ω) : Prop :=
  ∀ s : Finset ι, FiniteUniformIntrinsicBernstein (finiteCompressionBasis b s) P

/-- Actual centered rank-one sum represented in the genuine HS column space. -/
def centeredRankOneSumColumns (b : HilbertBasis ι ℝ H) (μ : Measure X) (u : X → H)
    {n : ℕ} (x : Fin n → X) : HilbertSchmidtColumns ι H :=
  ∑ i, (hsRankOne b (u (x i)) (u (x i)) - hsCovariance b μ u)

theorem hilbertSchmidtOperator_centeredRankOneSumColumns (b : HilbertBasis ι ℝ H)
    {μ : Measure X} (u : X → H) (hu : MemLp u 2 μ) {n : ℕ} (x : Fin n → X) :
    hilbertSchmidtOperator b (centeredRankOneSumColumns b μ u x) =
      ∑ i, centeredRankOne u hu (x i) := by
  simp only [centeredRankOneSumColumns, map_sum, map_sub, hilbertSchmidtOperator_rankOne,
    hilbertSchmidtOperator_hsCovariance b u hu, centeredRankOne]

/-- Conditional finite tails with uniform true covariance norm and original
feature trace. The norm equality is later derived from the actual top vector. -/
theorem projected_covariance_sum_tail
    {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (hTropp : FiniteUniformIntrinsicBernstein (finiteCompressionBasis b s) P)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ) (hind : iIndepFun x P)
    (u : X → H) (hu : MemLp u 2 μ) {L : ℝ} (hbound : ∀ᵐ y ∂μ, ‖u y‖ ^ 2 ≤ L)
    (hC : 0 < ‖populationCovariance (featureEmbedding μ u hu)‖)
    (hnorm : ‖finiteCovarianceCompression b s (populationCovariance (featureEmbedding μ u hu))‖ =
      ‖populationCovariance (featureEmbedding μ u hu)‖) (t : ℝ)
    (ht : Real.sqrt (((n : ℝ) * L) * ‖populationCovariance (featureEmbedding μ u hu)‖) +
      (2 * L) / 3 ≤ t) :
    P {ω | t ≤ ‖finiteBasisProjection b s * (∑ i, centeredRankOne u hu (x i ω)) *
      finiteBasisProjection b s‖} ≤
      ENNReal.ofReal (8 *
        ((∫ y, ‖u y‖ ^ 2 ∂μ) / ‖populationCovariance (featureEmbedding μ u hu)‖) *
        Real.exp (-(t ^ 2) /
          (2 * (((n : ℝ) * L) * ‖populationCovariance (featureEmbedding μ u hu)‖ + (2 * L) * t / 3)))) := by
  let U := FiniteSpectralSubspace b s
  let us : X → U := fun y => U.subtypeL.adjoint (u y)
  have hus : MemLp us 2 μ := U.subtypeL.adjoint.comp_memLp' hu
  have hcs : populationCovariance (featureEmbedding μ us hus) =
      finiteCovarianceCompression b s (populationCovariance (featureEmbedding μ u hu)) :=
    (subspaceCompression_populationCovariance U u hu).symm
  have hcn : ‖populationCovariance (featureEmbedding μ us hus)‖ =
      ‖populationCovariance (featureEmbedding μ u hu)‖ := by rw [hcs, hnorm]
  have hnormu (y : X) : ‖us y‖ ≤ ‖u y‖ := by
    simpa only [us, Submodule.adjoint_subtypeL] using U.norm_orthogonalProjectionOnto_apply_le (u y)
  have hsq (y : X) : ‖us y‖ ^ 2 ≤ ‖u y‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hnormu y) 2
  have hbus : ∀ᵐ y ∂μ, ‖us y‖ ^ 2 ≤ L := hbound.mono (fun y hy => (hsq y).trans hy)
  have htail := finite_covariance_sum_tail_featureTrace (finiteCompressionBasis b s) hTropp
    hn x hlaw hind us hus hbus (by rwa [hcn]) t (by simpa only [hcn] using ht)
  have hcenter (y : X) : centeredRankOne us hus y =
      finiteCovarianceCompression b s (centeredRankOne u hu y) := by
    change _ = subspaceCompression U (InnerProductSpace.rankOne ℝ (u y) (u y) -
      populationCovariance (featureEmbedding μ u hu))
    rw [← subspaceCompressionL_apply, map_sub]
    simp only [subspaceCompressionL_apply, subspaceCompression_rankOne, centeredRankOne, hcs]
    rfl
  have hsum (ω : Ω) : (∑ i, centeredRankOne us hus (x i ω)) =
      finiteCovarianceCompression b s (∑ i, centeredRankOne u hu (x i ω)) := by
    simp_rw [hcenter]
    exact (map_sum (finiteCovarianceCompression b s) _ _).symm
  simp only [hsum, finiteCovarianceCompression_norm_eq, hcn] at htail
  apply htail.trans
  apply ENNReal.ofReal_le_ofReal
  have hint : (∫ y, ‖us y‖ ^ 2 ∂μ) ≤ ∫ y, ‖u y‖ ^ 2 ∂μ :=
    integral_mono ((memLp_two_iff_integrable_sq_norm hus.1).mp hus)
      ((memLp_two_iff_integrable_sq_norm hu.1).mp hu) hsq
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hint (norm_nonneg _)) (by norm_num))
    (Real.exp_pos _).le

/-- The actual infinite-dimensional covariance sum tail, conditional on the
external finite-dimensional leaf alone. The finite approximation, variance
inputs, true norm and trace comparison are conclusions of local proofs. -/
theorem infinite_covariance_sum_tail [TopologicalSpace.SeparableSpace H]
    {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (u : X → H) (hu : MemLp u 2 μ)
    (hTropp : FiniteSpectralBernstein (featureCovarianceBasis u hu) P)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ) (hind : iIndepFun x P)
    {L : ℝ} (hbound : ∀ᵐ y ∂μ, ‖u y‖ ^ 2 ≤ L)
    (hC : 0 < ‖populationCovariance (featureEmbedding μ u hu)‖) (t : ℝ)
    (ht : Real.sqrt (((n : ℝ) * L) * ‖populationCovariance (featureEmbedding μ u hu)‖) +
      (2 * L) / 3 ≤ t) :
    P {ω | t < ‖∑ i, centeredRankOne u hu (x i ω)‖} ≤
      ENNReal.ofReal (8 *
        ((∫ y, ‖u y‖ ^ 2 ∂μ) / ‖populationCovariance (featureEmbedding μ u hu)‖) *
        Real.exp (-(t ^ 2) /
          (2 * (((n : ℝ) * L) * ‖populationCovariance (featureEmbedding μ u hu)‖ + (2 * L) * t / 3)))) := by
  letI : Countable (FeatureCovarianceIndex u hu) := featureCovarianceIndex_countable u hu
  let b := featureCovarianceBasis u hu
  let c : Ω → HilbertSchmidtColumns (FeatureCovarianceIndex u hu) H :=
    fun ω => centeredRankOneSumColumns b μ u (fun i => x i ω)
  have hnorm := positive_compact_compression_norm_eventually_eq
    (populationCovariance (featureEmbedding μ u hu))
    (populationCovariance_feature_isCompact μ u hu) (populationCovariance_isPositive _) hC
  have htail := measure_hs_norm_gt_le_of_compression_tails b P c t _ (by
    filter_upwards [hnorm] with s hs
    simp only [c, hilbertSchmidtOperator_centeredRankOneSumColumns b u hu]
    apply projected_covariance_sum_tail b s (hTropp s) hn x hlaw hind u hu hbound hC _ t ht
    exact (finiteCovarianceCompression_norm_eq b s _).trans hs)
  simpa only [c, hilbertSchmidtOperator_centeredRankOneSumColumns b u hu] using htail

end

end KernelSeq
