import KernelSeq.SpectralMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Logic.Denumerable

/-!
# The original exact counting asymptotic gives a genuine enumeration

The actual positive covariance index is countable by domain separability.
The original positive power-law counting asymptotic forces this index to be
infinite; the relabeling by ℕ is therefore constructed, not an additional
statistical or spectral assumption.
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

omit [TopologicalSpace.SeparableSpace H] [IsProbabilityMeasure μ] in
/-- Exact power-law counting is genuinely unbounded near zero. -/
theorem featureSpectralCount_tendsto_atTop_of_exact_counting
    (k : X → H) (hk : MemLp k 2 μ) {D β : ℝ} (hD : 0 < D) (hβ : 0 < β)
    (hcount : Tendsto
      (fun t => (featureSpectralCount k hk t : ℝ) / (D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun t => (featureSpectralCount k hk t : ℝ)) (𝓝[>] 0) atTop := by
  have hp : Tendsto (fun t : ℝ => t^(-(1/β))) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos (one_div_pos.mpr hβ))
  have hden := hp.const_mul_atTop hD
  have hmul := hcount.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hden
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htp : 0 < t := ht
  have hdp : 0 < D * t^(-(1/β)) := mul_pos hD (Real.rpow_pos_of_pos htp _)
  exact div_mul_cancel₀ _ hdp.ne'

omit [TopologicalSpace.SeparableSpace H] [IsProbabilityMeasure μ] in
/-- Finiteness would bound every actual counting value by the cardinality
of the entire positive spectral index, contradicting the original asymptotic. -/
theorem infinite_predictionSingularIndex_of_exact_counting
    (k : X → H) (hk : MemLp k 2 μ) {D β : ℝ} (hD : 0 < D) (hβ : 0 < β)
    (hcount : Tendsto
      (fun t => (featureSpectralCount k hk t : ℝ) / (D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) :
    Infinite (PredictionSingularIndex (featureEmbedding μ k hk)) := by
  classical
  let I := PredictionSingularIndex (featureEmbedding μ k hk)
  rcases finite_or_infinite I with hfinite | hinfinite
  · letI : Finite I := hfinite
    have hh := featureSpectralCount_tendsto_atTop_of_exact_counting k hk hD hβ hcount
    obtain ⟨t, ht⟩ := (hh.eventually (eventually_gt_atTop (Nat.card I : ℝ))).exists
    have hle : featureSpectralCount k hk t ≤ Nat.card I := Set.ncard_le_card _
    have hleR : (featureSpectralCount k hk t : ℝ) ≤ (Nat.card I : ℝ) := by exact_mod_cast hle
    exact (not_lt_of_ge hleR ht).elim
  · exact hinfinite

/-- A genuine relabeling of the actual positive spectrum is supplied by the
original exact counting hypothesis. No enumeration is an application input. -/
def featureSpectrumEnumeration_of_exact_counting
    (k : X → H) (hk : MemLp k 2 μ) {D β : ℝ} (hD : 0 < D) (hβ : 0 < β)
    (hcount : Tendsto
      (fun t => (featureSpectralCount k hk t : ℝ) / (D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) : FeatureSpectrumEnumeration k hk := by
  letI : Countable (PredictionSingularIndex (featureEmbedding μ k hk)) :=
    predictionSingularIndex_countable (featureEmbedding μ k hk)
      (populationCovariance_feature_isCompact μ k hk)
  letI := infinite_predictionSingularIndex_of_exact_counting k hk hD hβ hcount
  exact Classical.choice (inferInstance : Nonempty (ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk)))

end
end KernelSeq
