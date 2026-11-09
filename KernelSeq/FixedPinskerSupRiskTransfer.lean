import KernelSeq.UniformSupRiskTransfer
import KernelSeq.UniformRiskEquivalence
import KernelSeq.ExactCountingScaleVerification
import KernelSeq.SpectralScaleModel
import KernelSeq.PinskerSourceBias
import KernelSeq.PinskerOracle

/-!
# Actual fixed-kernel source families and supremum risk transfer

The row models may have different observation probability spaces. Their
deterministic primitive data agree with a single fixed RKHS/design law and
the indicated target, sample size and actual Pinsker oracle. The original
model assumptions remain in `TriangularRiskModel`; no risk, moment or scale
estimate is supplied as an extra field or premise.
-/

namespace KernelSeq

open MeasureTheory Filter Topology Set
noncomputable section

set_option maxHeartbeats 1000000

universe uH uX uΩ

namespace SpectralScaleModel

def sequenceBenchmarkAtNoise {κ ρ A : ℝ} (b : SpectralScaleModel.{uH, uX} κ ρ A) (σ : ℝ) : ℝ :=
  sequenceBenchmark b.feature b.feature_memLp b.φ b.f σ b.n

end SpectralScaleModel

theorem TriangularRiskModel.benchmark_eq_scaleModel {κ ρ A : ℝ}
    (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A) :
    m.benchmark = m.scaleModel.sequenceBenchmarkAtNoise m.σ := rfl

/-- Only deterministic primitive fields of the fixed RKHS model are
updated. The filter conditions here are the proved actual Pinsker instances. -/
def fixedPinskerOracleScaleRow {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH, uX} κ (ResidualFilter.pinskerOrder s) (4 * (1 + s / 2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (n : ℕ) (hn : 0 < n) (f : Lp ℝ 2 b.μ) :
    SpectralScaleModel.{uH, uX} κ (ResidualFilter.pinskerOrder s) (4 * (1 + s / 2)) :=
  { b with
    n := n
    sample_pos := hn
    f := f
    lam := pinskerOracleScale s β R σ D (n : ℝ)
    lambda_pos := pinskerOracleScale_pos (by linarith) (by linarith) hR hσ hD (Nat.cast_pos.mpr hn)
    φ := ResidualFilter.pinsker (pinskerOracleScale s β R σ D (n : ℝ)) s
    spectral_filter := ResidualFilter.pinsker_spectralFilter
      (pinskerOracleScale_pos (by linarith) (by linarith) hR hσ hD (Nat.cast_pos.mpr hn)) (by linarith)
    filter_contract := ResidualFilter.pinsker_contract
      (pinskerOracleScale_pos (by linarith) (by linarith) hR hσ hD (Nat.cast_pos.mpr hn)) hs }

abbrev PinskerSourceIndex {κ s : ℝ}
    (b : SpectralScaleModel.{uH, uX} κ (ResidualFilter.pinskerOrder s) (4 * (1 + s / 2)))
    (hs : 1 ≤ s) (R : ℝ) := ↥(b.SourceBall s (zero_le_one.trans hs) R)

/-- The actual worst sequence benchmark at the oracle, retaining the actual
population filter dimension rather than replacing it by its asymptotic. -/
def pinskerOracleWorstBenchmark {κ s : ℝ}
    (b : SpectralScaleModel.{uH, uX} κ (ResidualFilter.pinskerOrder s) (4 * (1 + s / 2)))
    (β R σ D : ℝ) (n : ℕ) : ℝ :=
  let lam := pinskerOracleScale s β R σ D (n : ℝ)
  R ^ 2 * lam ^ s + σ ^ 2 / (n : ℝ) *
    featureFilterDimension b.feature b.feature_memLp (ResidualFilter.pinsker lam s)

/-- The actual source-family expectation-risk supremum is equivalent to
its actual sequence supremum. Every analytic bound is derived internally
from original exact counting, source membership and the primitive row models.
The parameter space has no measurability or cardinality assumption. -/
theorem fixed_pinsker_sourceBall_sup_risk_transfer {I : Type*} {l : Filter I} [NeBot l]
    {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH, uX} κ (ResidualFilter.pinskerOrder s) (4 * (1 + s / 2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (e : b.SpectrumEnumeration)
    (hcount : Tendsto
      (fun t => (featureSpectralCount b.feature b.feature_memLp t : ℝ) / (D * t ^ (-(1 / β))))
      (𝓝[>] 0) (𝓝 1))
    (n : I → ℕ) (hnpos : ∀ i, 0 < n i) (hn : Tendsto (fun i => (n i : ℝ)) l atTop)
    (m : I → PinskerSourceIndex b hs R →
      TriangularRiskModel.{uH, uX, uΩ} κ (ResidualFilter.pinskerOrder s) (4 * (1 + s / 2)))
    (hfixed : ∀ i θ, (m i θ).scaleModel =
      fixedPinskerOracleScaleRow b hs hβ hR hσ hD (n i) (hnpos i) θ.val)
    (hnoise : ∀ i θ, (m i θ).σ = σ) :
    (∀ᶠ i in l, BddAbove (Set.range (fun θ => (m i θ).expectationRisk))) ∧
      (∀ᶠ i in l, sSup (Set.range (fun θ => (m i θ).benchmark)) =
        pinskerOracleWorstBenchmark b β R σ D (n i)) ∧
      Tendsto (fun i => sSup (Set.range (fun θ => (m i θ).expectationRisk)) /
        pinskerOracleWorstBenchmark b β R σ D (n i)) l (𝓝 1) ∧
      Tendsto (fun i => sSup (Set.range (fun θ => (m i θ).expectationRisk)) /
        sSup (Set.range (fun θ => (m i θ).benchmark))) l (𝓝 1) := by
  let Θ := PinskerSourceIndex b hs R
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hsp : 0 < s := zero_lt_one.trans_le hs
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  letI : Nonempty Θ := ⟨⟨0, zero_mem_predictionSourceBall _ _ s hs0 hR.le⟩⟩
  let lam := fun i => pinskerOracleScale s β R σ D (n i : ℝ)
  let N := fun i => featureEffectiveDimension b.feature b.feature_memLp (lam i)
  let Q := fun i => featureFilterDimension b.feature b.feature_memLp (ResidualFilter.pinsker (lam i) s)
  let L := fun i => featureLeverageEssentialSup b.feature b.feature_memLp (lam i)
  let S := fun i (θ : Θ) => featureSequenceSourceEnergy b.feature b.feature_memLp (lam i)
    (residualComparisonOrder (ResidualFilter.pinskerOrder s)) θ.val
  have hLp (i : I) : 0 < lam i := pinskerOracleScale_pos hsp hβ0 hR hσ hD (Nat.cast_pos.mpr (hnpos i))
  have hreg := pinskerOracleScale_isTheta (fun i => (n i : ℝ))
    (fun i => Nat.cast_pos.mpr (hnpos i)) hsp hβ0 hR hσ hD (l := l)
  have hfst : Tendsto Prod.fst (uniformFamilyFilter l Θ) l := tendsto_fst
  have hα : residualComparisonOrder (ResidualFilter.pinskerOrder s) = 1 := by
    have hp := (ResidualFilter.pinsker_order_bounds hs).1
    unfold residualComparisonOrder
    rw [min_eq_right (by linarith)]
  have hsmooth : 1 - 1 / β < min s (residualComparisonOrder (ResidualFilter.pinskerOrder s)) := by
    rw [hα, min_eq_right hs]
    linarith [one_div_pos.mpr hβ0]
  have hsc := exact_counting_universal_sourceBall_original_scales b.feature b.feature_memLp e
    b.kappa_nonneg (fun x => rkhsFeature_norm_le κ b.kappa_nonneg b.diagonal_bound x)
    hβ hD (pinskerOracleExponent_pos hsp hβ0) (pinskerOracleExponent_lt_one hs hβ0)
    hsp hR hsmooth (fun z => ResidualFilter.pinsker z s)
    (fun z hz => ResidualFilter.pinsker_spectralFilter hz hs0)
    (fun z hz => ResidualFilter.pinsker_contract hz hs) hcount
    (fun p : I × Θ => n p.1) (fun p => hnpos p.1) (hn.comp hfst)
    (fun p : I × Θ => lam p.1) (fun p => hLp p.1)
    ⟨hreg.1.comp_tendsto hfst, hreg.2.comp_tendsto hfst⟩
    (fun p : I × Θ => p.2.val) (fun p => p.2.property)
  have hQeq (i : I) (θ : Θ) : (m i θ).Q = Q i := by
    calc
      _ = (m i θ).scaleModel.Q := rfl
      _ = (fixedPinskerOracleScaleRow b hs hβ hR hσ hD (n i) (hnpos i) θ.val).Q :=
        congrArg SpectralScaleModel.Q (hfixed i θ)
      _ = _ := rfl
  have hceq (i : I) (θ : Θ) : (m i θ).compatibility =
      N i / Q i * Real.sqrt (L i * dimensionLog (N i) / (n i : ℝ)) := by
    calc
      _ = (m i θ).scaleModel.compatibility := rfl
      _ = (fixedPinskerOracleScaleRow b hs hβ hR hσ hD (n i) (hnpos i) θ.val).compatibility :=
        congrArg SpectralScaleModel.compatibility (hfixed i θ)
      _ = _ := rfl
  have hzeq (i : I) (θ : Θ) : (m i θ).sourceBalance =
      (n i : ℝ) * S i θ * originalBiasGamma (L i) (n i : ℝ) (N i) ^ 2 / Q i := by
    calc
      _ = (m i θ).scaleModel.sourceBalance := rfl
      _ = (fixedPinskerOracleScaleRow b hs hβ hR hσ hD (n i) (hnpos i) θ.val).sourceBalance :=
        congrArg SpectralScaleModel.sourceBalance (hfixed i θ)
      _ = _ := rfl
  have heeq (i : I) (θ : Θ) : (m i θ).expectationScale =
      L i / (n i : ℝ) * Real.log (Real.exp 1 + (n i : ℝ) / (lam i * Q i)) := by
    calc
      _ = (m i θ).scaleModel.expectationScale := rfl
      _ = (fixedPinskerOracleScaleRow b hs hβ hR hσ hD (n i) (hnpos i) θ.val).expectationScale :=
        congrArg SpectralScaleModel.expectationScale (hfixed i θ)
      _ = _ := rfl
  have hQm : ∀ᶠ i in l, ∀ θ : Θ, 0 < (m i θ).Q := by
    apply eventually_uniformFamilyFilter_iff.mp
    exact hsc.1.mono fun p hp => (hQeq p.1 p.2).symm ▸ hp
  have hc : Tendsto (fun p : I × Θ => (m p.1 p.2).compatibility) (uniformFamilyFilter l Θ) (𝓝 0) :=
    hsc.2.1.congr' (Eventually.of_forall fun p => (hceq p.1 p.2).symm)
  have hz : Tendsto (fun p : I × Θ => (m p.1 p.2).sourceBalance) (uniformFamilyFilter l Θ) (𝓝 0) :=
    hsc.2.2.1.congr' (Eventually.of_forall fun p => (hzeq p.1 p.2).symm)
  have he : Tendsto (fun p : I × Θ => (m p.1 p.2).expectationScale) (uniformFamilyFilter l Θ) (𝓝 0) :=
    hsc.2.2.2.congr' (Eventually.of_forall fun p => (heeq p.1 p.2).symm)
  have hu := uniform_expectation_risk_equivalence m hσ
    (Eventually.of_forall fun i θ => by rw [hnoise i θ]) hQm hc hz he
  have hbench (i : I) (θ : Θ) : (m i θ).benchmark =
      sequenceBenchmark b.feature b.feature_memLp (ResidualFilter.pinsker (lam i) s) θ.val σ (n i) := by
    rw [TriangularRiskModel.benchmark_eq_scaleModel, hnoise i θ, hfixed i θ]
    rfl
  have hUpper : ∀ᶠ i in l, ∀ θ : Θ, (m i θ).benchmark ≤ pinskerOracleWorstBenchmark b β R σ D (n i) := by
    apply Eventually.of_forall
    intro i θ
    rw [hbench]
    have hqual : ∀ t ∈ Ioc (0 : ℝ) (κ ^ 2),
        t ^ (s / 2) * |ResidualFilter.residual (ResidualFilter.pinsker (lam i) s) t| ≤
          (1 : ℝ) * lam i ^ (s / 2) := by
      intro t ht
      simpa only [one_mul] using ResidualFilter.pinsker_qualification (hLp i) ht.1.le (by positivity) le_rfl
    simpa only [one_pow, one_mul, pinskerOracleWorstBenchmark, lam] using sequenceBenchmark_le_sourceBall_of_qualification
      b.feature b.feature_memLp _ (hLp i) hs0 hR.le b.population_bound
      (ResidualFilter.pinsker_spectralFilter (hLp i) hs0) hqual θ.property σ (n i)
  have hlam0 := pinskerOracleScale_tendsto_zero (fun i => (n i : ℝ))
    (fun i => Nat.cast_pos.mpr (hnpos i)) hn hsp hβ0 hR hσ hD
  have hAttained : ∀ᶠ i in l, ∃ θ : Θ, (m i θ).benchmark = pinskerOracleWorstBenchmark b β R σ D (n i) := by
    filter_upwards [hlam0.eventually (gt_mem_nhds (e 0).2)] with i hi
    let θ0 : Θ := ⟨featureSourceDirection b.feature b.feature_memLp s hs0 R (e 0),
      featureSourceDirection_mem_sourceBall b.feature b.feature_memLp s hs0 hR.le (e 0)⟩
    refine ⟨θ0, ?_⟩
    rw [hbench]
    change sequenceBenchmark b.feature b.feature_memLp (ResidualFilter.pinsker (lam i) s)
      (featureSourceDirection b.feature b.feature_memLp s hs0 R (e 0)) σ (n i) = _
    rw [sequenceBenchmark, featureSequenceBias_pinsker_attained b.feature b.feature_memLp (hLp i)
      hs0 R (e 0) hi.le, ← featureFilterDimension_eq_positive_sequence]
    rfl
  have hPos : ∀ᶠ i in l, ∀ θ : Θ, 0 < (m i θ).benchmark :=
    hQm.mono fun i hi θ => (m i θ).benchmark_pos (hi θ)
  have hTransfer := uniform_sup_risk_ratio_tendsto (fun i θ => (m i θ).expectationRisk)
    (fun i θ => (m i θ).benchmark) (fun i => pinskerOracleWorstBenchmark b β R σ D (n i))
    hPos hUpper hAttained hu.2.1
  have hSup : ∀ᶠ i in l, sSup (Set.range (fun θ : Θ => (m i θ).benchmark)) =
      pinskerOracleWorstBenchmark b β R σ D (n i) := by
    filter_upwards [hUpper, hAttained] with i hi ha
    obtain ⟨θ0, hθ0⟩ := ha
    have hb : BddAbove (Set.range (fun θ : Θ => (m i θ).benchmark)) := ⟨_, by
      rintro _ ⟨θ, rfl⟩
      exact hi θ⟩
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨θ, rfl⟩
      exact hi θ
    · rw [← hθ0]
      exact le_csSup hb (Set.mem_range_self θ0)
  refine ⟨hTransfer.1, hSup, hTransfer.2, hTransfer.2.congr' ?_⟩
  exact hSup.mono fun i hi => congrArg
    (fun z => sSup (Set.range (fun θ : Θ => (m i θ).expectationRisk)) / z) hi.symm

end
end KernelSeq
