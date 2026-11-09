import KernelSeq.GaussianRangeMinimax
import KernelSeq.CanonicalPinskerUpperBound

/-!
# The upper half of the original all-rule Pinsker minimax limit

The rule is valued in the genuine closed prediction range and is jointly
measurable on design/response data. Its risk is the original Gaussian risk.
The minimax infimum is over every such measurable rule, not merely spectral
or linear rules.
-/

namespace KernelSeq
open MeasureTheory Filter Set Topology
open scoped ENNReal
noncomputable section

universe uH uX

theorem gaussianRangeMinimaxRisk_le_pinsker_expected_sup
    {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH,uX} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (n : ℕ) (hn : 0 < n)
    (hbdd : BddAbove (Set.range (fun θ : PinskerSourceIndex b hs R =>
      (canonicalPinskerOracleRiskRow b hs hβ hR hσ hD n hn θ).expectationRisk))) :
    gaussianRangeMinimaxRisk b.feature b.feature_memLp σ n (b.SourceBall s (zero_le_one.trans hs) R) ≤
      ENNReal.ofReal (sSup (Set.range (fun θ : PinskerSourceIndex b hs R =>
        (canonicalPinskerOracleRiskRow b hs hβ hR hσ hD n hn θ).expectationRisk))) := by
  let b0 := fixedPinskerOracleScaleRow b hs hβ hR hσ hD n hn 0
  apply (gaussianRangeMinimaxRisk_le_spectral_sup b0 σ (b.SourceBall s (zero_le_one.trans hs) R)).trans
  apply iSup_le
  intro θ
  let bt := fixedPinskerOracleScaleRow b hs hβ hR hσ hD n hn θ.val
  have hsupport : bt.f ∈ (predictionCovariance
      (featureEmbedding bt.μ bt.feature bt.feature_memLp)).range.topologicalClosure :=
    featureSourceBall_supported b.feature b.feature_memLp s (zero_le_one.trans hs) R θ.property
  have heq := gaussianSpectralDecision_risk_eq_expectationRisk bt hσ hsupport
  exact heq.le.trans (ENNReal.ofReal_le_ofReal (le_csSup hbdd (Set.mem_range_self θ)))

/-- The actual original prediction-range minimax risk is finite, and its
normalized upper limit is at most the exact original Pinsker constant. -/
theorem pinsker_minimax_normalized_upper
    {I : Type*} {l : Filter I} [NeBot l] {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH,uX} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hcount : Tendsto
      (fun t => (featureSpectralCount b.feature b.feature_memLp t : ℝ) / (D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1))
    (n : I → ℕ) (hnpos : ∀ i, 0 < n i) (hn : Tendsto (fun i => (n i : ℝ)) l atTop) :
    (∀ i, gaussianRangeMinimaxRisk b.feature b.feature_memLp σ (n i)
      (b.SourceBall s (zero_le_one.trans hs) R) < ∞) ∧
    ∀ ε > 0, ∀ᶠ i in l,
      (n i : ℝ)^pinskerRiskExponent s β *
        (gaussianRangeMinimaxRisk b.feature b.feature_memLp σ (n i)
          (b.SourceBall s (zero_le_one.trans hs) R)).toReal ≤
        pinskerUpperConstant s β R σ D + ε := by
  let Θ := PinskerSourceIndex b hs R
  let rows := fun i => canonicalPinskerOracleRiskRow b hs hβ hR hσ hD (n i) (hnpos i)
  let S := fun i => sSup (Set.range (fun θ : Θ => (rows i θ).expectationRisk))
  have hupper := canonical_gaussian_pinsker_sourceBall_upper_bound b hs hβ hR hσ hD hcount n hnpos hn
  have hfinite (i : I) := gaussianRangeMinimaxRisk_sourceBall_lt_top b.feature b.feature_memLp
    b.kappa_nonneg (Eventually.of_forall (fun x => rkhsFeature_norm_le κ b.kappa_nonneg b.diagonal_bound x))
    (zero_le_one.trans hs) hR.le σ (n i)
  refine ⟨hfinite, fun ε hε => ?_⟩
  have hlimit := hupper.2.2.eventually (gt_mem_nhds (by linarith :
    pinskerUpperConstant s β R σ D < pinskerUpperConstant s β R σ D + ε))
  filter_upwards [hupper.1, hlimit] with i hbi hli
  have hb := gaussianRangeMinimaxRisk_le_pinsker_expected_sup b hs hβ hR hσ hD (n i) (hnpos i) hbi
  have hS0 : 0 ≤ S i := by
    let θ0 : Θ := ⟨0, zero_mem_predictionSourceBall _ _ s (zero_le_one.trans hs) hR.le⟩
    have h0 : 0 ≤ (rows i θ0).expectationRisk := integral_nonneg fun _ => sq_nonneg _
    exact h0.trans (le_csSup hbi (Set.mem_range_self θ0))
  have hreal := (ENNReal.toReal_le_toReal (hfinite i).ne ENNReal.ofReal_ne_top).mpr hb
  rw [ENNReal.toReal_ofReal hS0] at hreal
  exact (mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans hli.le

end
end KernelSeq
