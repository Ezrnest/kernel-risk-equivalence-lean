import KernelSeq.PinskerUpperBound
import KernelSeq.CanonicalGaussianRegression
import KernelSeq.ExactCountingEnumeration

/-!
# Pinsker upper bound in the actual independent Gaussian experiment

The entire family of observation laws is constructed from `μ × N(0,σ²)`.
No independent-pair, conditional-moment, or row-equality premise is needed
by this specialization of the original upper bound.
-/

namespace KernelSeq
open MeasureTheory Filter Topology Set
noncomputable section

universe uH uX

def canonicalPinskerOracleRiskRow {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH,uX} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (n : ℕ) (hn : 0 < n) (θ : PinskerSourceIndex b hs R) :
    TriangularRiskModel.{uH,uX,uX} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)) :=
  let lam := pinskerOracleScale s β R σ D (n : ℝ)
  let hlam := pinskerOracleScale_pos (zero_lt_one.trans_le hs) (zero_lt_one.trans hβ)
    hR hσ hD (Nat.cast_pos.mpr hn)
  CanonicalGaussianRegression.riskModel b.μ b.kernel_measurable b.kappa_nonneg b.diagonal_bound
    n hn θ.val (featureSourceBall_supported b.feature b.feature_memLp s (zero_le_one.trans hs) R θ.property)
    σ hσ lam hlam (ResidualFilter.pinsker lam s)
    (ResidualFilter.pinsker_spectralFilter hlam (zero_le_one.trans hs))
    (ResidualFilter.pinsker_contract hlam hs)

theorem canonicalPinskerOracleRiskRow_scaleModel {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH,uX} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (n : ℕ) (hn : 0 < n) (θ : PinskerSourceIndex b hs R) :
    (canonicalPinskerOracleRiskRow b hs hβ hR hσ hD n hn θ).scaleModel =
      fixedPinskerOracleScaleRow b hs hβ hR hσ hD n hn θ.val := rfl

/-- The Pinsker upper bound for Gaussian regression. The
supremum ranges over the actual operator source ball, including every target
in it. All observation laws, scales and intermediate estimates are supplied. -/
theorem canonical_gaussian_pinsker_sourceBall_upper_bound
    {I : Type*} {l : Filter I} [NeBot l] {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH,uX} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hcount : Tendsto
      (fun t => (featureSpectralCount b.feature b.feature_memLp t : ℝ) / (D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1))
    (n : I → ℕ) (hnpos : ∀ i, 0 < n i) (hn : Tendsto (fun i => (n i : ℝ)) l atTop) :
    let rows := fun i => canonicalPinskerOracleRiskRow b hs hβ hR hσ hD (n i) (hnpos i)
    (∀ᶠ i in l, BddAbove (Set.range (fun θ => (rows i θ).expectationRisk))) ∧
      Tendsto (fun i => sSup (Set.range (fun θ => (rows i θ).expectationRisk)) /
        pinskerOracleWorstBenchmark b β R σ D (n i)) l (𝓝 1) ∧
      Tendsto (fun i => (n i : ℝ)^pinskerRiskExponent s β *
        sSup (Set.range (fun θ => (rows i θ).expectationRisk))) l
        (𝓝 (pinskerUpperConstant s β R σ D)) := by
  let e := featureSpectrumEnumeration_of_exact_counting b.feature b.feature_memLp hD
    (zero_lt_one.trans hβ) hcount
  exact pinsker_sourceBall_upper_bound b hs hβ hR hσ hD e hcount n hnpos hn
    (fun i => canonicalPinskerOracleRiskRow b hs hβ hR hσ hD (n i) (hnpos i))
    (fun i θ => canonicalPinskerOracleRiskRow_scaleModel b hs hβ hR hσ hD (n i) (hnpos i) θ)
    (fun _ _ => rfl)

end
end KernelSeq
