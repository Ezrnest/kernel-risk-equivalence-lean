import KernelSeq.FixedPinskerSupRiskTransfer
import KernelSeq.PinskerOracleBenchmark

/-!
# The original Pinsker upper bound for actual RKHS risk

The expected-risk supremum over the power-source ball is asymptotic
to its exact sequence benchmark and
has the original sharp displayed constant. Exact counting, filter bounds,
source estimates, all three scales and uniform risk transfer are proved
internally. The primitive row law may satisfy the more general two noise
moments; the original independent Gaussian experiment is a specialization.
-/

namespace KernelSeq
open MeasureTheory Filter Topology Set
noncomputable section

universe uH uX uΩ

theorem pinsker_sourceBall_upper_bound {I : Type*} {l : Filter I} [NeBot l]
    {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH,uX} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (e : b.SpectrumEnumeration)
    (hcount : Tendsto
      (fun t => (featureSpectralCount b.feature b.feature_memLp t : ℝ) / (D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1))
    (n : I → ℕ) (hnpos : ∀ i, 0 < n i) (hn : Tendsto (fun i => (n i : ℝ)) l atTop)
    (rows : I → PinskerSourceIndex b hs R →
      TriangularRiskModel.{uH,uX,uΩ} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)))
    (hfixed : ∀ i θ, (rows i θ).scaleModel =
      fixedPinskerOracleScaleRow b hs hβ hR hσ hD (n i) (hnpos i) θ.val)
    (hnoise : ∀ i θ, (rows i θ).σ = σ) :
    (∀ᶠ i in l, BddAbove (Set.range (fun θ => (rows i θ).expectationRisk))) ∧
      Tendsto (fun i => sSup (Set.range (fun θ => (rows i θ).expectationRisk)) /
        pinskerOracleWorstBenchmark b β R σ D (n i)) l (𝓝 1) ∧
      Tendsto (fun i => (n i : ℝ)^pinskerRiskExponent s β *
        sSup (Set.range (fun θ => (rows i θ).expectationRisk))) l
        (𝓝 (pinskerUpperConstant s β R σ D)) := by
  have htransfer := fixed_pinsker_sourceBall_sup_risk_transfer b hs hβ hR hσ hD e hcount
    n hnpos hn rows hfixed hnoise
  have hnorm := pinskerWorstSequenceBenchmark_normalized_limit b.feature b.feature_memLp e
    hs hβ hR hσ hD hcount (fun i => (n i : ℝ))
    (fun i => Nat.cast_pos.mpr (hnpos i)) hn
  have hSpos (i : I) : 0 < pinskerOracleWorstBenchmark b β R σ D (n i) := by
    have hl := pinskerOracleScale_pos (zero_lt_one.trans_le hs) (zero_lt_one.trans hβ)
      hR hσ hD (Nat.cast_pos.mpr (hnpos i))
    apply add_pos_of_pos_of_nonneg
    · exact mul_pos (sq_pos_of_pos hR) (Real.rpow_pos_of_pos hl _)
    · exact mul_nonneg (div_nonneg (sq_nonneg σ) (Nat.cast_nonneg _))
        (featureFilterDimension_nonneg _ _ _)
  have hmul := htransfer.2.2.1.mul hnorm
  simp only [one_mul] at hmul
  refine ⟨htransfer.1, htransfer.2.2.1, ?_⟩
  apply hmul.congr'
  apply Eventually.of_forall
  intro i
  change
    (sSup (Set.range (fun θ => (rows i θ).expectationRisk)) /
      pinskerOracleWorstBenchmark b β R σ D (n i)) *
    ((n i : ℝ)^pinskerRiskExponent s β * pinskerOracleWorstBenchmark b β R σ D (n i)) = _
  field_simp [(hSpos i).ne']

end
end KernelSeq
