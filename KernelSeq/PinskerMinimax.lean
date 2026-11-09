import KernelSeq.PinskerPrimitiveModel
import KernelSeq.PinskerMinimaxUpperBound
import KernelSeq.ActualPinskerPrior
import KernelSeq.PinskerMinimaxAssembly

/-!
# The original sharp Pinsker minimax constant and attainment

The lower bound covers the full measurable prediction class. All Gaussian
prior, source, concentration and truncation estimates are supplied from the
original primitive assumptions. No minimax, Bayes or tail certificate is an
input. The public primitive-RKHS wrapper also constructs the auxiliary model
and actual positive-spectrum enumeration internally.
-/

namespace KernelSeq
open MeasureTheory Filter Topology Set
noncomputable section

universe uH uX

theorem pinsker_minimax_constant
    {I : Type*} {l : Filter I} [NeBot l] {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH,uX} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hcount : Tendsto
      (fun t => (featureSpectralCount b.feature b.feature_memLp t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1))
    (n : I → ℕ) (hnpos : ∀ i, 0 < n i) (hn : Tendsto (fun i => (n i : ℝ)) l atTop) :
    Tendsto (fun i => (n i : ℝ)^pinskerRiskExponent s β *
      (gaussianRangeMinimaxRisk b.feature b.feature_memLp σ (n i)
        (b.SourceBall s (zero_le_one.trans hs) R)).toReal) l
      (𝓝 (pinskerUpperConstant s β R σ D)) := by
  let e := featureSpectrumEnumeration_of_exact_counting b.feature b.feature_memLp hD
    (zero_lt_one.trans hβ) hcount
  apply tendsto_of_pinsker_shaved_bounds _
    (pinskerUpperConstant_pos (zero_lt_one.trans_le hs) (zero_lt_one.trans hβ) hR hσ hD)
    (show 0 < 1/(s*β+1) by positivity) (show 1/(s*β+1) ≤ 1 by
      apply (div_le_one (by positivity : 0 < s*β+1)).mpr
      have hsp := zero_lt_one.trans_le hs
      have hβp := zero_lt_one.trans hβ
      nlinarith)
  · exact (pinsker_minimax_normalized_upper b hs hβ hR hσ hD hcount n hnpos hn).2
  · intro δ hδ hδ1 ε hε
    have hl := pinsker_minimax_normalized_shaved_lower b.feature b.feature_memLp e b.kappa_nonneg
      (Eventually.of_forall fun x => rkhsFeature_norm_le κ b.kappa_nonneg b.diagonal_bound x)
      hs hβ hR hσ hD hδ hδ1 hcount n hnpos hn ε hε
    simpa only [SpectralScaleModel.SourceBall, mul_comm] using hl

theorem pinsker_minimax_attainment
    {I : Type*} {l : Filter I} [NeBot l] {κ s β R σ D : ℝ}
    (b : SpectralScaleModel.{uH,uX} κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)))
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hcount : Tendsto
      (fun t => (featureSpectralCount b.feature b.feature_memLp t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1))
    (n : I → ℕ) (hnpos : ∀ i, 0 < n i) (hn : Tendsto (fun i => (n i : ℝ)) l atTop) :
    let rows := fun i => canonicalPinskerOracleRiskRow b hs hβ hR hσ hD (n i) (hnpos i)
    Tendsto (fun i => sSup (Set.range (fun θ => (rows i θ).expectationRisk)) /
      (gaussianRangeMinimaxRisk b.feature b.feature_memLp σ (n i)
        (b.SourceBall s (zero_le_one.trans hs) R)).toReal) l (𝓝 1) := by
  have hupper := (canonical_gaussian_pinsker_sourceBall_upper_bound b hs hβ hR hσ hD hcount n hnpos hn).2.2
  have hmin := pinsker_minimax_constant b hs hβ hR hσ hD hcount n hnpos hn
  have hC := pinskerUpperConstant_pos (zero_lt_one.trans_le hs) (zero_lt_one.trans hβ) hR hσ hD
  have hratio := hupper.div hmin hC.ne'
  rw [div_self hC.ne'] at hratio
  apply hratio.congr'
  apply Eventually.of_forall
  intro i
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hnpos i)) _).ne'

section OriginalPrimitiveModel
variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  (μ : Measure X) [IsProbabilityMeasure μ] {κ s : ℝ}
  (hkernel : Measurable (fun p : X × X => rkhsKernel (H := H) p.1 p.2))
  (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (H := H) x x ≤ κ^2) (hs : 1 ≤ s)

/-- The exact Pinsker minimax constant and its attainment in the class of
all measurable prediction-range decisions. -/
theorem rkhs_gaussian_pinsker_minimax
    {I : Type*} {l : Filter I} [NeBot l] {β R σ D : ℝ}
    (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hcount : Tendsto
      (fun t => (featureSpectralCount (rkhsFeature (H := H))
        (rkhsFeature_memLp μ hkernel κ hκ hdiag) t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1))
    (n : I → ℕ) (hnpos : ∀ i, 0 < n i) (hn : Tendsto (fun i => (n i : ℝ)) l atTop) :
    let k := rkhsFeature (H := H)
    let hk := rkhsFeature_memLp μ hkernel κ hκ hdiag
    let b := pinskerPrimitiveModel μ hkernel hκ hdiag hs
    let rows := fun i => canonicalPinskerOracleRiskRow b hs hβ hR hσ hD (n i) (hnpos i)
    Tendsto (fun i => (n i : ℝ)^pinskerRiskExponent s β *
      (gaussianRangeMinimaxRisk k hk σ (n i) (featureSourceBall k hk s (zero_le_one.trans hs) R)).toReal)
      l (𝓝 (pinskerUpperConstant s β R σ D)) ∧
    Tendsto (fun i => sSup (Set.range (fun θ => (rows i θ).expectationRisk)) /
      (gaussianRangeMinimaxRisk k hk σ (n i) (featureSourceBall k hk s (zero_le_one.trans hs) R)).toReal)
      l (𝓝 1) :=
  ⟨pinsker_minimax_constant (pinskerPrimitiveModel μ hkernel hκ hdiag hs)
      hs hβ hR hσ hD hcount n hnpos hn,
    pinsker_minimax_attainment (pinskerPrimitiveModel μ hkernel hκ hdiag hs)
      hs hβ hR hσ hD hcount n hnpos hn⟩

end OriginalPrimitiveModel
end
end KernelSeq
