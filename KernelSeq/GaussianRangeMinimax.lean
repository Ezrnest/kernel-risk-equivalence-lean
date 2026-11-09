import KernelSeq.GaussianSpectralDecision
import KernelSeq.SourceNormBounds

/-!
# The original full prediction-range minimax class

The decision codomain is the actual closed population prediction range,
as in the manuscript. It is not restricted to linear rules or to any finite
spectral span. Ambient-rule lower bounds apply to this class, while the
actual measurable spectral estimator supplies its upper bound.
-/

namespace KernelSeq
open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

local instance rangeMinimaxLpMeasurableSpace : MeasurableSpace (Lp ℝ 2 μ) := borel _
local instance rangeMinimaxLpBorelSpace : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩

def gaussianRangeMinimaxRisk (k : X → H) (hk : MemLp k 2 μ)
    (σ : ℝ) (n : ℕ) (F : Set (Lp ℝ 2 μ)) : ℝ≥0∞ :=
  ⨅ (d : (Fin n → X) × EuclideanSpace ℝ (Fin n) → PredictionRange (featureEmbedding μ k hk))
    (_hd : Measurable d), ⨆ f : F, gaussianRegressionRisk μ σ (fun z => (d z : Lp ℝ 2 μ)) f.val

omit [CompleteSpace H] [IsProbabilityMeasure μ] in
theorem gaussianRegressionMinimaxRisk_le_rangeMinimaxRisk
    (k : X → H) (hk : MemLp k 2 μ) (σ : ℝ) (n : ℕ) (F : Set (Lp ℝ 2 μ)) :
    gaussianRegressionMinimaxRisk μ σ n F ≤ gaussianRangeMinimaxRisk k hk σ n F := by
  unfold gaussianRangeMinimaxRisk
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact iInf_le_of_le (fun z => (d z : Lp ℝ 2 μ))
    (iInf_le_of_le (measurable_subtype_coe.comp hd) le_rfl)

theorem gaussianRangeMinimaxRisk_sourceBall_lt_top
    (k : X → H) (hk : MemLp k 2 μ) {κ s R : ℝ}
    (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (σ : ℝ) (n : ℕ) :
    gaussianRangeMinimaxRisk k hk σ n (featureSourceBall k hk s hs R) < ∞ := by
  let B := (1+κ^2)^(s/2)*R
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : gaussianRangeMinimaxRisk k hk σ n (featureSourceBall k hk s hs R) ≤ ENNReal.ofReal (B^2) := by
    apply iInf_le_of_le (fun _ => (0 : PredictionRange (featureEmbedding μ k hk)))
    apply iInf_le_of_le measurable_const
    apply iSup_le
    intro f
    have hf : ‖f.val‖ ≤ B := featureSourceBall_norm_le k hk hκ hbound hs f.property
    simpa only [gaussianRegressionRisk, predictionDecisionRisk, Submodule.coe_zero,
      zero_sub, norm_neg, lintegral_const, measure_univ, mul_one] using
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg f.val) hf 2)
  exact hb.trans_lt ENNReal.ofReal_lt_top

universe uH uX
variable {κ ρ A : ℝ}

def gaussianSpectralRangeDecision (b : SpectralScaleModel.{uH,uX} κ ρ A) :
    (Fin b.n → b.X) × EuclideanSpace ℝ (Fin b.n) →
      PredictionRange (featureEmbedding b.μ b.feature b.feature_memLp) := fun z =>
  ⟨gaussianSpectralDecision b z, by
    apply subset_closure
    exact ⟨_, rfl⟩⟩

theorem measurable_gaussianSpectralRangeDecision (b : SpectralScaleModel.{uH,uX} κ ρ A) :
    Measurable (gaussianSpectralRangeDecision b) :=
  (measurable_gaussianSpectralDecision b).subtype_mk

/-- A true measurable rule valued in the actual closed prediction range
gives an upper bound for the manuscript's unrestricted minimax risk. -/
theorem gaussianRangeMinimaxRisk_le_spectral_sup
    (b : SpectralScaleModel.{uH,uX} κ ρ A) (σ : ℝ) (F : Set (Lp ℝ 2 b.μ)) :
    gaussianRangeMinimaxRisk b.feature b.feature_memLp σ b.n F ≤
      ⨆ f : F, gaussianRegressionRisk b.μ σ (gaussianSpectralDecision b) f.val :=
  iInf_le_of_le (gaussianSpectralRangeDecision b)
    (iInf_le_of_le (measurable_gaussianSpectralRangeDecision b) le_rfl)

end
end KernelSeq
