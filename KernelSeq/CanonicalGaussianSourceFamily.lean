import KernelSeq.GaussianRangeMinimax
import KernelSeq.ConcreteRiskApplications
import KernelSeq.DependentSupRiskTransfer

/-!
# Canonical Gaussian risks over changing actual source balls

The source index is the literal operator source ball of each row. The
regression experiment and the measurable decision are constructed from the
primitive row data. Target support follows from actual source membership.
-/

namespace KernelSeq
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section

universe uH uX
variable {κ ρ A : ℝ} (b : SpectralScaleModel.{uH,uX} κ ρ A)

abbrev GaussianSourceIndex (s : ℝ) (hs : 0 ≤ s) (R : ℝ) :=
  ↥(b.SourceBall s hs R)

theorem gaussianSourceIndex_nonempty {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) :
    Nonempty (GaussianSourceIndex b s hs R) :=
  ⟨⟨0,zero_mem_predictionSourceBall _ _ s hs hR⟩⟩

def SpectralScaleModel.withTarget (f : Lp ℝ 2 b.μ) :
    SpectralScaleModel.{uH,uX} κ ρ A := { b with f := f }

def canonicalGaussianSourceRiskRow {s R σ : ℝ} {hs : 0 ≤ s}
    (hσ : 0 < σ) (f : GaussianSourceIndex b s hs R) :
    TriangularRiskModel.{uH,uX,uX} κ ρ A :=
  CanonicalGaussianRegression.riskModel b.μ b.kernel_measurable b.kappa_nonneg
    b.diagonal_bound b.n b.sample_pos f.val
    (featureSourceBall_supported b.feature b.feature_memLp s hs R f.property)
    σ hσ b.lam b.lambda_pos b.φ b.spectral_filter b.filter_contract

theorem canonicalGaussianSourceRiskRow_scaleModel {s R σ : ℝ} {hs : 0 ≤ s}
    (hσ : 0 < σ) (f : GaussianSourceIndex b s hs R) :
    (canonicalGaussianSourceRiskRow b hσ f).scaleModel = b.withTarget f.val := by
  cases b
  rfl

theorem canonicalGaussianSourceRiskRow_benchmark {s R σ : ℝ} {hs : 0 ≤ s}
    (hσ : 0 < σ) (f : GaussianSourceIndex b s hs R) :
    (canonicalGaussianSourceRiskRow b hσ f).benchmark =
      sequenceBenchmark b.feature b.feature_memLp b.φ f.val σ b.n := rfl

def canonicalGaussianSourceWorstRisk (s : ℝ) (hs : 0 ≤ s) (R : ℝ) {σ : ℝ} (hσ : 0 < σ) : ℝ :=
  sSup (Set.range (fun f : GaussianSourceIndex b s hs R =>
    (canonicalGaussianSourceRiskRow b hσ f).expectationRisk))

def gaussianSourceMinimaxRisk (s : ℝ) (hs : 0 ≤ s) (R σ : ℝ) : ℝ≥0∞ :=
  gaussianRangeMinimaxRisk b.feature b.feature_memLp σ b.n (b.SourceBall s hs R)

theorem gaussianSourceMinimaxRisk_lt_top {s R σ : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) :
    gaussianSourceMinimaxRisk b s hs R σ < ∞ :=
  gaussianRangeMinimaxRisk_sourceBall_lt_top b.feature b.feature_memLp
    b.kappa_nonneg
    (Eventually.of_forall fun x => rkhsFeature_norm_le κ b.kappa_nonneg b.diagonal_bound x)
    hs hR σ b.n

theorem gaussianSourceMinimaxRisk_le_canonicalWorstRisk {s R σ : ℝ}
    (hs : 0 ≤ s) (hσ : 0 < σ)
    (hbdd : BddAbove (Set.range (fun f : GaussianSourceIndex b s hs R =>
      (canonicalGaussianSourceRiskRow b hσ f).expectationRisk))) :
    gaussianSourceMinimaxRisk b s hs R σ ≤
      ENNReal.ofReal (canonicalGaussianSourceWorstRisk b s hs R hσ) := by
  apply (gaussianRangeMinimaxRisk_le_spectral_sup b σ (b.SourceBall s hs R)).trans
  apply iSup_le
  intro f
  let bf := b.withTarget f.val
  have hsupp : bf.f ∈ (predictionCovariance
      (featureEmbedding bf.μ bf.feature bf.feature_memLp)).range.topologicalClosure :=
    featureSourceBall_supported b.feature b.feature_memLp s hs R f.property
  exact (gaussianSpectralDecision_risk_eq_expectationRisk bf hσ hsupp).le.trans
    (ENNReal.ofReal_le_ofReal (le_csSup hbdd (Set.mem_range_self f)))

theorem canonicalGaussianSourceWorstRisk_nonneg {s R σ : ℝ}
    (hs : 0 ≤ s) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hbdd : BddAbove (Set.range (fun f : GaussianSourceIndex b s hs R =>
      (canonicalGaussianSourceRiskRow b hσ f).expectationRisk))) :
    0 ≤ canonicalGaussianSourceWorstRisk b s hs R hσ := by
  obtain ⟨f⟩ := gaussianSourceIndex_nonempty b hs hR
  have hf : 0 ≤ (canonicalGaussianSourceRiskRow b hσ f).expectationRisk := by
    apply integral_nonneg
    intro ω
    exact sq_nonneg _
  exact hf.trans (le_csSup hbdd (Set.mem_range_self f))

end
end KernelSeq
