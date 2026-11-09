import KernelSeq.GaussianSequenceRisk
import Mathlib.Probability.Independence.InfinitePi

/-!
# A concrete iid infinite Gaussian sequence probability model

The product measure below supplies the Gaussian laws and full independence;
the checked sequence-risk result therefore has a concrete model witness.
-/

open MeasureTheory ProbabilityTheory

namespace KernelSeq

/-- The actual product of standard Gaussian laws, on all coordinate families.
The sequence-risk application has a countable positive-spectrum index. -/
noncomputable def gaussianProductLaw (J : Type*) : Measure (J → ℝ) :=
  Measure.infinitePi (fun _ : J => gaussianReal 0 1)

instance gaussianProductLaw_isProbabilityMeasure (J : Type*) :
    IsProbabilityMeasure (gaussianProductLaw J) := by
  unfold gaussianProductLaw
  infer_instance

theorem gaussianProductLaw_coordinate_hasLaw {J : Type*} (j : J) :
    HasLaw (fun ω : J → ℝ => ω j) (gaussianReal 0 1) (gaussianProductLaw J) :=
  (measurePreserving_eval_infinitePi (fun _ : J => gaussianReal 0 1) j).hasLaw

/-- Independence of all finite coordinate families is proved from the product
measure, rather than assumed as a noise-model certificate. -/
theorem gaussianProductLaw_iIndepFun (J : Type*) :
    iIndepFun (fun j (ω : J → ℝ) => ω j) (gaussianProductLaw J) :=
  iIndepFun_infinitePi (X := fun _ : J => (id : ℝ → ℝ)) (fun _ => measurable_id)

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual infinite sequence error on its concrete iid Gaussian product
space, in the genuine positive singular coordinates of the feature embedding. -/
noncomputable def canonicalGaussianSequenceError (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (hf : f ∈ PredictionRange (featureEmbedding μ k hk)) (σ : ℝ) (n : ℕ) :
    (PredictionSingularIndex (featureEmbedding μ k hk) → ℝ) →
      lp (fun _ : PredictionSingularIndex (featureEmbedding μ k hk) => ℝ) 2 :=
  featureGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n
    (fun j (ω : PredictionSingularIndex (featureEmbedding μ k hk) → ℝ) => ω j)
    (fun j => gaussianProductLaw_coordinate_hasLaw j)

/-- The concrete iid Gaussian model has exactly the manuscript's sequence
risk, and a square-integrable strongly measurable error vector. -/
theorem canonicalGaussianSequenceError_risk (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (hf : f ∈ PredictionRange (featureEmbedding μ k hk))
    (σ : ℝ) (n : ℕ) (hn : 0 < n) :
    StronglyMeasurable (canonicalGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n) ∧
      MemLp (canonicalGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n) 2
        (gaussianProductLaw (PredictionSingularIndex (featureEmbedding μ k hk))) ∧
      (∫ ω, ‖canonicalGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n ω‖ ^ 2
        ∂gaussianProductLaw (PredictionSingularIndex (featureEmbedding μ k hk))) =
        sequenceBenchmark k hk φ f σ n := by
  refine ⟨featureGaussianSequenceError_stronglyMeasurable k hk φ hlam hM hfilter h f hf σ n _ _, ?_⟩
  have hr := featureGaussianSequenceError_risk k hk φ hlam hM hfilter h f hf σ n hn
    (fun j (ω : PredictionSingularIndex (featureEmbedding μ k hk) → ℝ) => ω j)
    (fun j => gaussianProductLaw_coordinate_hasLaw j)
  exact ⟨hr.1, hr.2.2⟩

/-- The sequence observations themselves are coordinate families; they need
not lie in `ℓ²` before applying the filter. -/
noncomputable def canonicalGaussianObservation (k : X → H) (hk : MemLp k 2 μ)
    (f : Lp ℝ 2 μ) (σ : ℝ) (n : ℕ)
    (ω : PredictionSingularIndex (featureEmbedding μ k hk) → ℝ)
    (j : PredictionSingularIndex (featureEmbedding μ k hk)) : ℝ :=
  featureSequenceCoefficient k hk f j + (σ / Real.sqrt (n : ℝ)) * ω j

/-- The constructed `ℓ²` vector is the estimation error `q_j y_j - f_j`
for the concrete iid Gaussian sequence observations, coordinate by coordinate. -/
theorem canonicalGaussianSequenceError_coordinates_ae (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (hf : f ∈ PredictionRange (featureEmbedding μ k hk))
    (σ : ℝ) (n : ℕ) (hn : 0 < n) :
    ∀ᵐ ω ∂gaussianProductLaw (PredictionSingularIndex (featureEmbedding μ k hk)), ∀ j,
      canonicalGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n ω j =
        ResidualFilter.shrinkage φ j.1.1 * canonicalGaussianObservation k hk f σ n ω j -
          featureSequenceCoefficient k hk f j := by
  have hcoord := (featureGaussianSequenceError_risk k hk φ hlam hM hfilter h f hf σ n hn
    (fun j (ω : PredictionSingularIndex (featureEmbedding μ k hk) → ℝ) => ω j)
    (fun j => gaussianProductLaw_coordinate_hasLaw j)).2.1
  filter_upwards [hcoord] with ω hω j
  change featureGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n
    (fun j (ω : PredictionSingularIndex (featureEmbedding μ k hk) → ℝ) => ω j)
    (fun j => gaussianProductLaw_coordinate_hasLaw j) ω j = _
  rw [hω j]
  simp only [canonicalGaussianObservation]
  ring

end KernelSeq
