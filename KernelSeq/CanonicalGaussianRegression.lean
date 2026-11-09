import KernelSeq.TriangularRiskModel
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.HasLaw

/-!
# Canonical independent Gaussian regression observations

The raw sample is the actual finite product of `μ × N(0,σ²)`. Regression
responses are formed from a measurable target representative. Full-pair
independence, design laws and own-design noise moments are proved from this
construction; the design space needs no standard-Borel assumption.
-/

namespace KernelSeq.CanonicalGaussianRegression

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def noiseMeasure (σ : ℝ) : Measure ℝ := gaussianReal 0 ⟨σ^2, sq_nonneg σ⟩

instance noiseMeasure_probability (σ : ℝ) : IsProbabilityMeasure (noiseMeasure σ) := by
  unfold noiseMeasure
  infer_instance

instance noiseMeasure_gaussian (σ : ℝ) : IsGaussian (noiseMeasure σ) := by
  unfold noiseMeasure
  infer_instance

def sampleMeasure (σ : ℝ) (n : ℕ) : Measure (Fin n → X × ℝ) :=
  Measure.pi (fun _ => μ.prod (noiseMeasure σ))

instance sampleMeasure_probability (σ : ℝ) (n : ℕ) : IsProbabilityMeasure (sampleMeasure μ σ n) := by
  unfold sampleMeasure
  infer_instance

def design {n : ℕ} (i : Fin n) (ω : Fin n → X × ℝ) : X := (ω i).1
def noise {n : ℕ} (i : Fin n) (ω : Fin n → X × ℝ) : ℝ := (ω i).2

def observation (f : X → ℝ) {n : ℕ} (i : Fin n) (ω : Fin n → X × ℝ) : X × ℝ :=
  (design i ω, f (design i ω) + noise i ω)

theorem measurable_design {n : ℕ} (i : Fin n) : Measurable (design (X := X) i) := by
  unfold design
  fun_prop

theorem measurable_noise {n : ℕ} (i : Fin n) : Measurable (noise (X := X) i) := by
  unfold noise
  fun_prop

theorem measurable_observation {f : X → ℝ} (hf : Measurable f) {n : ℕ} (i : Fin n) :
    Measurable (observation f i) := by
  exact (measurable_design i).prodMk ((hf.comp (measurable_design i)).add (measurable_noise i))

theorem design_law (σ : ℝ) {n : ℕ} (i : Fin n) :
    MeasurePreserving (design i) (sampleMeasure μ σ n) μ :=
  measurePreserving_fst.comp (measurePreserving_eval (fun _ : Fin n => μ.prod (noiseMeasure σ)) i)

theorem noise_law (σ : ℝ) {n : ℕ} (i : Fin n) :
    MeasurePreserving (noise i) (sampleMeasure μ σ n) (noiseMeasure σ) :=
  measurePreserving_snd.comp (measurePreserving_eval (fun _ : Fin n => μ.prod (noiseMeasure σ)) i)

theorem independent_observations (σ : ℝ) {f : X → ℝ} (hf : Measurable f) (n : ℕ) :
    iIndepFun (observation f) (sampleMeasure μ σ n) := by
  exact iIndepFun_pi (fun _ => (measurable_fst.prodMk ((hf.comp measurable_fst).add measurable_snd)).aemeasurable)

theorem design_independent_noise (σ : ℝ) {n : ℕ} (i : Fin n) :
    IndepFun (design i) (noise i) (sampleMeasure μ σ n) := by
  apply (indepFun_iff_hasLaw_prodMk_prod
    (show HasLaw (design i) μ (sampleMeasure μ σ n) from
      ⟨(design_law μ σ i).aemeasurable, (design_law μ σ i).map_eq⟩)
    (show HasLaw (noise i) (noiseMeasure σ) (sampleMeasure μ σ n) from
      ⟨(noise_law μ σ i).aemeasurable, (noise_law μ σ i).map_eq⟩)).mpr
  exact ⟨(measurePreserving_eval (fun _ : Fin n => μ.prod (noiseMeasure σ)) i).aemeasurable,
    (measurePreserving_eval (fun _ : Fin n => μ.prod (noiseMeasure σ)) i).map_eq⟩

theorem noise_memLp (σ : ℝ) {n : ℕ} (i : Fin n) :
    MemLp (noise i) 2 (sampleMeasure μ σ n) :=
  (show MemLp id 2 (noiseMeasure σ) from IsGaussian.memLp_two_id).comp_measurePreserving (noise_law μ σ i)

theorem integral_noise (σ : ℝ) {n : ℕ} (i : Fin n) :
    (∫ ω, noise i ω ∂sampleMeasure μ σ n) = 0 := by
  have he := integral_map (noise_law μ σ i).aemeasurable aestronglyMeasurable_id
  rw [(noise_law μ σ i).map_eq] at he
  exact he.symm.trans (integral_id_gaussianReal (μ := 0) (v := ⟨σ^2, sq_nonneg σ⟩))

theorem integral_noise_sq (σ : ℝ) {n : ℕ} (i : Fin n) :
    (∫ ω, noise i ω ^ 2 ∂sampleMeasure μ σ n) = σ^2 := by
  have he := integral_map (noise_law μ σ i).aemeasurable
    (show AEStronglyMeasurable (fun r : ℝ => r^2) ((sampleMeasure μ σ n).map (noise i)) from by fun_prop)
  rw [(noise_law μ σ i).map_eq] at he
  have hv := variance_id_gaussianReal (μ := 0) (v := ⟨σ^2, sq_nonneg σ⟩)
  rw [variance_eq_integral aemeasurable_id] at hv
  simp only [id_eq, integral_id_gaussianReal, sub_zero] at hv
  exact he.symm.trans hv

private theorem condExp_noise_function (σ : ℝ) {n : ℕ} (i : Fin n)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (sampleMeasure μ σ n)[g ∘ noise i | MeasurableSpace.comap (design i) inferInstance] =ᵐ[sampleMeasure μ σ n]
      (fun _ => ∫ ω, g (noise i ω) ∂sampleMeasure μ σ n) := by
  have hn : Measurable (g ∘ noise (X := X) i) := hg.comp (measurable_noise i)
  have hD : Measurable (design (X := X) i) := measurable_design i
  have hgn : Measurable[MeasurableSpace.comap (g ∘ noise (X := X) i) inferInstance] (g ∘ noise i) :=
    Measurable.of_comap_le le_rfl
  have hi : IndepFun (g ∘ noise (X := X) i) (design i) (sampleMeasure μ σ n) :=
    (design_independent_noise μ σ i).symm.comp hg measurable_id
  exact condExp_indep_eq hn.comap_le hD.comap_le hgn.stronglyMeasurable hi

omit [MeasurableSpace X] in
theorem observationNoise_eq {f : X → ℝ} {n : ℕ} (i : Fin n) :
    observationNoise (observation f i) f = noise i := by
  funext ω
  exact add_sub_cancel_left _ _

theorem noise_mean (σ : ℝ) (f : X → ℝ) {n : ℕ} (i : Fin n) :
    (sampleMeasure μ σ n)[observationNoise (observation f i) f |
      observationDesignSigma (observation f i)] =ᵐ[sampleMeasure μ σ n] (fun _ => 0) := by
  rw [observationNoise_eq]
  exact (condExp_noise_function μ σ i id measurable_id).trans
    (Eventually.of_forall fun _ => integral_noise μ σ i)

theorem noise_second (σ : ℝ) (f : X → ℝ) {n : ℕ} (i : Fin n) :
    (sampleMeasure μ σ n)[(fun ω => observationNoise (observation f i) f ω ^ 2) |
      observationDesignSigma (observation f i)] =ᵐ[sampleMeasure μ σ n] (fun _ => σ^2) := by
  rw [observationNoise_eq]
  exact (condExp_noise_function μ σ i (fun r => r^2) (by fun_prop)).trans
    (Eventually.of_forall fun _ => integral_noise_sq μ σ i)

/-- An actual row of the original regression model, constructed from its
primitive kernel, target and filter assumptions. Conditional moments and
full-pair independence are supplied by the canonical Gaussian sample. -/
def riskModel {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H] [RKHS ℝ H X ℝ]
    {κ ρ A : ℝ}
    (hkernel : Measurable (fun p : X × X => rkhsKernel (H := H) p.1 p.2))
    (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (H := H) x x ≤ κ^2)
    (n : ℕ) (hn : 0 < n) (f : Lp ℝ 2 μ)
    (hsupport : f ∈ (predictionCovariance (featureEmbedding μ (rkhsFeature (H := H))
      (rkhsFeature_memLp μ hkernel κ hκ hdiag))).range.topologicalClosure)
    (σ : ℝ) (hσ : 0 < σ) (lam : ℝ) (hlam : 0 < lam) (φ : ℝ → ℝ)
    (hf : ResidualFilter.SpectralFilter (κ^2) φ) (h : ResidualFilter.Contract lam (κ^2) ρ A φ) :
    TriangularRiskModel κ ρ A where
  H := H
  X := X
  Ω := Fin n → X × ℝ
  μ := μ
  P := sampleMeasure μ σ n
  kernel_measurable := hkernel
  kappa_nonneg := hκ
  diagonal_bound := hdiag
  n := n
  sample_pos := hn
  Z := observation (lpRepresentative f)
  observation_measurable := measurable_observation (lpRepresentative_measurable f)
  design_law := design_law μ σ
  independent_pairs := independent_observations μ σ (lpRepresentative_measurable f) n
  f := f
  target_support := hsupport
  σ := σ
  noise_pos := hσ
  noise_mean := noise_mean μ σ (lpRepresentative f)
  noise_second := noise_second μ σ (lpRepresentative f)
  lam := lam
  lambda_pos := hlam
  φ := φ
  spectral_filter := hf
  filter_contract := h

end
end KernelSeq.CanonicalGaussianRegression
