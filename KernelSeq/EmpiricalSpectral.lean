import KernelSeq.CompactCalculus
import KernelSeq.CompactCovariance
import KernelSeq.EmpiricalCovariance
import KernelSeq.ConditionalNoise
import Mathlib.Tactic.GCongr

/-!
# Actual empirical spectral estimators and their deterministic bounds

The covariance and response representer are the actual finite sample maps.
The filter acts on the infinite-dimensional real Hilbert space through its
constructed compact spectral calculus. The finite-sample prediction coefficients
below have the deterministic bounds required by conditional risk.

Design strong measurability of covariance, Gram matrix, and unfiltered sample
representers is proved. `EmpiricalMeasurability` proves strong measurability
of the actual filtered estimator under the manuscript's residual contract,
using continuity of shrinkage and resolvent limits on sample features.
-/

open MeasureTheory InnerProductSpace LinearMap Module.End
open scoped BigOperators

namespace KernelSeq

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The empirical operator has range inside the actual finite feature span. -/
theorem empiricalCovariance_range_le_span {n : ℕ} (v : Fin n → H) :
    LinearMap.range (empiricalCovariance v).toLinearMap ≤ Submodule.span ℝ (Set.range v) := by
  rintro y ⟨h, rfl⟩
  change empiricalCovariance v h ∈ Submodule.span ℝ (Set.range v)
  rw [empiricalCovariance_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- Actual finite rank, without assuming finite-dimensional ambient space. -/
theorem empiricalCovariance_finiteDimensional_range {n : ℕ} (v : Fin n → H) :
    FiniteDimensional ℝ (LinearMap.range (empiricalCovariance v).toLinearMap) := by
  letI := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  exact Submodule.finiteDimensional_of_le (empiricalCovariance_range_le_span v)

/-- A finite empirical sum of rank-one operators is compact. -/
theorem empiricalCovariance_isCompact {n : ℕ} (v : Fin n → H) :
    IsCompactOperator (empiricalCovariance v) := by
  let K : Submodule ℝ (H →L[ℝ] H) := compactOperator (RingHom.id ℝ) H H
  change empiricalCovariance v ∈ K
  apply K.smul_mem
  exact K.sum_mem (fun i _ => isCompactOperator_rankOne_real (v i) (v i))

/-- Every sample feature is orthogonal to the actual empirical kernel. -/
theorem sample_inner_eq_zero_of_empiricalCovariance_eq_zero {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) {z : H} (hz : empiricalCovariance v z = 0) (i : Fin n) :
    inner ℝ (v i) z = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hq := empiricalCovariance_quadratic v z
  rw [hz, inner_zero_right] at hq
  have hsum : ∑ j, (inner ℝ (v j) z) ^ 2 = 0 :=
    (mul_eq_zero.mp hq.symm).resolve_left (inv_ne_zero hn0)
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    sq_nonneg (inner ℝ (v j) z)) (Finset.mem_univ i)
  rw [hsum] at hi
  exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))

variable [CompleteSpace H]

/-- The manuscript's filter acting on the actual empirical covariance. -/
noncomputable def empiricalFilterOperator {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) (κ : ℝ) (hv : ∀ i, ‖v i‖ ^ 2 ≤ κ ^ 2)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) : H →L[ℝ] H :=
  compactFilterOperator (empiricalCovariance v) (empiricalCovariance_isCompact v)
    (empiricalCovariance_isPositive v) φ hlam (norm_empiricalCovariance_le_bound hn v κ hv) h

theorem empiricalFilterOperator_norm_le {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) (κ : ℝ) (hv : ∀ i, ‖v i‖ ^ 2 ≤ κ ^ 2)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    ‖empiricalFilterOperator hn v κ hv φ hlam h‖ ≤ A / lam := by
  unfold empiricalFilterOperator compactFilterOperator
  apply compactSpectralMultiplier_norm_le

theorem empiricalFilterOperator_eigen {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) (κ : ℝ) (hv : ∀ i, ‖v i‖ ^ 2 ≤ κ ^ 2)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) {u : H} {t : ℝ}
    (hu : empiricalCovariance v u = t • u) :
    empiricalFilterOperator hn v κ hv φ hlam h u = φ t • u := by
  unfold empiricalFilterOperator compactFilterOperator
  apply compactSpectralMultiplier_eigen
  exact hu

/-- The actual empirical spectral estimator, with observed response vector `y`. -/
noncomputable def empiricalSpectralEstimator {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) (κ : ℝ) (hv : ∀ i, ‖v i‖ ^ 2 ≤ κ ^ 2) (y : Fin n → ℝ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) : H :=
  empiricalFilterOperator hn v κ hv φ hlam h (empiricalRepresenter v y)

theorem empiricalSpectralEstimator_norm_le {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) (κ : ℝ) (hv : ∀ i, ‖v i‖ ^ 2 ≤ κ ^ 2) (y : Fin n → ℝ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    ‖empiricalSpectralEstimator hn v κ hv y φ hlam h‖ ≤
      A / lam * ‖empiricalRepresenter v y‖ :=
  (empiricalFilterOperator hn v κ hv φ hlam h).le_of_opNorm_le
    (empiricalFilterOperator_norm_le hn v κ hv φ hlam h) _

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual prediction coefficient multiplying one observation's noise. -/
noncomputable def empiricalPredictionCoefficient (S : H →L[ℝ] E) {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) (κ : ℝ) (hv : ∀ i, ‖v i‖ ^ 2 ≤ κ ^ 2)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) : E :=
  (n : ℝ)⁻¹ • S (empiricalFilterOperator hn v κ hv φ hlam h (v i))

/-- The prediction is exactly the finite linear response rule with these coefficients. -/
theorem empiricalSpectralEstimator_prediction_sum (S : H →L[ℝ] E) {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) (κ : ℝ) (hv : ∀ i, ‖v i‖ ^ 2 ≤ κ ^ 2) (y : Fin n → ℝ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    S (empiricalSpectralEstimator hn v κ hv y φ hlam h) =
      ∑ i, y i • empiricalPredictionCoefficient S hn v κ hv φ hlam h i := by
  simp only [empiricalSpectralEstimator, empiricalRepresenter, map_smul, map_sum,
    empiricalPredictionCoefficient, Finset.smul_sum, smul_smul]
  congr 1
  funext i
  rw [mul_comm]

/-- The actual prediction error is bias plus the finite coefficient-weighted noise. -/
theorem empiricalSpectralEstimator_prediction_noise_decomposition
    (S : H →L[ℝ] E) {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) (κ : ℝ) (hv : ∀ i, ‖v i‖ ^ 2 ≤ κ ^ 2)
    (y ε : Fin n → ℝ) (f : E) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    S (empiricalSpectralEstimator hn v κ hv (fun i => y i + ε i) φ hlam h) - f =
      (S (empiricalSpectralEstimator hn v κ hv y φ hlam h) - f) +
        ∑ i, ε i • empiricalPredictionCoefficient S hn v κ hv φ hlam h i := by
  rw [empiricalSpectralEstimator_prediction_sum, empiricalSpectralEstimator_prediction_sum]
  simp only [add_smul, Finset.sum_add_distrib]
  abel

/-- Uniform finite-sample prediction-coefficient bound for the true filter. -/
theorem empiricalPredictionCoefficient_norm_le (S : H →L[ℝ] E) {n : ℕ} (hn : 0 < n)
    (v : Fin n → H) (κ : ℝ) (hκ : 0 ≤ κ) (hS : ‖S‖ ≤ κ)
    (hv : ∀ i, ‖v i‖ ≤ κ) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) :
    ‖empiricalPredictionCoefficient S hn v κ
      (fun j => pow_le_pow_left₀ (norm_nonneg _) (hv j) 2) φ hlam h i‖ ≤
      A * κ ^ 2 / ((n : ℝ) * lam) := by
  let hv2 : ∀ j, ‖v j‖ ^ 2 ≤ κ ^ 2 := fun j => pow_le_pow_left₀ (norm_nonneg _) (hv j) 2
  let F := empiricalFilterOperator hn v κ hv2 φ hlam h
  have hA := h.constant_nonneg hlam (sq_nonneg κ)
  have hF : ‖F (v i)‖ ≤ (A / lam) * ‖v i‖ :=
    F.le_of_opNorm_le (empiricalFilterOperator_norm_le hn v κ hv2 φ hlam h) _
  have hpred : ‖S (F (v i))‖ ≤ κ * ((A / lam) * κ) := by
    calc
      _ ≤ ‖S‖ * ‖F (v i)‖ := S.le_opNorm _
      _ ≤ κ * ((A / lam) * κ) := by
        gcongr
        exact hF.trans (mul_le_mul_of_nonneg_left (hv i) (div_nonneg hA hlam.le))
  change ‖(n : ℝ)⁻¹ • S (F (v i))‖ ≤ _
  calc
    _ = (n : ℝ)⁻¹ * ‖S (F (v i))‖ := by simp [norm_smul]
    _ ≤ (n : ℝ)⁻¹ * (κ * ((A / lam) * κ)) :=
      mul_le_mul_of_nonneg_left hpred (by positivity)
    _ = _ := by ring

/-- The coefficient bound specialized to the actual L² feature embedding. -/
theorem empiricalFeaturePredictionCoefficient_norm_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (k : X → H) (hk : MemLp k 2 μ) {n : ℕ} (hn : 0 < n) (x : Fin n → X)
    (κ : ℝ) (hκ : 0 ≤ κ) (hkbound : ∀ z, ‖k z‖ ≤ κ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) :
    ‖empiricalPredictionCoefficient (featureEmbedding μ k hk) hn (fun j => k (x j)) κ
      (fun j => pow_le_pow_left₀ (norm_nonneg _) (hkbound (x j)) 2) φ hlam h i‖ ≤
      A * κ ^ 2 / ((n : ℝ) * lam) :=
  empiricalPredictionCoefficient_norm_le _ hn _ κ hκ
    (featureEmbedding_norm_le μ k hk κ hκ (Filter.Eventually.of_forall hkbound))
    (fun j => hkbound (x j)) φ hlam h i

section Measurability

variable {Ω X : Type*} {m : MeasurableSpace Ω} [MeasurableSpace X]

omit [CompleteSpace H] in
/-- Empirical covariance is strongly measurable in operator norm from strongly
measurable sampled features, with no separability of the full operator space. -/
theorem stronglyMeasurable_empiricalCovariance {n : ℕ} (v : Fin n → Ω → H)
    (hv : ∀ i, StronglyMeasurable (v i)) :
    StronglyMeasurable (fun ω => empiricalCovariance (fun i => v i ω)) := by
  have hr (i : Fin n) : StronglyMeasurable (fun ω => rankOne ℝ (v i ω) (v i ω)) :=
    ((rankOne ℝ).continuous.clm_apply continuous_id).comp_stronglyMeasurable (hv i)
  convert (Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ => hr i)).const_smul (n : ℝ)⁻¹ using 1
  rfl

omit [CompleteSpace H] in
theorem stronglyMeasurable_empiricalRepresenter {n : ℕ} (v : Fin n → Ω → H)
    (hv : ∀ i, StronglyMeasurable (v i)) (y : Fin n → Ω → ℝ)
    (hy : ∀ i, StronglyMeasurable (y i)) :
    StronglyMeasurable (fun ω => empiricalRepresenter (fun i => v i ω) (fun i => y i ω)) := by
  convert (Finset.stronglyMeasurable_fun_sum Finset.univ
    (fun i _ => (hy i).smul (hv i))).const_smul (n : ℝ)⁻¹ using 1
  rfl

/-- The actual normalized finite Gram matrix. -/
noncomputable def empiricalGram {n : ℕ} (v : Fin n → H) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (n : ℝ)⁻¹ * inner ℝ (v i) (v j)

omit [CompleteSpace H] in
theorem measurable_empiricalGram {n : ℕ} (v : Fin n → Ω → H)
    (hv : ∀ i, StronglyMeasurable (v i)) :
    Measurable (fun ω (i j : Fin n) => empiricalGram (fun k => v k ω) i j) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact ((hv i).inner (𝕜 := ℝ) (hv j)).measurable.const_mul (n : ℝ)⁻¹

omit [CompleteSpace H] in
/-- Symmetry of the actual Gram entries. -/
theorem empiricalGram_symmetric {n : ℕ} (v : Fin n → H) (i j : Fin n) :
    empiricalGram v i j = empiricalGram v j i := by
  unfold empiricalGram
  congr 1
  exact real_inner_comm (v j) (v i)

omit [CompleteSpace H] in
/-- The finite-Gram reduction `T_X K = K G`, written without any assumptions
about a choice of eigenvectors or continuity of the spectral profile. -/
theorem empiricalCovariance_synthesis_eq_gram {n : ℕ} (v : Fin n → H) (c : Fin n → ℝ) :
    empiricalCovariance v (∑ j, c j • v j) =
      ∑ i, (∑ j, empiricalGram v i j * c j) • v i := by
  rw [empiricalCovariance_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum, smul_smul]
  simp only [inner_smul_right, empiricalGram, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Samples are measurable for the sigma-algebra generated by all design
coordinates by definition, without any standard-Borel assumption on `X`. -/
theorem observation_feature_design_stronglyMeasurable {n : ℕ}
    (Z : Fin n → Ω → X × ℝ) (k : X → H) (hk : StronglyMeasurable k) (i : Fin n) :
    StronglyMeasurable[⨆ j, observationDesignSigma (Z j)]
      (fun ω => k ((Z i ω).1)) := by
  exact hk.comp_measurable (Measurable.of_comap_le (le_iSup (fun j => observationDesignSigma (Z j)) i))

omit [CompleteSpace H] in
theorem observation_empiricalCovariance_design_stronglyMeasurable {n : ℕ}
    (Z : Fin n → Ω → X × ℝ) (k : X → H) (hk : StronglyMeasurable k) :
    StronglyMeasurable[⨆ j, observationDesignSigma (Z j)]
      (fun ω => empiricalCovariance (fun i => k ((Z i ω).1))) :=
  stronglyMeasurable_empiricalCovariance _ (observation_feature_design_stronglyMeasurable Z k hk)

omit [CompleteSpace H] in
theorem observation_meanRepresenter_design_stronglyMeasurable {n : ℕ}
    (Z : Fin n → Ω → X × ℝ) (k : X → H) (hk : StronglyMeasurable k)
    (f : X → ℝ) (hf : Measurable f) :
    StronglyMeasurable[⨆ j, observationDesignSigma (Z j)]
      (fun ω => empiricalRepresenter (fun i => k ((Z i ω).1)) (fun i => f ((Z i ω).1))) := by
  apply stronglyMeasurable_empiricalRepresenter _ (observation_feature_design_stronglyMeasurable Z k hk)
  intro i
  exact (hf.comp (Measurable.of_comap_le (le_iSup (fun j => observationDesignSigma (Z j)) i))).stronglyMeasurable

end Measurability

end KernelSeq
