import KernelSeq.EffectiveDimension
import KernelSeq.SpectralEnergy

/-!
# The actual filter variance dimension

For the main filter, `Nq = ∑ tᵢ² φ(tᵢ)²` is a genuinely summable series on the
actual covariance eigenbasis. Finiteness follows from the proved covariance
trace and the filter size bound. The comparison in the source is
`Nq ≤ A² ∑ (tᵢ/(tᵢ+λ))² ≤ A² ‖R T R‖ N1 ≤ A² N1`,
not an unscaled `Nq ≤ N1`.
No reverse comparison or unconditional strict positivity is asserted.

The bounded operator `q(T)` is also constructed, with exact coefficient energy
and column-square-sum identities. No abstract Hilbert--Schmidt certificate,
finite-dimensional ambient space, or separability of `L²(μ)` is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelSeq
namespace ResidualFilter

/-- The regularized inverse bound gives the exact scalar shrinkage comparison. -/
theorem Contract.shrinkage_abs_le {lam M ρ A t : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |shrinkage φ t| ≤ A * (t / (t + lam)) := by
  have hden : 0 < t + lam := add_pos_of_nonneg_of_pos ht.1 hlam
  have hφ : |φ t| ≤ A / (t + lam) := by
    apply (le_div_iff₀ hden).mpr
    simpa only [abs_mul, abs_of_pos hden, mul_comm] using (h.spectral_size hlam ht).1
  rw [shrinkage, abs_mul, abs_of_nonneg ht.1]
  calc
    _ ≤ t * (A / (t + lam)) := mul_le_mul_of_nonneg_left hφ ht.1
    _ = _ := by ring

/-- The square-weight comparison used for the source variance dimension. -/
theorem Contract.shrinkage_sq_le_regularized_sq {lam M ρ A t : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M) :
    shrinkage φ t ^ 2 ≤ A ^ 2 * (t / (t + lam)) ^ 2 := by
  simpa only [sq_abs, mul_pow] using
    pow_le_pow_left₀ (abs_nonneg (shrinkage φ t)) (h.shrinkage_abs_le hlam ht) 2

/-- A positive regularized scalar weight lies in `[0,1]`. -/
theorem regularized_weight_mem {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    t / (t + lam) ∈ Set.Icc (0 : ℝ) 1 := by
  have hden : 0 < t + lam := add_pos_of_nonneg_of_pos ht hlam
  exact ⟨div_nonneg ht hden.le, (div_le_one hden).mpr (by linarith)⟩

theorem Contract.shrinkage_sq_le_regularized {lam M ρ A t : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M) :
    shrinkage φ t ^ 2 ≤ A ^ 2 * (t / (t + lam)) := by
  have hw := regularized_weight_mem hlam ht.1
  exact (h.shrinkage_sq_le_regularized_sq hlam ht).trans
    (mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)] :
        (t / (t + lam)) ^ 2 ≤ t / (t + lam))
      (sq_nonneg A))

/-- Finiteness can already be derived by domination by the covariance trace,
using `q² ≤ q` and the proved bound `φ ≤ A/λ`. -/
theorem Contract.shrinkage_sq_le_trace_weight {lam M ρ A t : ℝ} {φ : ℝ → ℝ}
    (hf : SpectralFilter M φ) (h : Contract lam M ρ A φ) (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M) :
    shrinkage φ t ^ 2 ≤ (A / lam) * t := by
  have hq := hf.shrinkage_mem t ht
  calc
    _ ≤ shrinkage φ t := by nlinarith [hq.1, hq.2]
    _ = t * φ t := rfl
    _ ≤ t * (A / lam) := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (h.profile_bound hlam ht)) ht.1
    _ = _ := mul_comm _ _

end ResidualFilter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual bounded shrinkage operator for a positive compact operator. -/
noncomputable def compactShrinkageOperator (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ) {M : ℝ}
    (hM : ‖T‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ) : H →L[ℝ] H :=
  compactSpectralMultiplier T hc hp (ResidualFilter.shrinkage φ) 1 zero_le_one
    (fun t ht => by
      have hq := hf.shrinkage_mem t ⟨ht.1, ht.2.trans hM⟩
      simpa only [abs_of_nonneg hq.1] using hq.2)

theorem compactShrinkageOperator_eigenbasis (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ) {M : ℝ}
    (hM : ‖T‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ)
    (i : CompactSpectralIndex T) :
    compactShrinkageOperator T hc hp φ hM hf (compactEigenbasis T hc hp.isSymmetric i) =
      ResidualFilter.shrinkage φ i.1 • compactEigenbasis T hc hp.isSymmetric i :=
  compactSpectralMultiplier_eigen T hc hp _ _ _ _ (compactEigenbasis_eigen T hc hp.isSymmetric i)

/-- The constructed `q(T)` really is `T φ(T)`. -/
theorem compactShrinkageOperator_eq_mul_filter (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    compactShrinkageOperator T hc hp φ hM hf = T * compactFilterOperator T hc hp φ hlam hM h := by
  apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
  intro i
  have he := compactEigenbasis_eigen T hc hp.isSymmetric i
  have hF := compactSpectralMultiplier_eigen T hc hp φ _
    (div_nonneg (h.constant_nonneg hlam ((norm_nonneg T).trans hM)) hlam.le)
    (fun t ht => h.profile_bound hlam ⟨ht.1, ht.2.trans hM⟩) he
  change compactShrinkageOperator T hc hp φ hM hf _ = T (compactFilterOperator T hc hp φ hlam hM h _)
  rw [compactShrinkageOperator_eigenbasis, show compactFilterOperator T hc hp φ hlam hM h
      (compactEigenbasis T hc hp.isSymmetric i) = φ i.1 • compactEigenbasis T hc hp.isSymmetric i
      from hF, map_smul, he, smul_smul]
  simp only [ResidualFilter.shrinkage, mul_comm]

/-- Actual Hilbert norm energy of the shrinkage operator. -/
theorem compactShrinkageOperator_norm_sq_eq_tsum (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ) {M : ℝ}
    (hM : ‖T‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ) (f : H) :
    ‖compactShrinkageOperator T hc hp φ hM hf f‖ ^ 2 =
      ∑' i : CompactSpectralIndex T, ResidualFilter.shrinkage φ i.1 ^ 2 *
        (compactEigenbasis T hc hp.isSymmetric).repr f i ^ 2 :=
  compactSpectralMultiplier_norm_sq_eq_tsum T hc hp _ _ _ _ f

/-- The coefficient energy series converges; its sum is an actual norm. -/
theorem summable_compactShrinkageOperator_energy (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ) {M : ℝ}
    (hM : ‖T‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ) (f : H) :
    Summable (fun i : CompactSpectralIndex T => ResidualFilter.shrinkage φ i.1 ^ 2 *
      (compactEigenbasis T hc hp.isSymmetric).repr f i ^ 2) := by
  have hs := hilbertBasis_coefficients_sq_summable (compactEigenbasis T hc hp.isSymmetric)
    (compactShrinkageOperator T hc hp φ hM hf f)
  simpa only [compactShrinkageOperator, compactSpectralMultiplier_repr, mul_pow] using hs

theorem compactShrinkageOperator_basis_norm_sq (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ) {M : ℝ}
    (hM : ‖T‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ)
    (i : CompactSpectralIndex T) :
    ‖compactShrinkageOperator T hc hp φ hM hf (compactEigenbasis T hc hp.isSymmetric i)‖ ^ 2 =
      ResidualFilter.shrinkage φ i.1 ^ 2 := by
  rw [compactShrinkageOperator_eigenbasis, norm_smul,
    (compactEigenbasis T hc hp.isSymmetric).orthonormal.norm_eq_one, mul_one]
  simp

/-- Exact inverse-root action on every constructed covariance eigenvector. -/
theorem compactRegularizedInvSqrt_eigenbasis (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (i : CompactSpectralIndex T) :
    compactRegularizedInvSqrt T hc hp lam (compactEigenbasis T hc hp.isSymmetric i) =
      (Real.sqrt (i.1 + lam))⁻¹ • compactEigenbasis T hc hp.isSymmetric i := by
  classical
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext j
  rw [compactRegularizedInvSqrt_repr T hc hp lam hlam]
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    HilbertBasis.repr_self, lp.single_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- The source's actual normalized population covariance, not a chosen
spectral-envelope constant. -/
noncomputable def compactNormalizedCovariance (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (lam : ℝ) : H →L[ℝ] H :=
  compactRegularizedInvSqrt T hc hp lam * T * compactRegularizedInvSqrt T hc hp lam

theorem compactNormalizedCovariance_eigenbasis (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (i : CompactSpectralIndex T) :
    compactNormalizedCovariance T hc hp lam (compactEigenbasis T hc hp.isSymmetric i) =
      (i.1 / (i.1 + lam)) • compactEigenbasis T hc hp.isSymmetric i := by
  change compactRegularizedInvSqrt T hc hp lam
    (T (compactRegularizedInvSqrt T hc hp lam (compactEigenbasis T hc hp.isSymmetric i))) = _
  rw [compactRegularizedInvSqrt_eigenbasis T hc hp lam hlam, map_smul,
    compactEigenbasis_eigen, map_smul, map_smul,
    compactRegularizedInvSqrt_eigenbasis T hc hp lam hlam, smul_smul, smul_smul]
  congr 1
  have hs : (Real.sqrt (i.1 + lam))⁻¹ ^ 2 = (i.1 + lam)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (add_nonneg (compactEigenvalue_nonneg T hc hp i) hlam.le)]
  calc
    _ = i.1 * (Real.sqrt (i.1 + lam))⁻¹ ^ 2 := by ring
    _ = _ := by rw [hs]; rfl

/-- Every regularized eigenvalue is bounded by the actual normalized covariance
operator norm `varrho` used in the source concentration argument. -/
theorem compactNormalizedCovariance_weight_le_norm (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (i : CompactSpectralIndex T) :
    i.1 / (i.1 + lam) ≤ ‖compactNormalizedCovariance T hc hp lam‖ := by
  have hb := (compactNormalizedCovariance T hc hp lam).le_opNorm
    (compactEigenbasis T hc hp.isSymmetric i)
  have hw := ResidualFilter.regularized_weight_mem hlam (compactEigenvalue_nonneg T hc hp i)
  simpa only [compactNormalizedCovariance_eigenbasis T hc hp lam hlam, norm_smul,
    (compactEigenbasis T hc hp.isSymmetric).orthonormal.norm_eq_one, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hw.1] using hb

/-- The source normalized covariance is an actual contraction. -/
theorem compactNormalizedCovariance_norm_le_one (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    ‖compactNormalizedCovariance T hc hp lam‖ ≤ 1 := by
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |t / (t + lam)| ≤ 1 := by
    intro t ht
    have hw := ResidualFilter.regularized_weight_mem hlam ht.1
    simpa only [abs_of_nonneg hw.1] using hw.2
  have heq : compactNormalizedCovariance T hc hp lam =
      compactSpectralMultiplier T hc hp (fun t => t / (t + lam)) 1 zero_le_one hφ := by
    apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
    intro i
    rw [compactNormalizedCovariance_eigenbasis T hc hp lam hlam]
    exact (compactSpectralMultiplier_eigen T hc hp _ _ _ hφ
      (compactEigenbasis_eigen T hc hp.isSymmetric i)).symm
  rw [heq]
  exact compactSpectralMultiplier_norm_le T hc hp _ _ _ hφ

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem featureCovarianceEigenvalue_mem (k : X → H) (hk : MemLp k 2 μ)
    {M : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (i : FeatureCovarianceIndex k hk) : i.1 ∈ Set.Icc (0 : ℝ) M :=
  ⟨compactEigenvalue_nonneg _ (populationCovariance_feature_isCompact μ k hk)
      (populationCovariance_isPositive (featureEmbedding μ k hk)) i,
    ((le_abs_self i.1).trans (compactEigenvalue_norm_le _
      (populationCovariance_feature_isCompact μ k hk)
      (populationCovariance_isPositive (featureEmbedding μ k hk)).isSymmetric i)).trans hM⟩

variable [TopologicalSpace.SeparableSpace H]

/-- The actual population variance dimension `Nq`; zero is permitted. -/
noncomputable def featureFilterDimension (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) : ℝ :=
  ∑' i : FeatureCovarianceIndex k hk, ResidualFilter.shrinkage φ i.1 ^ 2

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem featureFilterDimension_eq_tsum (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) :
    featureFilterDimension k hk φ =
      ∑' i : FeatureCovarianceIndex k hk, i.1 ^ 2 * φ i.1 ^ 2 := by
  simp only [featureFilterDimension, ResidualFilter.shrinkage, mul_pow]

/-- The filter variance series is summable by direct domination by the actual
summable covariance eigenvalues. -/
theorem summable_featureFilterDimension (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    Summable (fun i : FeatureCovarianceIndex k hk => ResidualFilter.shrinkage φ i.1 ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    ((summable_featureCovarianceEigenvalues k hk).mul_left (A / lam))
  intro i
  exact h.shrinkage_sq_le_trace_weight hf hlam (featureCovarianceEigenvalue_mem k hk hM i)

theorem featureFilterDimension_le_trace (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    featureFilterDimension k hk φ ≤ (A / lam) * featureCovarianceTrace k hk := by
  rw [featureFilterDimension, featureCovarianceTrace, ← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun i => h.shrinkage_sq_le_trace_weight hf hlam (featureCovarianceEigenvalue_mem k hk hM i))
    (summable_featureFilterDimension k hk φ hlam hM hf h)
    ((summable_featureCovarianceEigenvalues k hk).mul_left _)

/-- The ridge squared-weight dimension appearing in the source comparison. -/
noncomputable def featureSquaredEffectiveDimension (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) : ℝ :=
  ∑' i : FeatureCovarianceIndex k hk, (i.1 / (i.1 + lam)) ^ 2

theorem summable_featureSquaredEffectiveDimension (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    Summable (fun i : FeatureCovarianceIndex k hk => (i.1 / (i.1 + lam)) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    (summable_featureEffectiveDimension k hk lam hlam)
  intro i
  have hw := ResidualFilter.regularized_weight_mem hlam
    (featureCovarianceEigenvalue_mem k hk (le_refl _) i).1
  nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]

theorem featureSquaredEffectiveDimension_le (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    featureSquaredEffectiveDimension k hk lam ≤ featureEffectiveDimension k hk lam := by
  apply Summable.tsum_le_tsum _
    (summable_featureSquaredEffectiveDimension k hk lam hlam)
    (summable_featureEffectiveDimension k hk lam hlam)
  intro i
  have hw := ResidualFilter.regularized_weight_mem hlam
    (featureCovarianceEigenvalue_mem k hk (le_refl _) i).1
  nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]

/-- The first exact source comparison, with the common inverse-size constant. -/
theorem featureFilterDimension_le_squaredEffectiveDimension (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    featureFilterDimension k hk φ ≤ A ^ 2 * featureSquaredEffectiveDimension k hk lam := by
  rw [featureFilterDimension, featureSquaredEffectiveDimension, ← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun i => h.shrinkage_sq_le_regularized_sq hlam (featureCovarianceEigenvalue_mem k hk hM i))
    (summable_featureFilterDimension k hk φ hlam hM hf h)
    ((summable_featureSquaredEffectiveDimension k hk lam hlam).mul_left _)

theorem featureFilterDimension_le_effectiveDimension (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    featureFilterDimension k hk φ ≤ A ^ 2 * featureEffectiveDimension k hk lam :=
  (featureFilterDimension_le_squaredEffectiveDimension k hk φ hlam hM hf h).trans
    (mul_le_mul_of_nonneg_left (featureSquaredEffectiveDimension_le k hk lam hlam) (sq_nonneg A))

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem featureFilterDimension_nonneg (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) :
    0 ≤ featureFilterDimension k hk φ := tsum_nonneg (fun _ => sq_nonneg _)

/-- Positivity needs a genuinely retained eigendirection; it is not a consequence
of mere admissibility and finiteness. -/
theorem featureFilterDimension_pos_iff (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    0 < featureFilterDimension k hk φ ↔
      ∃ i : FeatureCovarianceIndex k hk, ResidualFilter.shrinkage φ i.1 ≠ 0 := by
  classical
  constructor
  · intro hpos
    by_contra hex
    have hz : ∀ i : FeatureCovarianceIndex k hk, ResidualFilter.shrinkage φ i.1 = 0 := by
      simpa only [not_exists, not_not] using hex
    simp only [featureFilterDimension, hz, zero_pow (by decide : 2 ≠ 0), tsum_zero] at hpos
    exact (lt_irrefl 0) hpos
  · rintro ⟨i, hi⟩
    exact (summable_featureFilterDimension k hk φ hlam hM hf h).tsum_pos
      (fun _ => sq_nonneg _) i (sq_pos_of_ne_zero hi)

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem featureFilterDimension_zero_filter (k : X → H) (hk : MemLp k 2 μ) :
    featureFilterDimension k hk (fun _ => 0) = 0 := by
  simp [featureFilterDimension, ResidualFilter.shrinkage]

/-- The actual shrinkage operator has square-summable basis columns, derived
from the true filter dimension rather than assumed as a Hilbert--Schmidt field. -/
theorem hasSum_compactShrinkageOperator_columns (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    HasSum (fun i : FeatureCovarianceIndex k hk =>
      ‖compactShrinkageOperator (populationCovariance (featureEmbedding μ k hk))
        (populationCovariance_feature_isCompact μ k hk)
        (populationCovariance_isPositive (featureEmbedding μ k hk)) φ hM hf
        (featureCovarianceBasis k hk i)‖ ^ 2)
      (featureFilterDimension k hk φ) := by
  have hs := (summable_featureFilterDimension k hk φ hlam hM hf h).hasSum
  simpa only [featureFilterDimension, featureCovarianceBasis, compactShrinkageOperator_basis_norm_sq] using hs

/-- The actual `varrho` in the source, defined as `‖R T R‖`. -/
noncomputable def featureCovarianceRetention (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) : ℝ :=
  ‖compactNormalizedCovariance (populationCovariance (featureEmbedding μ k hk))
    (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)) lam‖

omit [TopologicalSpace.SeparableSpace H] in
theorem featureCovarianceRetention_eq_norm (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    featureCovarianceRetention k hk lam =
      ‖featureRegularizedInvSqrt μ k hk lam * populationCovariance (featureEmbedding μ k hk) *
        featureRegularizedInvSqrt μ k hk lam‖ := rfl

omit [TopologicalSpace.SeparableSpace H] in
theorem featureCovarianceRetention_nonneg (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    0 ≤ featureCovarianceRetention k hk lam := norm_nonneg _

omit [TopologicalSpace.SeparableSpace H] in
theorem featureCovarianceRetention_le_one (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) : featureCovarianceRetention k hk lam ≤ 1 :=
  compactNormalizedCovariance_norm_le_one _ _ _ lam hlam

/-- The precise intrinsic-dimension comparison uses the actual operator norm,
not an assumed maximal-eigenvalue formula. -/
theorem featureSquaredEffectiveDimension_le_retention (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    featureSquaredEffectiveDimension k hk lam ≤
      featureCovarianceRetention k hk lam * featureEffectiveDimension k hk lam := by
  rw [featureSquaredEffectiveDimension, featureEffectiveDimension, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    (summable_featureSquaredEffectiveDimension k hk lam hlam)
    ((summable_featureEffectiveDimension k hk lam hlam).mul_left _)
  intro i
  have hw := compactNormalizedCovariance_weight_le_norm
    (populationCovariance (featureEmbedding μ k hk))
    (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)) lam hlam i
  have hnonneg := (ResidualFilter.regularized_weight_mem hlam
    (featureCovarianceEigenvalue_mem k hk (le_refl _) i).1).1
  simpa only [featureCovarianceRetention, pow_two] using
    mul_le_mul_of_nonneg_right hw hnonneg

/-- Exactly `Q ≤ A² varrho N` from the source concentration reduction. -/
theorem featureFilterDimension_le_retention (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    featureFilterDimension k hk φ ≤
      A ^ 2 * featureCovarianceRetention k hk lam * featureEffectiveDimension k hk lam := by
  calc
    _ ≤ A ^ 2 * featureSquaredEffectiveDimension k hk lam :=
      featureFilterDimension_le_squaredEffectiveDimension k hk φ hlam hM hf h
    _ ≤ A ^ 2 * (featureCovarianceRetention k hk lam * featureEffectiveDimension k hk lam) :=
      mul_le_mul_of_nonneg_left (featureSquaredEffectiveDimension_le_retention k hk lam hlam)
        (sq_nonneg A)
    _ = _ := by ring

/-- The source's eventual positivity assumption for `Q` really forces positive
`varrho`; no converse and no unconditional positivity is claimed. -/
theorem featureCovarianceRetention_pos_of_filterDimension_pos
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hpos : 0 < featureFilterDimension k hk φ) :
    0 < featureCovarianceRetention k hk lam := by
  by_contra hnot
  have hz : featureCovarianceRetention k hk lam = 0 :=
    le_antisymm (not_lt.mp hnot) (featureCovarianceRetention_nonneg k hk lam)
  have hb := featureFilterDimension_le_retention k hk φ hlam hM hf h
  rw [hz, mul_zero, zero_mul] at hb
  exact (not_le_of_gt hpos) hb

end KernelSeq
