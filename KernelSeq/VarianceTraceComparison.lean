import KernelSeq.HilbertSchmidtIdeal
import KernelSeq.EmpiricalVariance
import KernelSeq.FilterDimension

/-!
# The actual variance trace perturbation

The population covariance is `S* S`. Relative quadratic-form comparison with
its constructed real inverse root is summed over actual square-summable
columns to obtain the trace perturbation bound for variance transfer.
The empirical specialization uses the actual finite-sample covariance and its
constructed square root. No trace-bound or Hilbert--Schmidt existence
certificate is assumed, and no finite-dimensional ambient replacement is used.
-/

open scoped BigOperators

namespace KernelSeq

variable {H E ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual nonnegative square root acts with the true norm quadratic form. -/
theorem compactSqrt_norm_sq (T : H →L[ℝ] H) (hc : IsCompactOperator T) (hp : T.IsPositive)
    (v : H) : ‖compactRegularizedSqrt T hc hp 0 v‖ ^ 2 = inner ℝ v (T v) := by
  rw [(compactRegularizedSqrt T hc hp 0).apply_norm_sq_eq_inner_adjoint_right]
  change inner ℝ v ((compactRegularizedSqrt T hc hp 0).adjoint
    (compactRegularizedSqrt T hc hp 0 v)) = _
  rw [(compactRegularizedSqrt_isSelfAdjoint T hc hp 0).adjoint_eq]
  change inner ℝ v ((compactRegularizedSqrt T hc hp 0 * compactRegularizedSqrt T hc hp 0) v) = _
  rw [compactRegularizedSqrt_sq T hc hp 0 le_rfl]
  simp

/-- The actual normalized covariance deviation, with `T = S* S`. -/
noncomputable def covarianceRelativeDeviation (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (TX : H →L[ℝ] H) (lam : ℝ) : ℝ :=
  ‖compactRegularizedInvSqrt (S.adjoint.comp S) hc (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam *
    (TX - S.adjoint.comp S) *
    compactRegularizedInvSqrt (S.adjoint.comp S) hc (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam‖

/-- Actual norm energies satisfy the relative covariance quadratic bound. -/
theorem covariance_energy_abs_sub_le (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (TX : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hpX : TX.IsPositive)
    (lam : ℝ) (hlam : 0 < lam) (v : H) :
    |‖S v‖ ^ 2 - ‖compactRegularizedSqrt TX hcX hpX 0 v‖ ^ 2| ≤
      covarianceRelativeDeviation S hc TX lam * (‖S v‖ ^ 2 + lam * ‖v‖ ^ 2) := by
  have h := compact_regularized_relative_comparison_real (S.adjoint.comp S) TX hc
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam hlam v
  dsimp only at h
  have hd : TX + lam • (1 : H →L[ℝ] H) - (S.adjoint.comp S + lam • 1) =
      TX - S.adjoint.comp S := by abel
  rw [hd] at h
  have hpop : inner ℝ v (S.adjoint.comp S v) = ‖S v‖ ^ 2 := by
    simpa only [RCLike.re_to_real] using
      (S.apply_norm_sq_eq_inner_adjoint_right v).symm
  have hpa : inner ℝ v ((S.adjoint.comp S + lam • (1 : H →L[ℝ] H)) v) =
      ‖S v‖ ^ 2 + lam * ‖v‖ ^ 2 := by
    change inner ℝ v (S.adjoint.comp S v + lam • v) = _
    rw [inner_add_right, inner_smul_right, hpop, real_inner_self_eq_norm_sq]
  have hpx : inner ℝ v ((TX + lam • (1 : H →L[ℝ] H)) v) =
      ‖compactRegularizedSqrt TX hcX hpX 0 v‖ ^ 2 + lam * ‖v‖ ^ 2 := by
    change inner ℝ v (TX v + lam • v) = _
    rw [inner_add_right, inner_smul_right, ← compactSqrt_norm_sq TX hcX hpX v,
      real_inner_self_eq_norm_sq]
  rw [hpa, hpx] at h
  change (1 - covarianceRelativeDeviation S hc TX lam) *
      (‖S v‖ ^ 2 + lam * ‖v‖ ^ 2) ≤
      ‖compactRegularizedSqrt TX hcX hpX 0 v‖ ^ 2 + lam * ‖v‖ ^ 2 ∧
    ‖compactRegularizedSqrt TX hcX hpX 0 v‖ ^ 2 + lam * ‖v‖ ^ 2 ≤
      (1 + covarianceRelativeDeviation S hc TX lam) *
        (‖S v‖ ^ 2 + lam * ‖v‖ ^ 2) at h
  exact abs_le.mpr ⟨by nlinarith [h.2], by nlinarith [h.1]⟩

/-- The real trace perturbation inequality for actual Hilbert--Schmidt columns.
All series convergence follows from the column space and bounded composition. -/
theorem hs_covariance_energy_abs_sub_le (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (TX : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hpX : TX.IsPositive)
    (lam : ℝ) (hlam : 0 < lam) (c : HilbertSchmidtColumns ι H) :
    |‖hsLeftComposition S c‖ ^ 2 -
      ‖hsLeftComposition (compactRegularizedSqrt TX hcX hpX 0) c‖ ^ 2| ≤
      covarianceRelativeDeviation S hc TX lam *
        (‖hsLeftComposition S c‖ ^ 2 + lam * ‖c‖ ^ 2) := by
  let f := fun i => ‖S (c i)‖ ^ 2
  let g := fun i => ‖compactRegularizedSqrt TX hcX hpX 0 (c i)‖ ^ 2
  let u := fun i => ‖c i‖ ^ 2
  let δ := covarianceRelativeDeviation S hc TX lam
  have hf : Summable f := by
    simpa only [hsLeftComposition_apply] using hsColumns_sq_summable (hsLeftComposition S c)
  have hg : Summable g := by
    simpa only [hsLeftComposition_apply] using
      hsColumns_sq_summable (hsLeftComposition (compactRegularizedSqrt TX hcX hpX 0) c)
  have hu : Summable u := hsColumns_sq_summable c
  have hb : Summable (fun i => δ * (f i + lam * u i)) := (hf.add (hu.mul_left lam)).mul_left δ
  have hp (i : ι) : |f i - g i| ≤ δ * (f i + lam * u i) :=
    covariance_energy_abs_sub_le S hc TX hcX hpX lam hlam (c i)
  have h₁ := Summable.tsum_le_tsum (fun i => (le_abs_self (f i - g i)).trans (hp i))
    (hf.sub hg) hb
  have h₂ := Summable.tsum_le_tsum (fun i => (neg_le_abs (f i - g i)).trans (hp i))
    ((hf.sub hg).neg) hb
  rw [hf.tsum_sub hg, tsum_mul_left, hf.tsum_add (hu.mul_left lam), tsum_mul_left] at h₁
  rw [tsum_neg, hf.tsum_sub hg, tsum_mul_left, hf.tsum_add (hu.mul_left lam), tsum_mul_left] at h₂
  have hfsum : (∑' i, f i) = ‖hsLeftComposition S c‖ ^ 2 := by
    simpa only [hsLeftComposition_apply] using (hsColumns_norm_sq (hsLeftComposition S c)).symm
  have hgsum : (∑' i, g i) = ‖hsLeftComposition (compactRegularizedSqrt TX hcX hpX 0) c‖ ^ 2 := by
    simpa only [hsLeftComposition_apply] using
      (hsColumns_norm_sq (hsLeftComposition (compactRegularizedSqrt TX hcX hpX 0) c)).symm
  have husum : (∑' i, u i) = ‖c‖ ^ 2 := (hsColumns_norm_sq c).symm
  rw [hfsum, hgsum, husum] at h₁ h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

/-- Square-root spectral action, including every vector in the zero eigenspace. -/
theorem compactRegularizedSqrt_eigenbasis (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (lam : ℝ) (i : CompactSpectralIndex T) :
    compactRegularizedSqrt T hc hp lam (compactEigenbasis T hc hp.isSymmetric i) =
      Real.sqrt (i.1 + lam) • compactEigenbasis T hc hp.isSymmetric i := by
  classical
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext j
  rw [compactRegularizedSqrt_repr]
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    HilbertBasis.repr_self, lp.single_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

theorem compactSqrt_basis_norm_sq (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (i : CompactSpectralIndex T) :
    ‖compactRegularizedSqrt T hc hp 0 (compactEigenbasis T hc hp.isSymmetric i)‖ ^ 2 = i.1 := by
  rw [compactSqrt_norm_sq, compactEigenbasis_eigen, inner_smul_right,
    real_inner_self_eq_norm_sq, (compactEigenbasis T hc hp.isSymmetric).orthonormal.norm_eq_one,
    one_pow, mul_one]

/-- Actual root-filter-root multiplication is shrinkage, proved on the full
spectral basis rather than assumed as an intertwining certificate. -/
theorem compactRoot_filter_root_eq_shrinkage (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    compactRegularizedSqrt T hc hp 0 * compactFilterOperator T hc hp φ hlam hM h *
      compactRegularizedSqrt T hc hp 0 = compactShrinkageOperator T hc hp φ hM hf := by
  apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
  intro i
  have he := compactEigenbasis_eigen T hc hp.isSymmetric i
  have hF := compactSpectralMultiplier_eigen T hc hp φ _
    (div_nonneg (h.constant_nonneg hlam ((norm_nonneg T).trans hM)) hlam.le)
    (fun t ht => h.profile_bound hlam ⟨ht.1, ht.2.trans hM⟩) he
  change compactRegularizedSqrt T hc hp 0 (compactFilterOperator T hc hp φ hlam hM h
    (compactRegularizedSqrt T hc hp 0 (compactEigenbasis T hc hp.isSymmetric i))) = _
  rw [compactRegularizedSqrt_eigenbasis, map_smul,
    show compactFilterOperator T hc hp φ hlam hM h (compactEigenbasis T hc hp.isSymmetric i) =
      φ i.1 • compactEigenbasis T hc hp.isSymmetric i from hF,
    map_smul, map_smul, compactRegularizedSqrt_eigenbasis,
    compactShrinkageOperator_eigenbasis, smul_smul, smul_smul]
  congr 1
  simp only [add_zero, ResidualFilter.shrinkage]
  have hs := Real.sq_sqrt (compactEigenvalue_nonneg T hc hp i)
  calc
    _ = φ i.1 * (Real.sqrt i.1) ^ 2 := by ring
    _ = _ := by rw [hs]; ring

namespace ResidualFilter

/-- The exact scalar comparison for `λ Tr C_X`, with the same inverse-size
constant as the main filter contract. -/
theorem Contract.lambda_mul_inverse_energy_le {lam M ρ A t : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M) :
    lam * (t * φ t ^ 2) ≤ A ^ 2 * (t / (t + lam)) := by
  have hden : 0 < t + lam := add_pos_of_nonneg_of_pos ht.1 hlam
  have hφ : |φ t| ≤ A / (t + lam) := by
    apply (le_div_iff₀ hden).mpr
    simpa only [abs_mul, abs_of_pos hden, mul_comm] using (h.spectral_size hlam ht).1
  have hφsq : φ t ^ 2 ≤ A ^ 2 / (t + lam) ^ 2 := by
    simpa only [sq_abs, div_pow] using pow_le_pow_left₀ (abs_nonneg (φ t)) hφ 2
  have hsmall : lam / (t + lam) ≤ 1 := (div_le_one hden).mpr (by linarith [ht.1])
  calc
    _ ≤ (lam * t) * (A ^ 2 / (t + lam) ^ 2) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hφsq (mul_nonneg hlam.le ht.1)
    _ = (A ^ 2 * (t / (t + lam))) * (lam / (t + lam)) := by
      field_simp [ne_of_gt hden]
    _ ≤ (A ^ 2 * (t / (t + lam))) * 1 :=
      mul_le_mul_of_nonneg_left hsmall (mul_nonneg (sq_nonneg A) (div_nonneg ht.1 hden.le))
    _ = _ := mul_one _

end ResidualFilter

abbrev EmpiricalCovarianceIndex {n : ℕ} (z : Fin n → H) :=
  CompactSpectralIndex (empiricalCovariance z)

noncomputable def empiricalCovarianceBasis {n : ℕ} (z : Fin n → H) :
    HilbertBasis (EmpiricalCovarianceIndex z) ℝ H :=
  compactEigenbasis (empiricalCovariance z) (empiricalCovariance_isCompact z)
    (empiricalCovariance_isPositive z).isSymmetric

/-- Actual empirical eigenvalues are summable, derived from finite-sample root
column energy. No ambient separability or trace-class premise is needed. -/
theorem hasSum_empiricalCovarianceEigenvalues {n : ℕ} (z : Fin n → H) :
    HasSum (fun i : EmpiricalCovarianceIndex z => i.1) ((n : ℝ)⁻¹ * ∑ j, ‖z j‖ ^ 2) := by
  have hc := empiricalVariance_column_energy z (1 : H →L[ℝ] H) (empiricalCovarianceBasis z)
  have ht (i : EmpiricalCovarianceIndex z) :
      ‖empiricalCovarianceSqrt z (empiricalCovarianceBasis z i)‖ ^ 2 = i.1 := by
    exact compactSqrt_basis_norm_sq (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) i
  simp only [one_apply_eq_self, ht] at hc
  have hs := hc.1.hasSum
  rw [hc.2] at hs
  exact hs

/-- The actual empirical regularized effective dimension. -/
noncomputable def empiricalEffectiveDimension {n : ℕ} (z : Fin n → H) (lam : ℝ) : ℝ :=
  ∑' i : EmpiricalCovarianceIndex z, i.1 / (i.1 + lam)

theorem summable_empiricalEffectiveDimension {n : ℕ} (z : Fin n → H)
    (lam : ℝ) (hlam : 0 < lam) :
    Summable (fun i : EmpiricalCovarianceIndex z => i.1 / (i.1 + lam)) := by
  apply Summable.of_nonneg_of_le _ _ ((hasSum_empiricalCovarianceEigenvalues z).summable.div_const lam)
  · intro i
    have ht := compactEigenvalue_nonneg _ (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) i
    exact div_nonneg ht (add_nonneg ht hlam.le)
  · intro i
    have ht := compactEigenvalue_nonneg _ (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) i
    apply (div_le_div_iff₀ (add_pos_of_nonneg_of_pos ht hlam) hlam).mpr
    nlinarith [sq_nonneg i.1]

theorem empiricalCovarianceEigenvalue_mem {n : ℕ} (z : Fin n → H) {M : ℝ}
    (hM : ‖empiricalCovariance z‖ ≤ M) (i : EmpiricalCovarianceIndex z) :
    i.1 ∈ Set.Icc (0 : ℝ) M :=
  ⟨compactEigenvalue_nonneg _ (empiricalCovariance_isCompact z) (empiricalCovariance_isPositive z) i,
    ((le_abs_self i.1).trans (compactEigenvalue_norm_le _ (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z).isSymmetric i)).trans hM⟩

/-- Actual columns of `φ(T_X) T_X^(1/2)`; their square summability comes from
`EmpiricalVariance`, not from a trace-class assumption. -/
noncomputable def empiricalFilteredRootColumns {n : ℕ} (z : Fin n → H) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    HilbertSchmidtColumns (EmpiricalCovarianceIndex z) H :=
  empiricalVarianceColumns z
    (compactFilterOperator (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) φ hlam hM h) (empiricalCovarianceBasis z)

/-- Exact per-column inverse-filter energy. -/
theorem empiricalFilteredRootColumns_energy {n : ℕ} (z : Fin n → H) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) (i : EmpiricalCovarianceIndex z) :
    ‖empiricalFilteredRootColumns z φ hlam hM h i‖ ^ 2 = i.1 * φ i.1 ^ 2 := by
  have he := compactEigenbasis_eigen (empiricalCovariance z) (empiricalCovariance_isCompact z)
    (empiricalCovariance_isPositive z).isSymmetric i
  have hF := compactSpectralMultiplier_eigen (empiricalCovariance z)
    (empiricalCovariance_isCompact z) (empiricalCovariance_isPositive z) φ _
    (div_nonneg (h.constant_nonneg hlam ((norm_nonneg _).trans hM)) hlam.le)
    (fun t ht => h.profile_bound hlam ⟨ht.1, ht.2.trans hM⟩) he
  change ‖compactFilterOperator (empiricalCovariance z) (empiricalCovariance_isCompact z)
    (empiricalCovariance_isPositive z) φ hlam hM h
    (compactRegularizedSqrt (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) 0
      (compactEigenbasis (empiricalCovariance z) (empiricalCovariance_isCompact z)
        (empiricalCovariance_isPositive z).isSymmetric i))‖ ^ 2 = _
  change compactFilterOperator (empiricalCovariance z) (empiricalCovariance_isCompact z)
    (empiricalCovariance_isPositive z) φ hlam hM h
    (compactEigenbasis (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z).isSymmetric i) = _ at hF
  rw [compactRegularizedSqrt_eigenbasis, map_smul, hF]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    (compactEigenbasis (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z).isSymmetric).orthonormal.norm_eq_one,
    mul_one, add_zero,
    Real.sq_sqrt (compactEigenvalue_nonneg _ (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) i)]

/-- `λ Tr C_X ≤ A² Nhat` for actual empirical filtered-root columns. Both
series are already proved summable, and the bound is summed pointwise. -/
theorem lambda_mul_empiricalFilteredRootColumns_norm_sq_le {n : ℕ} (z : Fin n → H)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    lam * ‖empiricalFilteredRootColumns z φ hlam hM h‖ ^ 2 ≤
      A ^ 2 * empiricalEffectiveDimension z lam := by
  rw [hsColumns_norm_sq, empiricalEffectiveDimension, ← tsum_mul_left, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    ((hsColumns_sq_summable (empiricalFilteredRootColumns z φ hlam hM h)).mul_left lam)
    ((summable_empiricalEffectiveDimension z lam hlam).mul_left (A ^ 2))
  intro i
  rw [empiricalFilteredRootColumns_energy]
  exact h.lambda_mul_inverse_energy_le hlam (empiricalCovarianceEigenvalue_mem z hM i)

/-- The prediction columns are precisely those of the actual variance map,
with no cyclic-trace manipulation assumed. -/
theorem empiricalFilteredRootColumns_prediction (S : H →L[ℝ] E) {n : ℕ} (z : Fin n → H)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    hsLeftComposition S (empiricalFilteredRootColumns z φ hlam hM h) =
      empiricalVarianceColumns z (S.comp
        (compactFilterOperator (empiricalCovariance z) (empiricalCovariance_isCompact z)
          (empiricalCovariance_isPositive z) φ hlam hM h)) (empiricalCovarianceBasis z) := by
  ext i
  simp only [hsLeftComposition_apply, empiricalFilteredRootColumns,
    empiricalVarianceColumns_apply, ContinuousLinearMap.comp_apply]

/-- `W_X = Tr q(T_X)²`, defined on the actual complete empirical eigenbasis. -/
noncomputable def empiricalFilterDimension {n : ℕ} (z : Fin n → H) (φ : ℝ → ℝ) : ℝ :=
  ∑' i : EmpiricalCovarianceIndex z, ResidualFilter.shrinkage φ i.1 ^ 2

/-- The actual shrinkage columns reconstruct the actual `q(T_X)` operator. -/
theorem hilbertSchmidtOperator_empiricalShrinkageColumns {n : ℕ} (z : Fin n → H)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    hilbertSchmidtOperator (empiricalCovarianceBasis z)
      (hsLeftComposition (empiricalCovarianceSqrt z) (empiricalFilteredRootColumns z φ hlam hM h)) =
        compactShrinkageOperator (empiricalCovariance z) (empiricalCovariance_isCompact z)
          (empiricalCovariance_isPositive z) φ hM hf := by
  rw [hilbertSchmidtOperator_leftComposition]
  change (empiricalCovarianceSqrt z).comp
    (hilbertSchmidtOperator (empiricalCovarianceBasis z)
      (empiricalVarianceColumns z _ (empiricalCovarianceBasis z))) = _
  rw [hilbertSchmidtOperator_empiricalVarianceColumns]
  change compactRegularizedSqrt (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) 0 *
    (compactFilterOperator (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) φ hlam hM h *
      compactRegularizedSqrt (empiricalCovariance z) (empiricalCovariance_isCompact z)
        (empiricalCovariance_isPositive z) 0) = _
  rw [← mul_assoc]
  exact compactRoot_filter_root_eq_shrinkage (empiricalCovariance z) (empiricalCovariance_isCompact z)
    (empiricalCovariance_isPositive z) φ hlam hM hf h

/-- The square-root-composed inverse-filter column energy is exactly `q²`. -/
theorem empiricalFilteredRootColumns_shrinkage_energy {n : ℕ} (z : Fin n → H)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (i : EmpiricalCovarianceIndex z) :
    ‖empiricalCovarianceSqrt z (empiricalFilteredRootColumns z φ hlam hM h i)‖ ^ 2 =
      ResidualFilter.shrinkage φ i.1 ^ 2 := by
  have heq := hilbertSchmidtOperator_empiricalShrinkageColumns z φ hlam hM hf h
  have hv := congrArg (fun B : H →L[ℝ] H => ‖B (empiricalCovarianceBasis z i)‖ ^ 2) heq
  rw [hilbertSchmidtOperator_basis, hsLeftComposition_apply] at hv
  exact hv.trans (compactShrinkageOperator_basis_norm_sq _ _ _ φ hM hf i)

/-- Finiteness of the actual empirical `q²` series is derived from constructed
Hilbert--Schmidt columns, including the nonseparable-kernel case. -/
theorem summable_empiricalFilterDimension {n : ℕ} (z : Fin n → H) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    Summable (fun i : EmpiricalCovarianceIndex z => ResidualFilter.shrinkage φ i.1 ^ 2) := by
  have hs := hsColumns_sq_summable
    (hsLeftComposition (empiricalCovarianceSqrt z) (empiricalFilteredRootColumns z φ hlam hM h))
  simpa only [hsLeftComposition_apply,
    empiricalFilteredRootColumns_shrinkage_energy z φ hlam hM hf h] using hs

theorem empiricalFilteredRootColumns_shrinkage_norm_sq {n : ℕ} (z : Fin n → H)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    ‖hsLeftComposition (empiricalCovarianceSqrt z) (empiricalFilteredRootColumns z φ hlam hM h)‖ ^ 2 =
      empiricalFilterDimension z φ := by
  rw [hsColumns_norm_sq, empiricalFilterDimension]
  apply tsum_congr
  intro i
  exact empiricalFilteredRootColumns_shrinkage_energy z φ hlam hM hf h i

/-- The source's real trace-perturbation step for the actual empirical filtered
variance. `a`, `W`, `Nhat`, and `δ` are all actual constructed quantities. -/
theorem empirical_variance_trace_abs_sub_le (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) {n : ℕ} (z : Fin n → H) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    |‖hsLeftComposition S (empiricalFilteredRootColumns z φ hlam hM h)‖ ^ 2 -
      empiricalFilterDimension z φ| ≤
      covarianceRelativeDeviation S hc (empiricalCovariance z) lam *
        (‖hsLeftComposition S (empiricalFilteredRootColumns z φ hlam hM h)‖ ^ 2 +
          A ^ 2 * empiricalEffectiveDimension z lam) := by
  have hb := hs_covariance_energy_abs_sub_le S hc (empiricalCovariance z)
    (empiricalCovariance_isCompact z) (empiricalCovariance_isPositive z) lam hlam
    (empiricalFilteredRootColumns z φ hlam hM h)
  change |‖hsLeftComposition S (empiricalFilteredRootColumns z φ hlam hM h)‖ ^ 2 -
      ‖hsLeftComposition (empiricalCovarianceSqrt z) (empiricalFilteredRootColumns z φ hlam hM h)‖ ^ 2| ≤ _ at hb
  rw [empiricalFilteredRootColumns_shrinkage_norm_sq z φ hlam hM hf h] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (lambda_mul_empiricalFilteredRootColumns_norm_sq_le z φ hlam hM h))
    (norm_nonneg _))

end KernelSeq
