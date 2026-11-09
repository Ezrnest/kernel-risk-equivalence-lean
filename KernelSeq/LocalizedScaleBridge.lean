import KernelSeq.LocalizedAssembly
import KernelSeq.PolarBridge

/-!
# Actual regularization scaling and the supported prediction bridge

The compact spectral choices at two scales need not coincide. All scaling
identities are proved on the original covariance eigenbasis, using spectral
action on each genuine eigenvector. The auxiliary embedded-interaction bound
remains a visible upstream premise; this module supplies no HMS theorem.
-/

namespace KernelSeq

noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Actual dimensionless covariance `T/λ`. -/
def dimensionlessCovariance (T : H →L[ℝ] H) (lam : ℝ) : H →L[ℝ] H := lam⁻¹ • T

omit [CompleteSpace H] in
theorem dimensionlessCovariance_isCompact (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (lam : ℝ) : IsCompactOperator (dimensionlessCovariance T lam) := hc.smul lam⁻¹

omit [CompleteSpace H] in
theorem dimensionlessCovariance_isPositive (T : H →L[ℝ] H) (hp : T.IsPositive)
    {lam : ℝ} (hlam : 0 < lam) : (dimensionlessCovariance T lam).IsPositive :=
  hp.smul_of_nonneg (inv_nonneg.mpr hlam.le)

omit [CompleteSpace H] in
theorem dimensionlessCovariance_norm_le (T : H →L[ℝ] H) {lam M : ℝ}
    (hlam : 0 < lam) (hM : ‖T‖ ≤ M) : ‖dimensionlessCovariance T lam‖ ≤ M / lam := by
  rw [dimensionlessCovariance, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr hlam.le)

omit [CompleteSpace H] in
theorem dimensionlessCovariance_eigen (T : H →L[ℝ] H) (lam : ℝ)
    {x : H} {t : ℝ} (hx : T x = t • x) :
    dimensionlessCovariance T lam x = (t / lam) • x := by
  simp only [dimensionlessCovariance, _root_.smul_apply, hx, smul_smul]
  congr 1
  ring

/-- Exact dimensionless inverse-filter scalar evaluation, including zero. -/
theorem dimensionlessProfile_apply {lam : ℝ} (hlam : lam ≠ 0) (φ : ℝ → ℝ) (t : ℝ) :
    localizedDimensionlessProfile lam φ (t / lam) = lam * φ t := by
  unfold localizedDimensionlessProfile
  rw [mul_div_cancel₀ t hlam]

theorem dimensionlessResidual_apply {lam : ℝ} (hlam : lam ≠ 0) (φ : ℝ → ℝ) (t : ℝ) :
    ResidualFilter.residual (localizedDimensionlessProfile lam φ) (t / lam) =
      ResidualFilter.residual φ t := by
  simp only [ResidualFilter.residual, ResidualFilter.shrinkage, dimensionlessProfile_apply hlam]
  field_simp

theorem dimensionlessResidualWeight_apply {lam : ℝ} (hlam : lam ≠ 0)
    (α : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    residualWeight 1 α (localizedDimensionlessProfile lam φ) (t / lam) = residualWeight lam α φ t := by
  unfold residualWeight
  rw [dimensionlessResidual_apply hlam]
  congr 2
  field_simp

/-- The actual original filter scales as `Φ(T/λ)=λ φ(T)`. No continuity of
`φ` or alignment of the two chosen compact spectral bases is required. -/
theorem compactFilterOperator_dimensionless (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    compactFilterOperator (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
      (dimensionlessCovariance_isPositive T hp hlam) (localizedDimensionlessProfile lam φ)
      (by norm_num) (dimensionlessCovariance_norm_le T hlam hM) (localizedDimensionless_contract hlam h) =
        lam • compactFilterOperator T hc hp φ hlam hM h := by
  apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
  intro i
  have he := dimensionlessCovariance_eigen T lam (compactEigenbasis_eigen T hc hp.isSymmetric i)
  simp only [_root_.smul_apply]
  unfold compactFilterOperator
  rw [compactSpectralMultiplier_eigen _ _ _ _ _ _ _ he,
    compactSpectralMultiplier_eigen _ _ _ _ _ _ _ (compactEigenbasis_eigen T hc hp.isSymmetric i),
    dimensionlessProfile_apply hlam.ne', smul_smul]

/-- The actual residual is invariant under regularization scaling. -/
theorem compactResidualOperator_dimensionless (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) :
    compactResidualOperator (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
      (dimensionlessCovariance_isPositive T hp hlam) (localizedDimensionlessProfile lam φ)
      (dimensionlessCovariance_norm_le T hlam hM) (localizedDimensionless_spectralFilter hlam hf) =
        compactResidualOperator T hc hp φ hM hf := by
  apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
  intro i
  unfold compactResidualOperator
  rw [compactSpectralMultiplier_eigen _ _ _ _ _ _ _
    (dimensionlessCovariance_eigen T lam (compactEigenbasis_eigen T hc hp.isSymmetric i)),
    compactSpectralMultiplier_eigen _ _ _ _ _ _ _ (compactEigenbasis_eigen T hc hp.isSymmetric i),
    dimensionlessResidual_apply hlam.ne']

/-- The actual source weight is invariant under the same scaling. -/
theorem compactResidualWeightOperator_dimensionless (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) :
    compactResidualWeightOperator (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
      (dimensionlessCovariance_isPositive T hp hlam) (localizedDimensionlessProfile lam φ)
      (lam := 1) (α := α) (by norm_num) hα (dimensionlessCovariance_norm_le T hlam hM) (localizedDimensionless_spectralFilter hlam hf) =
        compactResidualWeightOperator T hc hp φ hlam hα hM hf := by
  apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
  intro i
  unfold compactResidualWeightOperator
  rw [compactSpectralMultiplier_eigen _ _ _ _ _ _ _
    (dimensionlessCovariance_eigen T lam (compactEigenbasis_eigen T hc hp.isSymmetric i)),
    compactSpectralMultiplier_eigen _ _ _ _ _ _ _ (compactEigenbasis_eigen T hc hp.isSymmetric i),
    dimensionlessResidualWeight_apply hlam.ne']

/-- Actual root scaling, proved on the original eigenbasis. -/
theorem compactRegularizedSqrt_dimensionless (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) {lam : ℝ} (hlam : 0 < lam)
    (r : ℝ) (hr : 0 ≤ r) :
    compactRegularizedSqrt (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
      (dimensionlessCovariance_isPositive T hp hlam) r =
        (Real.sqrt lam)⁻¹ • compactRegularizedSqrt T hc hp (lam * r) := by
  apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
  intro i
  simp only [_root_.smul_apply]
  rw [compactRegularizedSqrt_eigen _ _ _ r
    (dimensionlessCovariance_eigen T lam (compactEigenbasis_eigen T hc hp.isSymmetric i)),
    compactRegularizedSqrt_eigenbasis, smul_smul]
  congr 1
  have hnum : 0 ≤ i.1 + lam * r := add_nonneg (compactEigenvalue_nonneg T hc hp i) (mul_nonneg hlam.le hr)
  rw [show i.1 / lam + r = (i.1 + lam * r) / lam by field_simp,
    Real.sqrt_div hnum]
  ring

/-- Eigenvector action of the actual inverse root follows from its proved
two-sided cancellation with the actual square root. -/
theorem compactRegularizedInvSqrt_eigen (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) {lam : ℝ} (hlam : 0 < lam)
    {x : H} {t : ℝ} (hx : T x = t • x) (ht : 0 < t + lam) :
    compactRegularizedInvSqrt T hc hp lam x = (Real.sqrt (t + lam))⁻¹ • x := by
  have hn : Real.sqrt (t + lam) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have he := congrArg (fun F : H →L[ℝ] H => F x)
    (compactRegularizedInvSqrt_mul_sqrt T hc hp lam hlam)
  change compactRegularizedInvSqrt T hc hp lam (compactRegularizedSqrt T hc hp lam x) = x at he
  rw [compactRegularizedSqrt_eigen T hc hp lam hx, map_smul] at he
  calc
    _ = (Real.sqrt (t + lam))⁻¹ •
        (Real.sqrt (t + lam) • compactRegularizedInvSqrt T hc hp lam x) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    _ = _ := by rw [he]

/-- The actual inverse-root scaling used in both normalized perturbations. -/
theorem compactRegularizedInvSqrt_dimensionless (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) {lam : ℝ} (hlam : 0 < lam) :
    compactRegularizedInvSqrt (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
      (dimensionlessCovariance_isPositive T hp hlam) 1 =
        Real.sqrt lam • compactRegularizedInvSqrt T hc hp lam := by
  apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
  intro i
  have hi := compactEigenvalue_nonneg T hc hp i
  simp only [_root_.smul_apply]
  rw [compactRegularizedInvSqrt_eigen _ _ _ (by norm_num)
    (dimensionlessCovariance_eigen T lam (compactEigenbasis_eigen T hc hp.isSymmetric i)) (by positivity),
    compactRegularizedInvSqrt_eigenbasis T hc hp lam hlam, smul_smul]
  congr 1
  rw [show i.1 / lam + 1 = (i.1 + lam) / lam by field_simp,
    Real.sqrt_div (add_nonneg hi hlam.le), inv_div]
  ring

/-- Actual low projections have the original cutoff `λτ`, including its
boundary atom. This is proved without identifying the two chosen bases. -/
theorem lowBlockProjection_dimensionless (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    lowBlockProjection (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
      (dimensionlessCovariance_isPositive T hp hlam) τ = lowBlockProjection T hc hp (lam * τ) := by
  apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
  intro i
  have hi := compactEigenvalue_nonneg T hc hp i
  have hmem : i.1 / lam ∈ Set.Icc (0 : ℝ) τ ↔ i.1 ∈ Set.Icc (0 : ℝ) (lam * τ) := by
    simp only [Set.mem_Icc, hi, div_nonneg hi hlam.le, true_and]
    rw [div_le_iff₀ hlam, mul_comm τ lam]
  unfold lowBlockProjection compactSpectralProjection
  rw [compactSpectralMultiplier_eigen _ _ _ _ _ _ _
    (dimensionlessCovariance_eigen T lam (compactEigenbasis_eigen T hc hp.isSymmetric i)),
    compactSpectralMultiplier_eigen _ _ _ _ _ _ _ (compactEigenbasis_eigen T hc hp.isSymmetric i)]
  simp only [hmem]
  split_ifs <;> simp

/-- The actual normalized covariance perturbation is strictly scale invariant. -/
theorem realNormalizedPerturbation_dimensionless (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) {lam : ℝ} (hlam : 0 < lam) :
    realNormalizedPerturbation (dimensionlessCovariance T lam) (dimensionlessCovariance TX lam)
      (dimensionlessCovariance_isCompact T hc lam) (dimensionlessCovariance_isPositive T hp hlam) 1 =
        realNormalizedPerturbation T TX hc hp lam := by
  unfold realNormalizedPerturbation
  rw [compactRegularizedInvSqrt_dimensionless T hc hp hlam]
  change (Real.sqrt lam • compactRegularizedInvSqrt T hc hp lam) *
      (lam⁻¹ • TX - lam⁻¹ • T) * (Real.sqrt lam • compactRegularizedInvSqrt T hc hp lam) = _
  rw [← smul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hs : Real.sqrt lam * lam⁻¹ * Real.sqrt lam = 1 := by
    calc
      _ = (Real.sqrt lam * Real.sqrt lam) * lam⁻¹ := by ring
      _ = 1 := by rw [Real.mul_self_sqrt hlam.le, mul_inv_cancel₀ hlam.ne']
  simp only [mul_assoc] at hs
  rw [hs, one_smul]

/-- The manuscript-oriented actual mixed perturbation is also strictly
invariant. Thus the same actual HS columns can be used at both scales. -/
theorem manuscriptMixedPerturbation_dimensionless (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) {lam : ℝ} (hlam : 0 < lam) :
    manuscriptMixedPerturbation (dimensionlessCovariance T lam) (dimensionlessCovariance TX lam)
      (dimensionlessCovariance_isCompact T hc lam) (dimensionlessCovariance_isCompact TX hcX lam)
      (dimensionlessCovariance_isPositive T hp hlam) (dimensionlessCovariance_isPositive TX hpX hlam) 1 =
        manuscriptMixedPerturbation T TX hc hcX hp hpX lam := by
  unfold manuscriptMixedPerturbation
  rw [compactRegularizedInvSqrt_dimensionless T hc hp hlam,
    compactRegularizedInvSqrt_dimensionless TX hcX hpX hlam]
  change (Real.sqrt lam • compactRegularizedInvSqrt TX hcX hpX lam) *
      (lam⁻¹ • TX - lam⁻¹ • T) * (Real.sqrt lam • compactRegularizedInvSqrt T hc hp lam) = _
  rw [← smul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hs : Real.sqrt lam * lam⁻¹ * Real.sqrt lam = 1 := by
    calc
      _ = (Real.sqrt lam * Real.sqrt lam) * lam⁻¹ := by ring
      _ = 1 := by rw [Real.mul_self_sqrt hlam.le, mul_inv_cancel₀ hlam.ne']
  simp only [mul_assoc] at hs
  rw [hs, one_smul]

/-- Exact interaction scaling for the original residual-only filter contract. -/
theorem compactInteraction_dimensionless (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    compactInteraction (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
      (dimensionlessCovariance_isCompact TX hcX lam) (dimensionlessCovariance_isCompact T hc lam)
      (dimensionlessCovariance_isPositive TX hpX hlam) (dimensionlessCovariance_isPositive T hp hlam)
      (localizedDimensionlessProfile lam φ) (by norm_num)
      (dimensionlessCovariance_norm_le TX hlam hMX) (dimensionlessCovariance_norm_le T hlam hM)
      (localizedDimensionless_spectralFilter hlam hf) (localizedDimensionless_contract hlam h) =
        lam • compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h := by
  unfold compactInteraction
  rw [compactFilterOperator_dimensionless TX hcX hpX φ hlam hMX h,
    compactFilterOperator_dimensionless T hc hp φ hlam hM h,
    compactResidualOperator_dimensionless TX hcX hpX φ hlam hMX hf,
    compactResidualOperator_dimensionless T hc hp φ hlam hM hf,
    smul_mul_assoc, mul_smul_comm, ← smul_sub]

/-- The sandwiched interaction used by the prediction bridge is exactly
invariant: the two square-root factors cancel the inverse-filter scaling. -/
theorem embeddedInteraction_dimensionless (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    compactRegularizedSqrt (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
        (dimensionlessCovariance_isPositive T hp hlam) 0 *
      compactInteraction (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
        (dimensionlessCovariance_isCompact TX hcX lam) (dimensionlessCovariance_isCompact T hc lam)
        (dimensionlessCovariance_isPositive TX hpX hlam) (dimensionlessCovariance_isPositive T hp hlam)
        (localizedDimensionlessProfile lam φ) (by norm_num)
        (dimensionlessCovariance_norm_le TX hlam hMX) (dimensionlessCovariance_norm_le T hlam hM)
        (localizedDimensionless_spectralFilter hlam hf) (localizedDimensionless_contract hlam h) *
      compactRegularizedSqrt (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
        (dimensionlessCovariance_isPositive T hp hlam) 0 =
      compactRegularizedSqrt T hc hp 0 * compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h *
        compactRegularizedSqrt T hc hp 0 := by
  rw [compactInteraction_dimensionless TX T hcX hc hpX hp φ hlam hMX hM hf h,
    compactRegularizedSqrt_dimensionless T hc hp hlam 0 (by norm_num)]
  simp only [mul_zero, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hn : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
  have hs : (Real.sqrt lam)⁻¹ * lam * (Real.sqrt lam)⁻¹ = 1 := by
    field_simp
    nlinarith [Real.sq_sqrt hlam.le]
  simp only [mul_assoc] at hs
  rw [hs, one_smul]

/-- The actual original auxiliary construction commutes with dimensionless
scaling, as an equality of profiles rather than a supplied operator premise. -/
theorem auxiliaryProfile_dimensionless {lam : ℝ} (hlam : lam ≠ 0)
    (τ : ℝ) (φ : ℝ → ℝ) :
    localizedDimensionlessProfile lam (ResidualFilter.auxiliaryFilter lam τ φ) =
      ResidualFilter.auxiliaryFilter 1 τ (localizedDimensionlessProfile lam φ) := by
  funext u
  exact auxiliaryFilter_dimensionless lam hlam τ φ u

/-- Equal scalar profiles define equal actual interaction operators. -/
theorem compactInteraction_profile_congr {TX T : H →L[ℝ] H}
    {hcX : IsCompactOperator TX} {hc : IsCompactOperator T}
    {hpX : TX.IsPositive} {hp : T.IsPositive} {φ ψ : ℝ → ℝ}
    {lam M ρ A : ℝ} {hlam : 0 < lam} {hMX : ‖TX‖ ≤ M} {hM : ‖T‖ ≤ M}
    {hfφ : ResidualFilter.SpectralFilter M φ} {hφ : ResidualFilter.Contract lam M ρ A φ}
    {hfψ : ResidualFilter.SpectralFilter M ψ} {hψ : ResidualFilter.Contract lam M ρ A ψ}
    (heq : φ = ψ) :
    compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hfφ hφ =
      compactInteraction TX T hcX hc hpX hp ψ hlam hMX hM hfψ hψ := by
  subst ψ
  rfl

/-- Exact scaling of the actual auxiliary sandwiched interaction. Both
auxiliary contracts are derived from the same original contract. -/
theorem embeddedAuxiliaryInteraction_dimensionless (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A τ : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    compactRegularizedSqrt (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
        (dimensionlessCovariance_isPositive T hp hlam) 0 *
      compactInteraction (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
        (dimensionlessCovariance_isCompact TX hcX lam) (dimensionlessCovariance_isCompact T hc lam)
        (dimensionlessCovariance_isPositive TX hpX hlam) (dimensionlessCovariance_isPositive T hp hlam)
        (ResidualFilter.auxiliaryFilter 1 τ (localizedDimensionlessProfile lam φ)) (by norm_num)
        (dimensionlessCovariance_norm_le TX hlam hMX) (dimensionlessCovariance_norm_le T hlam hM)
        (localizedDimensionless_spectralFilter hlam hf).auxiliary
        ((localizedDimensionless_contract hlam h).auxiliary_contract (by norm_num) hτ hτ1) *
      compactRegularizedSqrt (dimensionlessCovariance T lam) (dimensionlessCovariance_isCompact T hc lam)
        (dimensionlessCovariance_isPositive T hp hlam) 0 =
      compactRegularizedSqrt T hc hp 0 *
        compactInteraction TX T hcX hc hpX hp (ResidualFilter.auxiliaryFilter lam τ φ)
          hlam hMX hM hf.auxiliary (h.auxiliary_contract hlam hτ hτ1) *
        compactRegularizedSqrt T hc hp 0 := by
  have he := embeddedInteraction_dimensionless TX T hcX hc hpX hp
    (ResidualFilter.auxiliaryFilter lam τ φ) hlam hMX hM hf.auxiliary
    (h.auxiliary_contract hlam hτ hτ1)
  have hJi : compactInteraction (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
      (dimensionlessCovariance_isCompact TX hcX lam) (dimensionlessCovariance_isCompact T hc lam)
      (dimensionlessCovariance_isPositive TX hpX hlam) (dimensionlessCovariance_isPositive T hp hlam)
      (localizedDimensionlessProfile lam (ResidualFilter.auxiliaryFilter lam τ φ)) (by norm_num)
      (dimensionlessCovariance_norm_le TX hlam hMX) (dimensionlessCovariance_norm_le T hlam hM)
      (localizedDimensionless_spectralFilter hlam hf.auxiliary)
      (localizedDimensionless_contract hlam (h.auxiliary_contract hlam hτ hτ1)) =
    compactInteraction (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
      (dimensionlessCovariance_isCompact TX hcX lam) (dimensionlessCovariance_isCompact T hc lam)
      (dimensionlessCovariance_isPositive TX hpX hlam) (dimensionlessCovariance_isPositive T hp hlam)
      (ResidualFilter.auxiliaryFilter 1 τ (localizedDimensionlessProfile lam φ)) (by norm_num)
      (dimensionlessCovariance_norm_le TX hlam hMX) (dimensionlessCovariance_norm_le T hlam hM)
      (localizedDimensionless_spectralFilter hlam hf).auxiliary
      ((localizedDimensionless_contract hlam h).auxiliary_contract (by norm_num) hτ hτ1) :=
    compactInteraction_profile_congr (auxiliaryProfile_dimensionless hlam.ne' τ φ)
  rw [hJi] at he
  exact he

/-- Actual original-scale localized interaction, conditional only on the
visible actual original-scale auxiliary embedded estimate. All regularization
scaling, the mixed-column reconstruction at the new scale, and projection
boundaries are derived rather than supplied as certificates. -/
theorem localized_original_scale_of_auxiliary_bound (b : HilbertBasis ι ℝ H)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α τ : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hτA : τ ≤ 1 / (4 * (A + 1)))
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 4)
    (c : HilbertSchmidtColumns ι H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation T TX hc hcX hp hpX lam)
    (Caux : ℝ)
    (haux : ∀ z : H,
      ‖(compactRegularizedSqrt T hc hp 0 *
          compactInteraction TX T hcX hc hpX hp (ResidualFilter.auxiliaryFilter lam τ φ)
            hlam hMX hM hf.auxiliary (h.auxiliary_contract hlam hτ hτ1) *
          compactRegularizedSqrt T hc hp 0 * (1 - lowBlockProjection T hc hp (lam * τ))) z‖ ≤
        Caux * (hsSchattenEndpoint b c / τ) *
          ‖compactResidualWeightOperator T hc hp φ hlam hα0 hM hf
            ((1 - lowBlockProjection T hc hp (lam * τ)) z)‖)
    (z : H) :
    ‖(compactRegularizedSqrt T hc hp 0 * compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h *
        compactRegularizedSqrt T hc hp 0) z‖ ≤
      localizedAssemblyConstant A Caux * (τ + ‖realNormalizedPerturbation T TX hc hp lam‖ / τ) *
        ‖compactResidualOperator T hc hp φ hM hf z‖ +
      localizedAssemblyConstant A Caux * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator T hc hp φ hlam hα0 hM hf z‖ := by
  have hδd : lowBlockDeviation (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
      (dimensionlessCovariance_isCompact T hc lam) (dimensionlessCovariance_isPositive T hp hlam) ≤ 1 / 4 := by
    unfold lowBlockDeviation
    rw [realNormalizedPerturbation_dimensionless T TX hc hp hlam]
    exact hδ
  have hcKd : hilbertSchmidtOperator b c = manuscriptMixedPerturbation
      (dimensionlessCovariance T lam) (dimensionlessCovariance TX lam)
      (dimensionlessCovariance_isCompact T hc lam) (dimensionlessCovariance_isCompact TX hcX lam)
      (dimensionlessCovariance_isPositive T hp hlam) (dimensionlessCovariance_isPositive TX hpX hlam) 1 := by
    rw [manuscriptMixedPerturbation_dimensionless T TX hc hcX hp hpX hlam]
    exact hcK
  have hb := localized_interaction_of_auxiliary_bound b
    (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
    (dimensionlessCovariance_isCompact TX hcX lam) (dimensionlessCovariance_isCompact T hc lam)
    (dimensionlessCovariance_isPositive TX hpX hlam) (dimensionlessCovariance_isPositive T hp hlam)
    (localizedDimensionlessProfile lam φ)
    (dimensionlessCovariance_norm_le TX hlam hMX) (dimensionlessCovariance_norm_le T hlam hM)
    (localizedDimensionless_spectralFilter hlam hf) (localizedDimensionless_contract hlam h)
    hα0 hα2 hτ hτ1 hτA hδd c hcKd Caux (fun w => by
      simpa only [embeddedAuxiliaryInteraction_dimensionless TX T hcX hc hpX hp φ hlam hMX hM hf h hτ hτ1,
        lowBlockProjection_dimensionless T hc hp hlam τ,
        compactResidualWeightOperator_dimensionless T hc hp φ hlam hα0 hM hf] using haux w) z
  simpa only [embeddedInteraction_dimensionless TX T hcX hc hpX hp φ hlam hMX hM hf h,
    lowBlockDeviation, realNormalizedPerturbation_dimensionless T TX hc hp hlam,
    compactResidualOperator_dimensionless T hc hp φ hlam hM hf,
    compactResidualWeightOperator_dimensionless T hc hp φ hlam hα0 hM hf] using hb

section Prediction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The two actual adjoint-product covariance norms agree for arbitrary
real Hilbert prediction spaces. -/
theorem self_comp_adjoint_norm_eq_adjoint_comp_self (S : H →L[ℝ] E) :
    ‖S.comp S.adjoint‖ = ‖S.adjoint.comp S‖ := by
  calc
    _ = ‖S.adjoint‖ * ‖S.adjoint‖ := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using S.adjoint.norm_adjoint_comp_self
    _ = ‖S‖ * ‖S‖ := by simp only [LinearIsometryEquiv.norm_map]
    _ = _ := S.norm_adjoint_comp_self.symm

/-- Original-scale supported prediction localization conditional on the
visible auxiliary embedded-interaction core bound `haux`. The supported polar
isometry and all prediction/residual/weight bridges are constructed; none is
an extra premise. Only the actual feature covariance is required compact,
and no separability or closed-range hypothesis is placed on either space. -/
theorem localized_prediction_of_auxiliary_bound (b : HilbertBasis ι ℝ H)
    (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    (TX : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hpX : TX.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α τ : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖S.adjoint.comp S‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hτA : τ ≤ 1 / (4 * (A + 1)))
    (hδ : ‖realNormalizedPerturbation (S.adjoint.comp S) TX hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam‖ ≤ 1 / 4)
    (c : HilbertSchmidtColumns ι H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation (S.adjoint.comp S) TX hc hcX
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) hpX lam)
    (Caux : ℝ)
    (haux : ∀ z : H,
      ‖(compactRegularizedSqrt (S.adjoint.comp S) hc
            (ContinuousLinearMap.isPositive_adjoint_comp_self S) 0 *
          compactInteraction TX (S.adjoint.comp S) hcX hc hpX
            (ContinuousLinearMap.isPositive_adjoint_comp_self S) (ResidualFilter.auxiliaryFilter lam τ φ)
            hlam hMX hM hf.auxiliary (h.auxiliary_contract hlam hτ hτ1) *
          compactRegularizedSqrt (S.adjoint.comp S) hc
            (ContinuousLinearMap.isPositive_adjoint_comp_self S) 0 *
          (1 - lowBlockProjection (S.adjoint.comp S) hc
            (ContinuousLinearMap.isPositive_adjoint_comp_self S) (lam * τ))) z‖ ≤
        Caux * (hsSchattenEndpoint b c / τ) *
          ‖compactResidualWeightOperator (S.adjoint.comp S) hc
            (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hα0 hM hf
            ((1 - lowBlockProjection (S.adjoint.comp S) hc
              (ContinuousLinearMap.isPositive_adjoint_comp_self S) (lam * τ)) z)‖)
    (f : E) (hsupport : f ∈ (S.comp S.adjoint).range.topologicalClosure) :
    ‖S (compactInteraction TX (S.adjoint.comp S) hcX hc hpX
        (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h (S.adjoint f))‖ ≤
      localizedAssemblyConstant A Caux *
        (τ + ‖realNormalizedPerturbation (S.adjoint.comp S) TX hc
          (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam‖ / τ) *
        ‖compactResidualOperator (S.comp S.adjoint)
          (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
          (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ
          ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf f‖ +
      localizedAssemblyConstant A Caux * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator (S.comp S.adjoint)
          (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
          (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα0
          ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf f‖ := by
  have hfRange : f ∈ PredictionRange S := by
    simpa only [closure_range_self_comp_adjoint S] using hsupport
  let fs : PredictionRange S := ⟨f, hfRange⟩
  let G := compactInteraction TX (S.adjoint.comp S) hcX hc hpX
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h
  have hb := localized_original_scale_of_auxiliary_bound b TX (S.adjoint.comp S) hcX hc hpX
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h hα0 hα2 hτ hτ1 hτA
    hδ c hcK Caux haux (supportedPolarIsometry S hc fs)
  simp only [mul_apply_eq_comp] at hb
  have hnorm := prediction_interaction_norm_eq S hc G fs
  have hres := prediction_residual_norm_eq S hc φ hM
    ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf fs
  have hweight := prediction_residualWeight_norm_eq S hc φ hlam hα0 hM
    ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf fs
  rw [← hnorm, ← hres, ← hweight] at hb
  exact hb

end Prediction

end
end KernelSeq
