import KernelSeq.LogInteractionFactorization
import KernelSeq.LocalizedScaleBridge
import KernelSeq.SchattenCompression
import KernelSeq.ActualBiasTransfer

/-!
# Actual two-basis DOI identification for the embedded interaction

The normalized logarithmic interaction kernel acts by an actual HS Schur map.
The DOI identification, common-eigenvalue cancellation, regularized outside
factors, and supported prediction bridge are proved here. A bound for this
specific Schur map is a visible analytic premise, not an asserted HMS theorem.
-/

namespace KernelSeq

noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual logarithmic coordinate of a compact spectral value. -/
def compactLogCoordinate (T : H →L[ℝ] H) (lam : ℝ) (i : CompactSpectralIndex T) : ℝ :=
  Real.log (1 + i.1 / lam)

/-- The actual normalized logarithmic interaction symbol on the two spectral
bases. The inverse profile is the original dimensionless profile. -/
def compactLogInteractionKernel (TX T : H →L[ℝ] H) (lam α : ℝ) (φ : ℝ → ℝ)
    (i : CompactSpectralIndex TX) (j : CompactSpectralIndex T) : ℝ :=
  logarithmicInteractionKernel α (localizedDimensionlessProfile lam φ) (i.1 / lam) (j.1 / lam)

theorem compactLogCoordinate_mem (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hp : T.IsPositive) {lam M : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (i : CompactSpectralIndex T) : compactLogCoordinate T lam i ∈ ResidualFilter.logDomain lam M :=
  ResidualFilter.log_coordinate_mem hlam ⟨compactEigenvalue_nonneg T hc hp i,
    ((le_abs_self i.1).trans (compactEigenvalue_norm_le T hc hp.isSymmetric i)).trans hM⟩

theorem exp_compactLogCoordinate_sub_one (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hp : T.IsPositive) {lam : ℝ} (hlam : 0 < lam) (i : CompactSpectralIndex T) :
    Real.exp (compactLogCoordinate T lam i) - 1 = i.1 / lam := by
  rw [compactLogCoordinate, Real.exp_log (by positivity [compactEigenvalue_nonneg T hc hp i])]
  ring

/-- The three-factor logarithmic symbol is evaluated at the actual logarithmic
empirical and population eigenvalue coordinates. -/
theorem compactLogInteractionKernel_factorization (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) {lam : ℝ} (hlam : 0 < lam)
    (α : ℝ) (φ : ℝ → ℝ) (i : CompactSpectralIndex TX) (j : CompactSpectralIndex T) :
    let x := compactLogCoordinate TX lam i
    let y := compactLogCoordinate T lam j
    let Φ := localizedDimensionlessProfile lam φ
    compactLogInteractionKernel TX T lam α φ i j =
      (1 / (1 + logInteractionResidualProfile α Φ y)) *
        (-logInteractionInverseProfile Φ x * interactionTheta α (x - y) *
            dividedDifference (logInteractionResidualProfile α Φ) x y +
          logInteractionResidualProfile α Φ x * interactionTheta α (x - y) *
            dividedDifference (logInteractionInverseProfile Φ) x y +
          logInteractionInverseProfile Φ x * logInteractionResidualProfile α Φ y *
            interactionChiOffDiagonal α x y) := by
  have he := logarithmicInteractionKernel_factorization α (localizedDimensionlessProfile lam φ)
    (compactLogCoordinate TX lam i) (compactLogCoordinate T lam j)
  rw [exp_compactLogCoordinate_sub_one TX hcX hpX hlam i,
    exp_compactLogCoordinate_sub_one T hc hp hlam j] at he
  exact he

/-- The same normalized symbol in original spectral units. -/
def physicalInteractionKernel (lam α : ℝ) (φ : ℝ → ℝ) (u v : ℝ) : ℝ :=
  if u = v then 0 else (lam + u) * (lam + v) *
    (φ u * ResidualFilter.residual φ v - ResidualFilter.residual φ u * φ v) /
      ((u - v) * residualWeight lam α φ v)

theorem logarithmicInteractionKernel_original_units {lam : ℝ} (hlam : lam ≠ 0)
    (α : ℝ) (φ : ℝ → ℝ) (u v : ℝ) :
    logarithmicInteractionKernel α (localizedDimensionlessProfile lam φ) (u / lam) (v / lam) =
      physicalInteractionKernel lam α φ u v := by
  by_cases huv : u = v
  · simp [huv, logarithmicInteractionKernel, physicalInteractionKernel]
  have hscaled : u / lam ≠ v / lam := by
    intro hh
    apply huv
    field_simp [hlam] at hh
    exact hh
  rw [logarithmicInteractionKernel, if_neg hscaled, physicalInteractionKernel, if_neg huv,
    dimensionlessProfile_apply hlam, dimensionlessProfile_apply hlam,
    dimensionlessResidual_apply hlam, dimensionlessResidual_apply hlam,
    dimensionlessResidualWeight_apply hlam]
  by_cases ha : residualWeight lam α φ v = 0
  · simp only [ha, mul_zero, div_zero]
  · field_simp [hlam, ha, sub_ne_zero.mpr huv]

/-- The original source weight is strictly positive on the true nonnegative
spectrum; all cancellation below therefore avoids division by zero. -/
theorem embedded_residualWeight_pos {lam M α t : ℝ} {φ : ℝ → ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter M φ)
    (ht : t ∈ Set.Icc (0 : ℝ) M) : 0 < residualWeight lam α φ t := by
  have hb := regularization_weight_mem hlam ht
  exact add_pos_of_nonneg_of_pos (hf.residual_nonneg ht) (Real.rpow_pos_of_pos hb.1 _)

/-- Exact scalar cancellation of the two regularization roots and source
weight in a non-diagonal normalized DOI entry. -/
theorem embedded_kernel_root_cancellation {lam u v a N c : ℝ}
    (hlam : 0 < lam) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u - v ≠ 0) (ha : a ≠ 0) :
    ((Real.sqrt (v + lam))⁻¹ * a) *
      (((lam + u) * (lam + v) * N / ((u - v) * a)) *
        (((u - v) / (Real.sqrt (u + lam) * Real.sqrt (v + lam))) * c)) =
      Real.sqrt (u + lam) * N * c := by
  have hsu : Real.sqrt (u + lam) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsv : Real.sqrt (v + lam) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [show lam + u = (Real.sqrt (u + lam)) ^ 2 by rw [Real.sq_sqrt (by positivity)]; ring,
    show lam + v = (Real.sqrt (v + lam)) ^ 2 by rw [Real.sq_sqrt (by positivity)]; ring]
  field_simp

/-- Genuine cross entries of the original-scale interaction. -/
theorem compactInteraction_original_cross_entry (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (i : CompactSpectralIndex TX) (j : CompactSpectralIndex T) :
    inner ℝ (compactEigenbasis TX hcX hpX.isSymmetric i)
      (compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h
        (compactEigenbasis T hc hp.isSymmetric j)) =
      (φ i.1 * ResidualFilter.residual φ j.1 - ResidualFilter.residual φ i.1 * φ j.1) *
        inner ℝ (compactEigenbasis TX hcX hpX.isSymmetric i)
          (compactEigenbasis T hc hp.isSymmetric j) := by
  have hF : compactFilterOperator T hc hp φ hlam hM h (compactEigenbasis T hc hp.isSymmetric j) =
      φ j.1 • compactEigenbasis T hc hp.isSymmetric j := by
    unfold compactFilterOperator
    exact compactSpectralMultiplier_eigen _ _ _ _ _ _ _ (compactEigenbasis_eigen T hc hp.isSymmetric j)
  have hR : compactResidualOperator T hc hp φ hM hf (compactEigenbasis T hc hp.isSymmetric j) =
      ResidualFilter.residual φ j.1 • compactEigenbasis T hc hp.isSymmetric j := by
    unfold compactResidualOperator
    exact compactSpectralMultiplier_eigen _ _ _ _ _ _ _ (compactEigenbasis_eigen T hc hp.isSymmetric j)
  change inner ℝ _ (compactFilterOperator TX hcX hpX φ hlam hMX h
      (compactResidualOperator T hc hp φ hM hf _) -
    compactResidualOperator TX hcX hpX φ hMX hf (compactFilterOperator T hc hp φ hlam hM h _)) = _
  rw [hF, hR, map_smul, map_smul, inner_sub_right, inner_smul_right, inner_smul_right]
  simp only [compactFilterOperator, compactResidualOperator,
    ← HilbertBasis.repr_apply_apply, compactSpectralMultiplier_repr]
  ring

/-- Actual HS columns of the normalized interaction DOI in the true population
spectral basis. Rebase is constructed from the original actual HS columns. -/
def embeddedInteractionDOIColumns (b : HilbertBasis ι ℝ H)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (lam α : ℝ) (φ : ℝ → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hkernel : ∀ i j, ‖compactLogInteractionKernel TX T lam α φ i j‖ ≤ B)
    (c : HilbertSchmidtColumns ι H) : HilbertSchmidtColumns (CompactSpectralIndex T) H :=
  hsSchurMultiplier (compactEigenbasis TX hcX hpX.isSymmetric)
    (compactLogInteractionKernel TX T lam α φ) B hB hkernel
    (hsRebase b (compactEigenbasis T hc hp.isSymmetric) c)

/-- The exact normalized DOI identification. The HS output is constructed,
and its product with the actual population weight and inverse root is the
actual empirical regularized root times the actual interaction. Common spectral
values are handled by the zero numerator, with no diagonal certificate. -/
theorem embeddedInteractionDOI_represents (b : HilbertBasis ι ℝ H)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α B : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα : 0 ≤ α) (hB : 0 ≤ B)
    (hkernel : ∀ i j, ‖compactLogInteractionKernel TX T lam α φ i j‖ ≤ B)
    (c : HilbertSchmidtColumns ι H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation T TX hc hcX hp hpX lam) :
    hilbertSchmidtOperator (compactEigenbasis T hc hp.isSymmetric)
        (embeddedInteractionDOIColumns b TX T hcX hc hpX hp lam α φ B hB hkernel c) *
      compactRegularizedInvSqrt T hc hp lam * compactResidualWeightOperator T hc hp φ hlam hα hM hf =
      compactRegularizedSqrt TX hcX hpX lam * compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h := by
  let bX := compactEigenbasis TX hcX hpX.isSymmetric
  let bT := compactEigenbasis T hc hp.isSymmetric
  let Aop := hilbertSchmidtOperator bT (embeddedInteractionDOIColumns b TX T hcX hc hpX hp lam α φ B hB hkernel c)
  let a := compactResidualWeightOperator T hc hp φ hlam hα hM hf
  let R := compactRegularizedInvSqrt T hc hp lam
  let QX := compactRegularizedSqrt TX hcX hpX lam
  let G := compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h
  change Aop * R * a = QX * G
  apply continuousLinearMap_eq_of_hilbertBasis bT
  intro j
  have hae : a (bT j) = residualWeight lam α φ j.1 • bT j := by
    exact compactSpectralMultiplier_eigen T hc hp _ _ _ _ (compactEigenbasis_eigen T hc hp.isSymmetric j)
  have hR : R (bT j) = (Real.sqrt (j.1 + lam))⁻¹ • bT j := compactRegularizedInvSqrt_eigenbasis T hc hp lam hlam j
  simp only [mul_apply_eq_comp, hae, hR, map_smul, smul_smul]
  apply bX.repr.injective
  ext i
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hA := hsSchurMultiplier_coefficient bX bT (compactLogInteractionKernel TX T lam α φ) B hB hkernel
    (hsRebase b bT c) i j
  change inner ℝ (bX i) (Aop (bT j)) = compactLogInteractionKernel TX T lam α φ i j *
    inner ℝ (bX i) (hilbertSchmidtOperator bT (hsRebase b bT c) (bT j)) at hA
  rw [hilbertSchmidtOperator_rebase b bT c, hcK] at hA
  have hK : inner ℝ (bX i) (manuscriptMixedPerturbation T TX hc hcX hp hpX lam (bT j)) =
      ((i.1 - j.1) / (Real.sqrt (i.1 + lam) * Real.sqrt (j.1 + lam))) * inner ℝ (bX i) (bT j) :=
    compactMixedDifference_cross_entry TX T hcX hc hpX hp lam hlam i j
  rw [hK] at hA
  have hQX : bX.repr (QX (G (bT j))) i = Real.sqrt (i.1 + lam) * bX.repr (G (bT j)) i :=
    compactRegularizedSqrt_repr TX hcX hpX lam _ i
  rw [hQX, bX.repr_apply_apply, bX.repr_apply_apply, hA,
    compactInteraction_original_cross_entry TX T hcX hc hpX hp φ hlam hMX hM hf h i j]
  rw [compactLogInteractionKernel, logarithmicInteractionKernel_original_units hlam.ne']
  by_cases hij : i.1 = j.1
  · rw [physicalInteractionKernel, if_pos hij, hij]
    ring
  · rw [physicalInteractionKernel, if_neg hij]
    have ht : j.1 ∈ Set.Icc (0 : ℝ) M :=
      ⟨compactEigenvalue_nonneg T hc hp j,
        ((le_abs_self j.1).trans (compactEigenvalue_norm_le T hc hp.isSymmetric j)).trans hM⟩
    simpa only [mul_assoc, mul_comm (residualWeight lam α φ j.1) ((Real.sqrt (j.1 + lam))⁻¹)] using
      (embedded_kernel_root_cancellation (N := φ i.1 * ResidualFilter.residual φ j.1 -
        ResidualFilter.residual φ i.1 * φ j.1) (c := inner ℝ (bX i) (bT j)) hlam
        (compactEigenvalue_nonneg TX hcX hpX i) (compactEigenvalue_nonneg T hc hp j)
        (sub_ne_zero.mpr hij) (ne_of_gt (embedded_residualWeight_pos hlam hf ht)))

/-- A visible Schur estimate for the actual normalized interaction kernel
controls the actual reconstructed DOI operator. No DOI reconstruction or
output-HS certificate is a premise. -/
theorem embeddedInteractionDOI_norm_le_of_schur (b : HilbertBasis ι ℝ H)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (lam α : ℝ) (φ : ℝ → ℝ)
    {B C p : ℝ} (hB : 0 ≤ B)
    (hkernel : ∀ i j, ‖compactLogInteractionKernel TX T lam α φ i j‖ ≤ B) (hp2 : 2 ≤ p)
    (hSchur : ∀ d : HilbertSchmidtColumns (CompactSpectralIndex T) H,
      hsSchattenNorm (compactEigenbasis T hc hp.isSymmetric)
        (hsSchurMultiplier (compactEigenbasis TX hcX hpX.isSymmetric)
          (compactLogInteractionKernel TX T lam α φ) B hB hkernel d) p ≤
        C * hsSchattenNorm (compactEigenbasis T hc hp.isSymmetric) d p)
    (c : HilbertSchmidtColumns ι H) :
    ‖hilbertSchmidtOperator (compactEigenbasis T hc hp.isSymmetric)
        (embeddedInteractionDOIColumns b TX T hcX hc hpX hp lam α φ B hB hkernel c)‖ ≤
      C * hsSchattenNorm b c p := by
  have hs := hSchur (hsRebase b (compactEigenbasis T hc hp.isSymmetric) c)
  rw [hsSchattenNorm_rebase] at hs
  exact (opNorm_le_hsSchattenNorm (compactEigenbasis T hc hp.isSymmetric) _ hp2).trans hs

/-- The actual population root-normalized covariance factor is a contraction
at every strictly positive regularization, not just in dimensionless units. -/
theorem embedded_population_root_factor_norm_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) {lam : ℝ} (hlam : 0 < lam) :
    ‖compactRegularizedSqrt T hc hp 0 * compactRegularizedInvSqrt T hc hp lam‖ ≤ 1 := by
  let R := compactRegularizedInvSqrt T hc hp lam
  let S := compactRegularizedSqrt T hc hp 0
  have heq : (S * R).adjoint * (S * R) = compactNormalizedCovariance T hc hp lam := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      (compactRegularizedInvSqrt_isSelfAdjoint T hc hp lam).adjoint_eq,
      (compactRegularizedSqrt_isSelfAdjoint T hc hp 0).adjoint_eq, S, R]
    change R * S * (S * R) = R * T * R
    rw [show R * S * (S * R) = R * (S * S) * R by simp only [mul_assoc],
      compactRegularizedSqrt_sq T hc hp 0 (by norm_num)]
    simp
  have hs : ‖S * R‖ ^ 2 ≤ 1 := by
    rw [pow_two, ← ContinuousLinearMap.norm_adjoint_comp_self]
    exact (congrArg norm heq).trans_le (compactNormalizedCovariance_norm_le_one T hc hp lam hlam)
  change ‖S * R‖ ≤ 1
  nlinarith [norm_nonneg (S * R)]

/-- The empirical outside root factor is bounded by the actual relative
quadratic comparison, with the explicit `sqrt 2` constant. -/
theorem embedded_empirical_root_factor_norm_le (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) {lam : ℝ} (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 4) :
    ‖compactRegularizedSqrt T hc hp 0 * compactRegularizedInvSqrt TX hcX hpX lam‖ ≤ Real.sqrt 2 := by
  let S := compactRegularizedSqrt T hc hp 0
  let R := compactRegularizedInvSqrt T hc hp lam
  let RX := compactRegularizedInvSqrt TX hcX hpX lam
  let D := rootTransition T TX hc hcX hp hpX lam
  have hfac : S * RX = (S * R) * D := by
    dsimp only [D, rootTransition]
    calc
      _ = S * (R * compactRegularizedSqrt T hc hp lam) * RX := by
        rw [show R * compactRegularizedSqrt T hc hp lam = 1 from
          compactRegularizedInvSqrt_mul_sqrt T hc hp lam hlam]
        simp
      _ = _ := by simp only [RX, mul_assoc]
  change ‖S * RX‖ ≤ _
  rw [hfac]
  calc
    _ ≤ ‖S * R‖ * ‖D‖ := norm_mul_le _ _
    _ ≤ 1 * Real.sqrt 2 := mul_le_mul (embedded_population_root_factor_norm_le T hc hp hlam)
      (rootTransition_norm_le T TX hc hcX hp hpX lam hlam (hδ.trans (by norm_num))) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The actual weighted population inverse-root vector is controlled by the
actual source weight, with no support or separability assumption on the vector. -/
theorem embedded_weighted_right_vector_norm_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (z : H) :
    ‖compactRegularizedInvSqrt T hc hp lam
        (compactResidualWeightOperator T hc hp φ hlam hα hM hf (compactRegularizedSqrt T hc hp 0 z))‖ ≤
      ‖compactResidualWeightOperator T hc hp φ hlam hα hM hf z‖ := by
  let R := compactRegularizedInvSqrt T hc hp lam
  let S := compactRegularizedSqrt T hc hp 0
  let a := compactResidualWeightOperator T hc hp φ hlam hα hM hf
  have heq : R (a (S z)) = (S * R) (a z) := by
    apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
    ext i
    simp only [R, S, a, compactResidualWeightOperator, mul_apply_eq_comp,
      compactRegularizedSqrt_repr, compactRegularizedInvSqrt_repr T hc hp lam hlam,
      compactSpectralMultiplier_repr]
    ring
  change ‖R (a (S z))‖ ≤ ‖a z‖
  rw [heq]
  simpa only [one_mul] using (S * R).le_of_opNorm_le (embedded_population_root_factor_norm_le T hc hp hlam) (a z)

/-- The visible analytic Schur premise for this specific actual interaction
kernel. It states only a Schatten estimate for the constructed entrywise map;
no coefficient identity, reconstruction, or embedded prediction estimate is a
field of this proposition. -/
def InteractionKernelSchurBound (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (lam α : ℝ) (φ : ℝ → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hkernel : ∀ i j, ‖compactLogInteractionKernel TX T lam α φ i j‖ ≤ B)
    (p C : ℝ) : Prop :=
  ∀ d : HilbertSchmidtColumns (CompactSpectralIndex T) H,
    hsSchattenNorm (compactEigenbasis T hc hp.isSymmetric)
      (hsSchurMultiplier (compactEigenbasis TX hcX hpX.isSymmetric)
        (compactLogInteractionKernel TX T lam α φ) B hB hkernel d) p ≤
      C * hsSchattenNorm (compactEigenbasis T hc hp.isSymmetric) d p

/-- The actual embedded interaction estimate conditional on a visible global
Schur bound for its actual logarithmic kernel. The DOI recovery and both
regularized outside factors are theorems above, not additional premises. -/
theorem embedded_interaction_of_schur_bound (b : HilbertBasis ι ℝ H)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α B p C : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα : 0 ≤ α) (hp2 : 2 ≤ p) (hB : 0 ≤ B)
    (hkernel : ∀ i j, ‖compactLogInteractionKernel TX T lam α φ i j‖ ≤ B)
    (hSchur : InteractionKernelSchurBound TX T hcX hc hpX hp lam α φ B hB hkernel p C)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 4)
    (c : HilbertSchmidtColumns ι H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation T TX hc hcX hp hpX lam) (z : H) :
    ‖(compactRegularizedSqrt T hc hp 0 * compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h *
        compactRegularizedSqrt T hc hp 0) z‖ ≤
      Real.sqrt 2 * C * hsSchattenNorm b c p * ‖compactResidualWeightOperator T hc hp φ hlam hα hM hf z‖ := by
  let S := compactRegularizedSqrt T hc hp 0
  let R := compactRegularizedInvSqrt T hc hp lam
  let RX := compactRegularizedInvSqrt TX hcX hpX lam
  let QX := compactRegularizedSqrt TX hcX hpX lam
  let a := compactResidualWeightOperator T hc hp φ hlam hα hM hf
  let G := compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h
  let bT := compactEigenbasis T hc hp.isSymmetric
  let Aop := hilbertSchmidtOperator bT (embeddedInteractionDOIColumns b TX T hcX hc hpX hp lam α φ B hB hkernel c)
  let w := R (a (S z))
  have hAnorm : ‖Aop‖ ≤ C * hsSchattenNorm b c p :=
    embeddedInteractionDOI_norm_le_of_schur b TX T hcX hc hpX hp lam α φ hB hkernel hp2 hSchur c
  have hCS : 0 ≤ C * hsSchattenNorm b c p := (norm_nonneg Aop).trans hAnorm
  have hid : Aop * R * a = QX * G := embeddedInteractionDOI_represents b TX T hcX hc hpX hp φ
    hlam hMX hM hf h hα hB hkernel c hcK
  have hG : G = RX * Aop * R * a := by
    have hundo : RX * (QX * G) = G := by
      rw [← mul_assoc, show RX * QX = 1 from compactRegularizedInvSqrt_mul_sqrt TX hcX hpX lam hlam,
        one_mul]
    have he := congrArg (fun F : H →L[ℝ] H => RX * F) hid
    rw [hundo] at he
    simpa only [mul_assoc] using he.symm
  have hleft : ‖S * RX‖ ≤ Real.sqrt 2 := embedded_empirical_root_factor_norm_le TX T hcX hc hpX hp hlam hδ
  have hw : ‖w‖ ≤ ‖a z‖ := embedded_weighted_right_vector_norm_le T hc hp φ hlam hα hM hf z
  change ‖(S * G * S) z‖ ≤ _
  rw [hG]
  change ‖(S * RX) (Aop w)‖ ≤ _
  calc
    _ ≤ Real.sqrt 2 * ‖Aop w‖ := (S * RX).le_of_opNorm_le hleft _
    _ ≤ Real.sqrt 2 * ((C * hsSchattenNorm b c p) * ‖w‖) :=
      mul_le_mul_of_nonneg_left (Aop.le_of_opNorm_le hAnorm w) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * ((C * hsSchattenNorm b c p) * ‖a z‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hCS) (Real.sqrt_nonneg _)
    _ = _ := by ring

section Prediction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual supported prediction version of the embedded-interaction
estimate. The prediction Hilbert space is arbitrary; no `L²` separability or
polar-factor premise is imposed. The only analytic leaf is the visible Schur
bound for the actual normalized logarithmic kernel. -/
theorem embedded_prediction_of_schur_bound (b : HilbertBasis ι ℝ H)
    (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    (TX : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hpX : TX.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α B p C : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖S.adjoint.comp S‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα : 0 ≤ α) (hp2 : 2 ≤ p) (hB : 0 ≤ B)
    (hkernel : ∀ i j, ‖compactLogInteractionKernel TX (S.adjoint.comp S) lam α φ i j‖ ≤ B)
    (hSchur : InteractionKernelSchurBound TX (S.adjoint.comp S) hcX hc hpX
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam α φ B hB hkernel p C)
    (hδ : ‖realNormalizedPerturbation (S.adjoint.comp S) TX hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam‖ ≤ 1 / 4)
    (c : HilbertSchmidtColumns ι H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation (S.adjoint.comp S) TX hc hcX
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) hpX lam)
    (f : E) (hsupport : f ∈ (S.comp S.adjoint).range.topologicalClosure) :
    ‖S (compactInteraction TX (S.adjoint.comp S) hcX hc hpX
        (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h (S.adjoint f))‖ ≤
      Real.sqrt 2 * C * hsSchattenNorm b c p *
        ‖compactResidualWeightOperator (S.comp S.adjoint)
          (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
          (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα
          ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf f‖ := by
  have hfRange : f ∈ PredictionRange S := by
    simpa only [closure_range_self_comp_adjoint S] using hsupport
  let fs : PredictionRange S := ⟨f, hfRange⟩
  let G := compactInteraction TX (S.adjoint.comp S) hcX hc hpX
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h
  have hb := embedded_interaction_of_schur_bound b TX (S.adjoint.comp S) hcX hc hpX
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h hα hp2 hB hkernel hSchur
    hδ c hcK (supportedPolarIsometry S hc fs)
  simp only [mul_apply_eq_comp] at hb
  have hnorm := prediction_interaction_norm_eq S hc G fs
  have hweight := prediction_residualWeight_norm_eq S hc φ hlam hα hM
    ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf fs
  rw [← hnorm, ← hweight] at hb
  exact hb

end Prediction

section ActualFeature

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual sampled RKHS embedded-interaction estimate. Mixed HS columns
and their reconstruction are the already constructed sample quantities, not
premises supplied to this theorem. No sample law or independence is needed
for this pointwise deterministic operator estimate. -/
theorem actual_embedded_prediction_of_schur_bound (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A α B p C : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    {n : ℕ} (x : Fin n → X) (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα : 0 ≤ α) (hp2 : 2 ≤ p) (hB : 0 ≤ B)
    (hkernel : ∀ i j, ‖compactLogInteractionKernel (empiricalCovariance (fun i => k (x i)))
      (populationCovariance (featureEmbedding μ k hk)) lam α φ i j‖ ≤ B)
    (hSchur : InteractionKernelSchurBound (empiricalCovariance (fun i => k (x i)))
      (populationCovariance (featureEmbedding μ k hk)) (empiricalCovariance_isCompact _)
      (populationCovariance_feature_isCompact μ k hk) (empiricalCovariance_isPositive _)
      (populationCovariance_isPositive _) lam α φ B hB hkernel p C)
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4)
    (f : Lp ℝ 2 μ) (hsupport : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure) :
    ‖actualInteractionPrediction k hk φ hlam hM x hMX hf h f‖ ≤
      Real.sqrt 2 * C * hsSchattenNorm b (manuscriptMixedColumns b k hk lam x) p *
        ‖actualBiasWeight k hk φ hlam hα hM hf f‖ := by
  exact embedded_prediction_of_schur_bound b (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) (empiricalCovariance (fun i => k (x i)))
    (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX hM hf h
    hα hp2 hB hkernel hSchur hδ (manuscriptMixedColumns b k hk lam x)
    (hilbertSchmidtOperator_manuscriptMixedColumns b k hk lam hlam x) f hsupport

end ActualFeature

end
end KernelSeq
