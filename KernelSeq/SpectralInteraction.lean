import KernelSeq.SpectralRHS
import KernelSeq.EmpiricalSpectral
import KernelSeq.MixedPerturbation
import KernelSeq.FilterDimension
import Mathlib.Tactic.NoncommRing

/-!
# Actual interaction and the empirical bias-error decomposition

The operator decomposition for bias transfer uses the real compact
spectral calculus for both covariance filters.
The localized interaction bound is a separate obligation.
-/

open MeasureTheory

namespace KernelSeq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual residual multiplier equals identity minus covariance times
filter, including the zero eigenspace and a possibly discontinuous filter. -/
theorem compactResidualOperator_eq_one_sub_mul_filter (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    compactResidualOperator T hc hp φ hM hf =
      1 - T * compactFilterOperator T hc hp φ hlam hM h := by
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [compactResidualOperator, compactFilterOperator, _root_.sub_apply,
    one_apply_eq_self, mul_apply_eq_comp, map_sub, lp.coeFn_sub, Pi.sub_apply,
    compactSpectralMultiplier_repr,
    compactEigenbasis_repr_apply, ResidualFilter.residual, ResidualFilter.shrinkage]
  ring

/-- The same residual identity with the commuting spectral filter on the
left. The equality is proved in the actual eigenbasis. -/
theorem compactResidualOperator_eq_one_sub_filter_mul (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    compactResidualOperator T hc hp φ hM hf =
      1 - compactFilterOperator T hc hp φ hlam hM h * T := by
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [compactResidualOperator, compactFilterOperator, _root_.sub_apply,
    one_apply_eq_self, mul_apply_eq_comp, map_sub, lp.coeFn_sub, Pi.sub_apply,
    compactSpectralMultiplier_repr,
    compactEigenbasis_repr_apply, ResidualFilter.residual, ResidualFilter.shrinkage]
  ring

/-- The paper's actual interaction operator `G`, without assuming two
covariance operators commute. -/
noncomputable def compactInteraction (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) : H →L[ℝ] H :=
  compactFilterOperator TX hcX hpX φ hlam hMX h * compactResidualOperator T hc hp φ hM hf -
    compactResidualOperator TX hcX hpX φ hMX hf * compactFilterOperator T hc hp φ hlam hM h

/-- The interaction has exactly the algebraic expression used in the
empirical RHS decomposition. No divided-difference certificate is supplied. -/
theorem compactInteraction_eq (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h =
      compactFilterOperator TX hcX hpX φ hlam hMX h * (TX - T) *
        compactFilterOperator T hc hp φ hlam hM h +
      compactFilterOperator TX hcX hpX φ hlam hMX h - compactFilterOperator T hc hp φ hlam hM h := by
  rw [compactInteraction, compactResidualOperator_eq_one_sub_mul_filter T hc hp φ hlam hM hf h,
    compactResidualOperator_eq_one_sub_filter_mul TX hcX hpX φ hlam hMX hf h]
  noncomm_ring

section ActualFeature

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Exact empirical mean-minus-population solution decomposition from the
actual sample RHS. This holds pointwise for the selected `L²` representative. -/
theorem spectral_estimator_error_decomposition (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    {n : ℕ} (x : Fin n → X) (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) :
    compactFilterOperator (empiricalCovariance (fun i => k (x i)))
        (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX h
        (empiricalRepresenter (fun i => k (x i)) (fun i => f (x i))) -
      populationSpectralSolution k hk φ hlam hM h f =
    compactFilterOperator (empiricalCovariance (fun i => k (x i)))
        (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX h
        (rhsFluctuation k hk f (populationSpectralSolution k hk φ hlam hM h f) x) +
      compactInteraction (empiricalCovariance (fun i => k (x i)))
        (populationCovariance (featureEmbedding μ k hk))
        (empiricalCovariance_isCompact _) (populationCovariance_feature_isCompact μ k hk)
        (empiricalCovariance_isPositive _) (populationCovariance_isPositive _) φ hlam hMX hM hf h
        ((featureEmbedding μ k hk).adjoint f) := by
  rw [compactInteraction_eq]
  simp only [rhsFluctuation, populationSpectralSolution, map_sub, _root_.add_apply,
    _root_.sub_apply, mul_apply_eq_comp]
  abel

end ActualFeature

end KernelSeq
