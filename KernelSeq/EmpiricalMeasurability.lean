import KernelSeq.ContinuousCompactCalculus
import KernelSeq.SpectralEnergy
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Design measurability of the actual empirical spectral estimator

Only the manuscript's residual-only contract is used. Shrinkage `q = t φ` is
continuous even when the inverse profile is discontinuous at zero. On vectors
orthogonal to the empirical kernel, `(T + εI)⁻¹ q(T) v` converges to `φ(T) v`.
This proves design strong measurability by limits of actual measurable maps.
-/

open MeasureTheory Filter Topology LinearMap Module.End
open scoped BigOperators

namespace KernelSeq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Resolvent regularization recovers the true filter on the kernel complement.
The proof uses actual spectral coordinates, Parseval, and dominated series
convergence; it does not assume a spectral-limit certificate. -/
theorem compactFilter_resolvent_approx_tendsto (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (v : H) (hker : ∀ z, T z = 0 → inner ℝ z v = 0) :
    Tendsto (fun n : ℕ => Ring.inverse (T + (1 / ((n : ℝ) + 1)) • (1 : H →L[ℝ] H))
      (compactShrinkageOperator T hc hp φ hM hf v)) atTop
        (𝓝 (compactFilterOperator T hc hp φ hlam hM h v)) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let b := compactEigenbasis T hc hp.isSymmetric
  let z : ℕ → H := fun n => Ring.inverse (T + ε n • (1 : H →L[ℝ] H))
    (compactShrinkageOperator T hc hp φ hM hf v) - compactFilterOperator T hc hp φ hlam hM h v
  have hcoeff (n : ℕ) (i : CompactSpectralIndex T) :
      b.repr (z n) i = -(ε n / (i.1 + ε n)) * φ i.1 * b.repr v i := by
    dsimp only [z, b]
    simp only [map_sub, lp.coeFn_sub, Pi.sub_apply,
      compact_regularizedInverse_repr T hc hp (ε n) (hε n), compactShrinkageOperator_repr,
      compactFilterOperator_repr, ResidualFilter.shrinkage]
    have hd : i.1 + ε n ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos
      (compactEigenvalue_nonneg T hc hp i) (hε n))
    field_simp
    ring
  have hA : 0 ≤ A / lam := div_nonneg
    (h.constant_nonneg hlam ((norm_nonneg T).trans hM)) hlam.le
  have hbound (n : ℕ) (i : CompactSpectralIndex T) :
      ‖b.repr (z n) i ^ 2‖ ≤ (A / lam) ^ 2 * b.repr v i ^ 2 := by
    have ht := compactEigenvalue_nonneg T hc hp i
    have hd := add_pos_of_nonneg_of_pos ht (hε n)
    have hfrac0 : 0 ≤ ε n / (i.1 + ε n) := div_nonneg (hε n).le hd.le
    have hfrac1 : ε n / (i.1 + ε n) ≤ 1 := (div_le_one hd).mpr (by linarith)
    have hsfrac : (ε n / (i.1 + ε n)) ^ 2 ≤ 1 := by nlinarith
    have hφ : |φ i.1| ≤ A / lam := h.profile_bound hlam ⟨ht,
      ((le_abs_self i.1).trans (compactEigenvalue_norm_le T hc hp.isSymmetric i)).trans hM⟩
    have hsφ : φ i.1 ^ 2 ≤ (A / lam) ^ 2 := by
      nlinarith [sq_abs (φ i.1), abs_nonneg (φ i.1)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hcoeff]
    calc
      _ = (ε n / (i.1 + ε n)) ^ 2 * φ i.1 ^ 2 * b.repr v i ^ 2 := by ring
      _ ≤ 1 * (A / lam) ^ 2 * b.repr v i ^ 2 := by gcongr
      _ = _ := by ring
  have hpoint (i : CompactSpectralIndex T) :
      Tendsto (fun n => b.repr (z n) i ^ 2) atTop (𝓝 (0 : ℝ)) := by
    by_cases hi : i.1 = 0
    · have hc0 : b.repr v i = 0 := by
        rw [HilbertBasis.repr_apply_apply]
        apply hker
        rw [compactEigenbasis_eigen, hi, zero_smul]
      simpa only [hcoeff, hc0, mul_zero, zero_pow (by decide : 2 ≠ 0)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have hratio : Tendsto (fun n => ε n / (i.1 + ε n)) atTop (𝓝 (0 : ℝ)) := by
        simpa only [Pi.div_def, add_zero, zero_div] using
          hεlim.div (tendsto_const_nhds.add hεlim) (by simpa only [add_zero] using hi)
      simpa only [hcoeff, neg_zero, zero_mul, zero_pow (by decide : 2 ≠ 0)] using
        ((hratio.neg.mul_const (φ i.1)).mul_const (b.repr v i)).pow 2
  have hseries := tendsto_tsum_of_dominated_convergence
    ((hilbertBasis_coefficients_sq_summable b v).mul_left ((A / lam) ^ 2))
    hpoint (Eventually.of_forall hbound)
  have hsquare : Tendsto (fun n => ‖z n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [← hilbertBasis_norm_sq_eq_tsum b, tsum_zero] using hseries
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, z, ε] using hnorm

/-- The true filter applied to a strongly measurable kernel-free vector family
is strongly measurable under the original filter assumptions. -/
theorem stronglyMeasurable_compactFilterOperator_apply
    {Ω : Type*} [MeasurableSpace Ω] (T : Ω → H →L[ℝ] H)
    (hT : StronglyMeasurable T) (hc : ∀ ω, IsCompactOperator (T ω))
    (hp : ∀ ω, (T ω).IsPositive) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ∀ ω, ‖T ω‖ ≤ M) (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) (v : Ω → H) (hv : StronglyMeasurable v)
    (hker : ∀ ω z, T ω z = 0 → inner ℝ z (v ω) = 0) :
    StronglyMeasurable (fun ω => compactFilterOperator (T ω) (hc ω) (hp ω) φ hlam (hM ω) h (v ω)) := by
  have hQ := stronglyMeasurable_compactShrinkageOperator T hT hc hp hlam hM φ hf h
  have hQv := stronglyMeasurable_operator_apply _ hQ v hv
  apply stronglyMeasurable_of_tendsto atTop
    (fun n : ℕ => stronglyMeasurable_operator_apply _
      (stronglyMeasurable_regularizedInverse T hT hp (1 / ((n : ℝ) + 1)) (by positivity)) _ hQv)
  apply tendsto_pi_nhds.mpr
  intro ω
  exact compactFilter_resolvent_approx_tendsto (T ω) (hc ω) (hp ω) φ hlam (hM ω) hf h (v ω) (hker ω)

section Empirical

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A sample feature is automatically kernel-free; the final filtered sample
vector's measurability is proved, rather than an additional premise. -/
theorem stronglyMeasurable_empiricalFilter_sample {n : ℕ} (hn : 0 < n)
    (v : Fin n → Ω → H) (hv : ∀ i, StronglyMeasurable (v i)) (κ : ℝ)
    (hbound : ∀ ω i, ‖v i ω‖ ^ 2 ≤ κ ^ 2) (φ : ℝ → ℝ) {lam ρ A : ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) :
    StronglyMeasurable (fun ω => empiricalFilterOperator hn (fun j => v j ω) κ (hbound ω) φ hlam h (v i ω)) := by
  apply stronglyMeasurable_compactFilterOperator_apply
    (fun ω => empiricalCovariance (fun j => v j ω))
    (stronglyMeasurable_empiricalCovariance v hv)
    (fun ω => empiricalCovariance_isCompact (fun j => v j ω))
    (fun ω => empiricalCovariance_isPositive (fun j => v j ω)) hlam
    (fun ω => norm_empiricalCovariance_le_bound hn _ κ (hbound ω)) φ hf h (v i) (hv i)
  intro ω z hz
  exact (real_inner_comm (v i ω) z).trans
    (sample_inner_eq_zero_of_empiricalCovariance_eq_zero hn (fun j => v j ω) hz i)

/-- Design/response strong measurability of the actual empirical spectral
estimator, including inverse profiles discontinuous at zero. -/
theorem stronglyMeasurable_empiricalSpectralEstimator {n : ℕ} (hn : 0 < n)
    (v : Fin n → Ω → H) (hv : ∀ i, StronglyMeasurable (v i)) (κ : ℝ)
    (hbound : ∀ ω i, ‖v i ω‖ ^ 2 ≤ κ ^ 2) (y : Fin n → Ω → ℝ)
    (hy : ∀ i, StronglyMeasurable (y i)) (φ : ℝ → ℝ) {lam ρ A : ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    StronglyMeasurable (fun ω => empiricalSpectralEstimator hn (fun j => v j ω) κ
      (hbound ω) (fun j => y j ω) φ hlam h) := by
  have hs := (Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    (hy i).smul (stronglyMeasurable_empiricalFilter_sample hn v hv κ hbound φ hlam hf h i))).const_smul (n : ℝ)⁻¹
  convert hs using 1
  funext ω
  simp only [empiricalSpectralEstimator, empiricalRepresenter, map_smul, map_sum, Pi.smul_apply]

theorem stronglyMeasurable_empiricalPredictionCoefficient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : H →L[ℝ] E)
    {n : ℕ} (hn : 0 < n) (v : Fin n → Ω → H) (hv : ∀ i, StronglyMeasurable (v i))
    (κ : ℝ) (hbound : ∀ ω i, ‖v i ω‖ ^ 2 ≤ κ ^ 2) (φ : ℝ → ℝ) {lam ρ A : ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) :
    StronglyMeasurable (fun ω => empiricalPredictionCoefficient S hn (fun j => v j ω) κ
      (hbound ω) φ hlam h i) := by
  have hs := (S.continuous.comp_stronglyMeasurable
    (stronglyMeasurable_empiricalFilter_sample hn v hv κ hbound φ hlam hf h i)).const_smul (n : ℝ)⁻¹
  convert hs using 1
  rfl

omit [MeasurableSpace Ω] in
/-- The actual conditional-risk noise coefficients are strongly measurable for
the sigma-algebra generated by all design coordinates. -/
theorem observation_empiricalPredictionCoefficient_design_stronglyMeasurable
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : H →L[ℝ] E) {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ)
    (k : X → H) (hk : StronglyMeasurable k) (κ : ℝ)
    (hbound : ∀ z, ‖k z‖ ^ 2 ≤ κ ^ 2) (φ : ℝ → ℝ) {lam ρ A : ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) :
    StronglyMeasurable[⨆ j, observationDesignSigma (Z j)]
      (fun ω => empiricalPredictionCoefficient S hn (fun j => k ((Z j ω).1)) κ
        (fun j => hbound ((Z j ω).1)) φ hlam h i) := by
  letI : MeasurableSpace Ω := ⨆ j, observationDesignSigma (Z j)
  exact stronglyMeasurable_empiricalPredictionCoefficient S hn _
    (observation_feature_design_stronglyMeasurable Z k hk) κ
    (fun ω j => hbound ((Z j ω).1)) φ hlam hf h i

omit [MeasurableSpace Ω] in
/-- The filtered noiseless sample representer is design strongly measurable
for the original filter class. -/
theorem observation_empiricalMeanEstimator_design_stronglyMeasurable
    {X : Type*} [MeasurableSpace X] {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ)
    (k : X → H) (hk : StronglyMeasurable k) (κ : ℝ)
    (hbound : ∀ z, ‖k z‖ ^ 2 ≤ κ ^ 2) (f : X → ℝ) (hfm : Measurable f)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ) (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    StronglyMeasurable[⨆ j, observationDesignSigma (Z j)]
      (fun ω => empiricalSpectralEstimator hn (fun j => k ((Z j ω).1)) κ
        (fun j => hbound ((Z j ω).1)) (fun j => f ((Z j ω).1)) φ hlam h) := by
  letI : MeasurableSpace Ω := ⨆ j, observationDesignSigma (Z j)
  apply stronglyMeasurable_empiricalSpectralEstimator hn _
    (observation_feature_design_stronglyMeasurable Z k hk) κ (fun ω j => hbound ((Z j ω).1))
    (fun j ω => f ((Z j ω).1)) _ φ hlam hf h
  intro i
  exact (hfm.comp (Measurable.of_comap_le
    (le_iSup (fun j => observationDesignSigma (Z j)) i))).stronglyMeasurable

/-- The observed-response estimator itself is strongly measurable for the
ambient observation sigma-algebra. -/
theorem observation_empiricalSpectralEstimator_stronglyMeasurable
    {X : Type*} [MeasurableSpace X] {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ)
    (hZ : ∀ i, Measurable (Z i)) (k : X → H) (hk : StronglyMeasurable k) (κ : ℝ)
    (hbound : ∀ z, ‖k z‖ ^ 2 ≤ κ ^ 2) (φ : ℝ → ℝ) {lam ρ A : ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    StronglyMeasurable (fun ω => empiricalSpectralEstimator hn (fun j => k ((Z j ω).1)) κ
      (fun j => hbound ((Z j ω).1)) (fun j => (Z j ω).2) φ hlam h) :=
  stronglyMeasurable_empiricalSpectralEstimator hn _
    (fun j => hk.comp_measurable (hZ j).fst) κ (fun ω j => hbound ((Z j ω).1))
    (fun j ω => (Z j ω).2) (fun j => (hZ j).snd.stronglyMeasurable) φ hlam hf h

end Empirical

end KernelSeq
