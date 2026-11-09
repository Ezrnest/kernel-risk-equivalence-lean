import KernelSeq.SequenceBenchmark
import KernelSeq.OriginalScaleParameters
import Mathlib.Data.Set.Card

/-!
# Population spectral counts and the qualification lower bound

The counts use the actual positive covariance spectrum with multiplicities.
Their finiteness follows from the proved covariance trace. The filter lower
bound in `subsubsec:interpolation-regime` and the scale-verification proofs is
derived from the original residual contract, rather than assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelSeq
noncomputable section

namespace ResidualFilter

def resolvedScaleFactor (ρ A : ℝ) : ℝ := (2 * (A + 1)) ^ (1 / ρ)

theorem resolvedScaleFactor_pos {ρ A : ℝ} (hA : 0 ≤ A) :
    0 < resolvedScaleFactor ρ A :=
  Real.rpow_pos_of_pos (by positivity) _

/-- Every population coordinate sufficiently above the regularization scale
retains at least one half. The threshold depends only on the original constants. -/
theorem Contract.resolved_shrinkage_ge_half {lam M ρ A t : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M)
    (hresolved : lam * resolvedScaleFactor ρ A ≤ t) :
    (1 / 2 : ℝ) ≤ shrinkage φ t := by
  have hA := h.constant_nonneg hlam (ht.1.trans ht.2)
  have hc := resolvedScaleFactor_pos (ρ := ρ) hA
  have ht0 : 0 < t := (mul_pos hlam hc).trans_le hresolved
  have hcPow : resolvedScaleFactor ρ A ^ ρ = 2 * (A + 1) := by
    unfold resolvedScaleFactor
    rw [one_div, Real.rpow_inv_rpow (by positivity) h.rho_pos.ne']
  have hpow := Real.rpow_le_rpow (mul_nonneg hlam.le hc.le) hresolved h.rho_pos.le
  rw [Real.mul_rpow hlam.le hc.le, hcPow] at hpow
  have hqual := h.qualification hlam ht h.rho_pos.le le_rfl
  have hp : 0 < lam ^ ρ := Real.rpow_pos_of_pos hlam _
  have habs : |residual φ t| ≤ 1 / 2 := by
    have hprod := (mul_le_mul_of_nonneg_right hpow (abs_nonneg (residual φ t))).trans hqual
    have hcancel : 2 * (A + 1) * |residual φ t| ≤ A := by
      apply (mul_le_mul_iff_right₀ hp).mp
      convert hprod using 1 <;> ring
    by_contra hnot
    have hbad := mul_lt_mul_of_pos_left (lt_of_not_ge hnot)
      (by positivity : 0 < 2 * (A + 1))
    nlinarith
  have hr := (le_abs_self (residual φ t)).trans habs
  unfold residual at hr
  linarith

end ResidualFilter

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The population eigenvalue counting function, retaining multiplicities.
Only positive thresholds are used below. -/
def featureSpectralCount (k : X → H) (hk : MemLp k 2 μ) (t : ℝ) : ℕ :=
  {i : PredictionSingularIndex (featureEmbedding μ k hk) | t ≤ i.1.1}.ncard

theorem summable_positive_covariance_eigenvalues (k : X → H) (hk : MemLp k 2 μ) :
    Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) => i.1.1) :=
  (summable_featureCovarianceEigenvalues k hk).subtype _

theorem finite_featureSpectrum_above (k : X → H) (hk : MemLp k 2 μ)
    {t : ℝ} (ht : 0 < t) :
    {i : PredictionSingularIndex (featureEmbedding μ k hk) | t ≤ i.1.1}.Finite := by
  have he := (summable_positive_covariance_eigenvalues k hk).tendsto_cofinite_zero.eventually
    (gt_mem_nhds ht)
  change {i : PredictionSingularIndex (featureEmbedding μ k hk) | i.1.1 < t} ∈ cofinite at he
  simpa only [Set.compl_setOf, not_lt] using (mem_cofinite.mp he)

/-- The exact quarter-count lower bound used in the original scale examples
and interpolation discussion. No eigenvalue-count estimate is an input. -/
theorem quarter_mul_featureSpectralCount_le_filterDimension
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ}
    (hlam : 0 < lam) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    (1 / 4 : ℝ) * featureSpectralCount k hk
      (lam * ResidualFilter.resolvedScaleFactor ρ A) ≤ featureFilterDimension k hk φ := by
  classical
  have hA := h.constant_nonneg hlam ((norm_nonneg _).trans hM)
  have ht := mul_pos hlam (ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA)
  let s := (finite_featureSpectrum_above k hk ht).toFinset
  have hcard : (featureSpectralCount k hk
      (lam * ResidualFilter.resolvedScaleFactor ρ A) : ℝ) = s.card := by
    simp only [featureSpectralCount,
      Set.ncard_eq_toFinset_card _ (finite_featureSpectrum_above k hk ht), s]
  rw [hcard, featureFilterDimension_eq_positive_sequence]
  calc
    (1 / 4 : ℝ) * (s.card : ℝ) = ∑ _i ∈ s, (1 / 4 : ℝ) := by simp; ring
    _ ≤ ∑ i ∈ s, ResidualFilter.shrinkage φ i.1.1 ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hire : lam * ResidualFilter.resolvedScaleFactor ρ A ≤ i.1.1 := by
        simpa only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hi
      have hq := h.resolved_shrinkage_ge_half hlam
        (featureCovarianceEigenvalue_mem k hk hM i.1) hire
      nlinarith [sq_nonneg (ResidualFilter.shrinkage φ i.1.1 - 1 / 2)]
    _ ≤ ∑' i : PredictionSingularIndex (featureEmbedding μ k hk),
        ResidualFilter.shrinkage φ i.1.1 ^ 2 :=
      (summable_positive_sequence_filterDimension k hk φ hlam hM hf h).sum_le_tsum
        s (fun _ _ => sq_nonneg _)

end
end KernelSeq
