import KernelSeq.TriangularRiskScales

/-!
# Actual bad-design probabilities for arbitrary regression rows

Every covariance tail is applied inside its own row probability space. The
original compatibility scale makes the fixed-quarter bad probability vanish
along any row filter, without an expectation-scale hypothesis.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

universe uH uX uΩ
namespace TriangularRiskModel
variable {κ ρ A : ℝ} (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A)

theorem badProbability_bound (hQ : 0 < m.Q)
    (hsmall : m.L * intrinsicDimensionLog m.N m.r / (m.n : ℝ) ≤ 1 / 65536) :
    m.P.real m.goodEventᶜ ≤ 8 * Real.exp (-(1 / 65536 : ℝ) * (m.n : ℝ) / m.L) := by
  have ht := actual_bad_design_exponential_tail m.feature m.feature_memLp m.lambda_pos
    m.sample_pos m.design m.design_law m.design_independent m.leverage_ae (m.r_pos hQ) hsmall
  have hc : m.goodEventᶜ = {ω | 1 / 4 < actualCovarianceDeviation m.feature m.feature_memLp
      m.lam (fun j => m.design j ω)} := by
    ext ω
    simp only [goodEvent, deviation, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have he : -(m.n : ℝ) / (65536 * m.L) = -(1 / 65536 : ℝ) * (m.n : ℝ) / m.L := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at ht
  rw [hc]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ht).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

end TriangularRiskModel

variable {J : Type*} {l : Filter J} {κ ρ A : ℝ}

/-- The exponential factor itself vanishes under variance compatibility. -/
theorem triangular_covariance_exponential_tendsto_zero
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0)) :
    Tendsto (fun i => 8 * Real.exp (-(1 / 65536 : ℝ) * ((m i).n : ℝ) / (m i).L)) l (𝓝 0) := by
  have hLn := (triangular_variance_scale_limits m hQ hc).2.1
  have ht := expectation_scale_polynomial_tail (fun i => (m i).L) (fun i => ((m i).n : ℝ))
    (fun _ => 0) (hQ.mono fun i hi => (m i).L_pos hi)
    (Eventually.of_forall fun i => Nat.cast_pos.mpr (m i).sample_pos)
    (Eventually.of_forall fun _ => le_rfl)
    (by simpa only [add_zero, Real.log_exp, mul_one] using hLn)
    (a := 0) (by norm_num) (c := (1 / 65536 : ℝ)) (by norm_num)
  simpa only [add_zero, Real.one_rpow, one_mul, mul_zero] using ht.const_mul 8

theorem triangular_bad_probability_tendsto_zero
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0)) :
    Tendsto (fun i => (m i).P.real (m i).goodEventᶜ) l (𝓝 0) := by
  have hs := triangular_eventually_small m hQ hc
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _
    (triangular_covariance_exponential_tendsto_zero m hQ hc)
  filter_upwards [hQ, hs] with i hi hsi
  exact (m i).badProbability_bound hi hsi.2.2.1

/-- The original expectation scale controls every fixed polynomial in the
actual reciprocal regularization/dimension scale, even as models vary. -/
theorem triangular_expectation_polynomial_tail
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (he : Tendsto (fun i => (m i).expectationScale) l (𝓝 0))
    {p : ℝ} (hp : 0 ≤ p) :
    Tendsto (fun i => (1 + (m i).expectationH) ^ p *
      Real.exp (-(1 / 65536 : ℝ) * ((m i).n : ℝ) / (m i).L)) l (𝓝 0) :=
  expectation_scale_polynomial_tail (fun i => (m i).L) (fun i => ((m i).n : ℝ))
    (fun i => (m i).expectationH) (hQ.mono fun i hi => (m i).L_pos hi)
    (Eventually.of_forall fun i => Nat.cast_pos.mpr (m i).sample_pos)
    (hQ.mono fun i hi => ((m i).expectationH_pos hi).le) he hp (by norm_num)

end
end KernelSeq
