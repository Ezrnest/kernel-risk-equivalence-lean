import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.NormNum

/-!
# Second moments of centered Hilbert-valued sample averages

Second-moment identities for independent centered sums, used to control
right-hand-side and Hilbert–Schmidt covariance fluctuations.
The latter application still requires construction of the HS operator space.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace KernelSeq

variable {Ω H ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {P : Measure Ω}

/-- Inner products of two square-integrable Hilbert functions are integrable. -/
theorem integrable_inner_of_memLp {f g : Ω → H}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => inner ℝ (f ω) (g ω)) P := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  rw [hfω, hgω]

variable [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [IsFiniteMeasure P] [Fintype ι]

/-- Exact second-moment identity; pairwise independence is sufficient. -/
theorem integral_norm_sq_sum_of_indep (ξ : ι → Ω → H)
    (hξ : ∀ i, MemLp (ξ i) 2 P)
    (hindep : Pairwise (fun i j => IndepFun (ξ i) (ξ j) P))
    (hmean : ∀ i, (∫ ω, ξ i ω ∂P) = 0) :
    (∫ ω, ‖∑ i, ξ i ω‖ ^ 2 ∂P) = ∑ i, ∫ ω, ‖ξ i ω‖ ^ 2 ∂P := by
  classical
  have hint (i j : ι) := integrable_inner_of_memLp (hξ i) (hξ j)
  have hcross (i j : ι) (hij : i ≠ j) :
      (∫ ω, inner ℝ (ξ i ω) (ξ j ω) ∂P) = 0 := by
    have h := (hindep hij).integral_bilin (𝕜 := ℝ)
      ((hξ i).integrable (by norm_num)) ((hξ j).integrable (by norm_num)) (innerSL ℝ)
    change (∫ ω, inner ℝ (ξ i ω) (ξ j ω) ∂P) =
      inner ℝ (∫ ω, ξ i ω ∂P) (∫ ω, ξ j ω ∂P) at h
    simpa only [hmean, inner_zero_left] using h
  have hexpand (ω : Ω) : ‖∑ i, ξ i ω‖ ^ 2 =
      ∑ i, ∑ j, inner ℝ (ξ i ω) (ξ j ω) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  rw [Finset.sum_eq_single i]
  · simp only [real_inner_self_eq_norm_sq]
  · intro j _ hji
    exact hcross i j hji.symm
  · simp

/-- A centered sample average has the `1/n²` sum of second moments. -/
theorem integral_norm_sq_average_of_indep {n : ℕ} (ξ : Fin n → Ω → H)
    (hξ : ∀ i, MemLp (ξ i) 2 P)
    (hindep : Pairwise (fun i j => IndepFun (ξ i) (ξ j) P))
    (hmean : ∀ i, (∫ ω, ξ i ω ∂P) = 0) :
    (∫ ω, ‖(n : ℝ)⁻¹ • ∑ i, ξ i ω‖ ^ 2 ∂P) =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, ∫ ω, ‖ξ i ω‖ ^ 2 ∂P := by
  simp_rw [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, mul_pow]
  rw [integral_const_mul, integral_norm_sq_sum_of_indep ξ hξ hindep hmean]

end KernelSeq
