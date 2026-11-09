import KernelSeq.PolynomialKernelEnergy
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Exact quadratic energy series for the original positive power-series kernel

The finite tensor expansion and a genuine dominated-convergence argument
identify the whole quadratic form with its convergent nonnegative degree
series. No quadratic-form representation or zero-energy certificate is an
assumption.
-/

namespace KernelSeq
open MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

theorem powerSeries_kernel_energy_hasSum {μ : Measure X} [SFinite μ]
    (z : X → EuclideanSpace ℝ ι) (hz : Measurable z) (hunit : ∀ x, ‖z x‖ ≤ 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasSum (fun j => a j * t ^ j) (Φ t))
    {f : X → ℝ} (hf : Integrable f μ) :
    HasSum (fun m => a m * tensorMomentEnergy μ z m f)
      (∫ p : X × X, f p.1 * f p.2 * Φ (inner ℝ (z p.1) (z p.2)) ∂μ.prod μ) := by
  classical
  have hs : Summable a := by
    simpa only [one_pow, mul_one] using (hseries 1 (by norm_num)).summable
  have hinner (p : X × X) : ‖inner ℝ (z p.1) (z p.2)‖ ≤ 1 :=
    (norm_inner_le_norm _ _).trans (by
      nlinarith [hunit p.1, hunit p.2, norm_nonneg (z p.1), norm_nonneg (z p.2)])
  have him : Measurable (fun p : X × X => inner ℝ (z p.1) (z p.2)) :=
    (hz.comp measurable_fst).inner (hz.comp measurable_snd)
  let F : ℕ → X × X → ℝ := fun n p =>
    f p.1 * f p.2 * ∑ j ∈ Finset.range n, a j * inner ℝ (z p.1) (z p.2) ^ j
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) (μ.prod μ) :=
    (hf.mul_prod hf).1.mul ((Finset.measurable_sum _ fun j _ =>
      measurable_const.mul (him.pow_const j)).aestronglyMeasurable)
  have hdom (n : ℕ) (p : X × X) : ‖F n p‖ ≤
      (∑' j, a j) * (‖f p.1‖ * ‖f p.2‖) := by
    have hpart : ‖∑ j ∈ Finset.range n, a j * inner ℝ (z p.1) (z p.2) ^ j‖ ≤ ∑' j, a j := by
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum fun j _ => ?_).trans (hs.sum_le_tsum _ fun j _ => ha j)
      rw [norm_mul, Real.norm_of_nonneg (ha j), norm_pow]
      exact mul_le_of_le_one_right (ha j) (pow_le_one₀ (norm_nonneg _) (hinner p))
    simpa only [F, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hpart (mul_nonneg (norm_nonneg (f p.1)) (norm_nonneg (f p.2)))
  have hlim := tendsto_integral_of_dominated_convergence
    (fun p : X × X => (∑' j, a j) * (‖f p.1‖ * ‖f p.2‖)) hmeas
    ((hf.norm.mul_prod hf.norm).const_mul (∑' j, a j))
    (fun n => Eventually.of_forall (hdom n)) (f := fun p =>
      f p.1 * f p.2 * Φ (inner ℝ (z p.1) (z p.2))) (by
      apply Eventually.of_forall
      intro p
      have ht : inner ℝ (z p.1) (z p.2) ∈ Set.Icc (-1 : ℝ) 1 := by
        simpa only [Set.mem_Icc, Real.norm_eq_abs, abs_le] using hinner p
      exact tendsto_const_nhds.mul (hseries _ ht).tendsto_sum_nat)
  have heq (n : ℕ) : (∫ p : X × X, F n p ∂μ.prod μ) =
      ∑ j ∈ Finset.range n, a j * tensorMomentEnergy μ z j f := by
    have hint (j : ℕ) := (integrable_tensor_kernel z hz hunit hf j).const_mul (a j)
    dsimp [F]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      calc
        _ = a j * ∫ p : X × X,
            f p.1 * f p.2 * inner ℝ (z p.1) (z p.2) ^ j ∂μ.prod μ := by
          rw [← integral_const_mul]
          congr 1; ext p; ring
        _ = _ := by rw [integral_tensor_kernel_eq_momentEnergy z hz hunit hf]
    · intro j _
      convert hint j using 1
      ext p
      ring
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun j => mul_nonneg (ha j) (tensorMomentEnergy_nonneg _ _ _ _)) _).mpr
  exact hlim.congr' (Eventually.of_forall heq)

section Feature
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

theorem featureAdjoint_powerSeries_energy_hasSum (k : X → H) (hk : MemLp k 2 μ)
    (z : X → EuclideanSpace ℝ ι) (hz : Measurable z) (hunit : ∀ x, ‖z x‖ ≤ 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = Φ (inner ℝ (z x) (z y)))
    (f : Lp ℝ 2 μ) :
    HasSum (fun m => a m*tensorMomentEnergy μ z m f) (‖(featureEmbedding μ k hk).adjoint f‖^2) := by
  rw [featureAdjoint_norm_sq_eq_kernel_integral]
  simp_rw [hkernel]
  exact powerSeries_kernel_energy_hasSum z hz hunit a ha Φ hseries
    ((Lp.memLp f).integrable (by norm_num))

end Feature
end
end KernelSeq
