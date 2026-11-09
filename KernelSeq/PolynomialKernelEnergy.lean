import KernelSeq.PopulationCovariance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Actual quadratic energies of positive power-series kernels

The finite tensor expansion is integrated against the original design law.
Positive power-series coefficients then give a genuine population quadratic
lower bound, rather than an assumed spectral block estimate.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace KernelSeq
noncomputable section

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

def tensorMonomial (z : X → EuclideanSpace ℝ ι) (m : ℕ) (a : Fin m → ι) (x : X) : ℝ :=
  ∏ r, z x (a r)

def tensorMomentEnergy (μ : Measure X) (z : X → EuclideanSpace ℝ ι)
    (m : ℕ) (f : X → ℝ) : ℝ :=
  ∑ a : Fin m → ι, (∫ x, f x * tensorMonomial z m a x ∂μ) ^ 2

theorem tensorMomentEnergy_nonneg (μ : Measure X) (z : X → EuclideanSpace ℝ ι)
    (m : ℕ) (f : X → ℝ) : 0 ≤ tensorMomentEnergy μ z m f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [MeasurableSpace X] in
theorem inner_pow_eq_tensorMonomial (z : X → EuclideanSpace ℝ ι) (m : ℕ) (x y : X) :
    inner ℝ (z x) (z y) ^ m =
      ∑ a : Fin m → ι, tensorMonomial z m a x * tensorMonomial z m a y := by
  classical
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  calc
    (∑ i, z y i * z x i) ^ m = ∏ _ : Fin m, ∑ i, z y i * z x i := by simp
    _ = ∑ a : Fin m → ι, ∏ r, z y (a r) * z x (a r) := Fintype.prod_sum _
    _ = _ := by simp only [Finset.prod_mul_distrib, tensorMonomial, mul_comm]

omit [Fintype ι] in
theorem measurable_tensorMonomial (z : X → EuclideanSpace ℝ ι) (hz : Measurable z)
    (m : ℕ) (a : Fin m → ι) : Measurable (tensorMonomial z m a) := by
  classical
  exact Finset.measurable_prod _ fun r _ => (measurable_pi_apply (a r)).comp
    ((WithLp.measurable_ofLp 2 _).comp hz)

omit [MeasurableSpace X] in
theorem norm_tensorMonomial_le_one (z : X → EuclideanSpace ℝ ι)
    (hz : ∀ x, ‖z x‖ ≤ 1) (m : ℕ) (a : Fin m → ι) (x : X) :
    ‖tensorMonomial z m a x‖ ≤ 1 := by
  classical
  unfold tensorMonomial
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun r _ =>
    (PiLp.norm_apply_le (z x) (a r)).trans (hz x)

theorem integrable_mul_tensorMonomial {μ : Measure X}
    (z : X → EuclideanSpace ℝ ι) (hz : Measurable z) (hunit : ∀ x, ‖z x‖ ≤ 1)
    {f : X → ℝ} (hf : Integrable f μ) (m : ℕ) (a : Fin m → ι) :
    Integrable (fun x => f x * tensorMonomial z m a x) μ :=
  hf.mul_bdd (measurable_tensorMonomial z hz m a).aestronglyMeasurable
    (Eventually.of_forall (norm_tensorMonomial_le_one z hunit m a))

theorem integral_tensor_kernel_eq_momentEnergy {μ : Measure X} [SFinite μ]
    (z : X → EuclideanSpace ℝ ι) (hz : Measurable z) (hunit : ∀ x, ‖z x‖ ≤ 1)
    {f : X → ℝ} (hf : Integrable f μ) (m : ℕ) :
    (∫ p : X × X, f p.1 * f p.2 * inner ℝ (z p.1) (z p.2) ^ m ∂μ.prod μ) =
      tensorMomentEnergy μ z m f := by
  classical
  have hint (a : Fin m → ι) := integrable_mul_tensorMonomial z hz hunit hf m a
  simp_rw [inner_pow_eq_tensorMonomial z, Finset.mul_sum]
  rw [integral_finsetSum]
  · unfold tensorMomentEnergy
    apply Finset.sum_congr rfl
    intro a _
    calc
      (∫ p : X × X, f p.1 * f p.2 *
          (tensorMonomial z m a p.1 * tensorMonomial z m a p.2) ∂μ.prod μ) =
        ∫ p : X × X, (f p.1 * tensorMonomial z m a p.1) *
          (f p.2 * tensorMonomial z m a p.2) ∂μ.prod μ := by
            congr 1; ext p; ring
      _ = _ := by
        simpa only [pow_two] using integral_prod_mul
          (fun x => f x * tensorMonomial z m a x) (fun x => f x * tensorMonomial z m a x)
  · intro a _
    convert (hint a).mul_prod (hint a) using 1
    ext p
    ring

theorem integrable_tensor_kernel {μ : Measure X}
    (z : X → EuclideanSpace ℝ ι) (hz : Measurable z) (hunit : ∀ x, ‖z x‖ ≤ 1)
    {f : X → ℝ} (hf : Integrable f μ) (m : ℕ) :
    Integrable (fun p : X × X => f p.1 * f p.2 * inner ℝ (z p.1) (z p.2) ^ m)
      (μ.prod μ) := by
  classical
  have h : Integrable (fun p : X × X => ∑ a : Fin m → ι,
      (f p.1 * tensorMonomial z m a p.1) * (f p.2 * tensorMonomial z m a p.2))
      (μ.prod μ) := integrable_finsetSum _ (fun a _ =>
        (integrable_mul_tensorMonomial z hz hunit hf m a).mul_prod
          (integrable_mul_tensorMonomial z hz hunit hf m a))
  convert h using 1
  ext p
  rw [inner_pow_eq_tensorMonomial z, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- An individual positive degree contributes its actual tensor moment
energy to the full power-series kernel's quadratic form. Uniform domination
comes from summability at t=1 and the genuine L1 product of the target. -/
theorem powerSeries_kernel_energy_lower {μ : Measure X} [SFinite μ]
    (z : X → EuclideanSpace ℝ ι) (hz : Measurable z) (hunit : ∀ x, ‖z x‖ ≤ 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasSum (fun j => a j * t ^ j) (Φ t))
    {f : X → ℝ} (hf : Integrable f μ) (m : ℕ) :
    a m * tensorMomentEnergy μ z m f ≤
      ∫ p : X × X, f p.1 * f p.2 * Φ (inner ℝ (z p.1) (z p.2)) ∂μ.prod μ := by
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
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (m + 1)] with n hn
  have hint (j : ℕ) := (integrable_tensor_kernel z hz hunit hf j).const_mul (a j)
  have heq : (∫ p : X × X, F n p ∂μ.prod μ) =
      ∑ j ∈ Finset.range n, a j * tensorMomentEnergy μ z j f := by
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
  rw [heq]
  apply Finset.single_le_sum (fun j _ => mul_nonneg (ha j) (tensorMomentEnergy_nonneg _ _ _ _))
  exact Finset.mem_range.mpr (by omega)

section FeatureQuadratic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

omit [Fintype ι] in
theorem featureAdjoint_norm_sq_eq_kernel_integral (k : X → H) (hk : MemLp k 2 μ)
    (f : Lp ℝ 2 μ) :
    ‖(featureEmbedding μ k hk).adjoint f‖ ^ 2 =
      ∫ p : X × X, f p.1 * f p.2 * inner ℝ (k p.1) (k p.2) ∂μ.prod μ := by
  rw [featureEmbedding_adjoint_eq_integral, ← real_inner_self_eq_norm_sq]
  have hi := integral_prod_bilin (innerSL ℝ) (integrable_feature_smul k hk f)
    (integrable_feature_smul k hk f)
  change (∫ p : X × X, inner ℝ (f p.1 • k p.1) (f p.2 • k p.2) ∂μ.prod μ) =
    inner ℝ (∫ x, f x • k x ∂μ) (∫ x, f x • k x ∂μ) at hi
  rw [← hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    simp only [inner_smul_left, inner_smul_right, conj_trivial]
    ring

theorem featureAdjoint_powerSeries_energy_lower (k : X → H) (hk : MemLp k 2 μ)
    (z : X → EuclideanSpace ℝ ι) (hz : Measurable z) (hunit : ∀ x, ‖z x‖ ≤ 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasSum (fun j => a j * t ^ j) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = Φ (inner ℝ (z x) (z y)))
    (f : Lp ℝ 2 μ) (m : ℕ) :
    a m * tensorMomentEnergy μ z m f ≤ ‖(featureEmbedding μ k hk).adjoint f‖ ^ 2 := by
  rw [featureAdjoint_norm_sq_eq_kernel_integral]
  simp_rw [hkernel]
  exact powerSeries_kernel_energy_lower z hz hunit a ha Φ hseries
    ((Lp.memLp f).integrable (by norm_num)) m

end FeatureQuadratic
end
end KernelSeq
