import KernelSeq.SphereTensorKernel
import KernelSeq.PowerSeriesKernelEnergy
import KernelSeq.SourceNormBounds

/-!
# The actual zonal operator as a norm-summable series of power kernels

Each monomial Gram kernel has a genuine bounded tensor prediction
operator. The positive coefficient series converges in operator norm.
The already proved quadratic energy series identifies its symmetric sum
with the actual full prediction operator by real polarization.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local notation "SphereL2" => Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))

def spherePowerPredictionOperator (ι : Type*) [Fintype ι] [Nonempty ι] (j : ℕ) :
    Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)) →L[ℝ]
      Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)) :=
  predictionCovariance (featureEmbedding uniformSphere (sphereTensorFeature j) (sphereTensorFeature_memLp j))

omit [DecidableEq ι] in
theorem spherePowerPredictionOperator_norm_le (j : ℕ) :
    ‖spherePowerPredictionOperator ι j‖ ≤ 1 := by
  have hh := feature_prediction_covariance_norm_le (sphereTensorFeature (ι := ι) j)
    (sphereTensorFeature_memLp j) (κ := 1) (by norm_num)
    (Eventually.of_forall fun x => (sphereTensorFeature_norm j x).le)
  simpa only [spherePowerPredictionOperator, one_pow] using hh

omit [DecidableEq ι] in
theorem spherePowerPredictionOperator_quadratic (j : ℕ) (f : SphereL2) :
    inner ℝ f (spherePowerPredictionOperator ι j f) =
      tensorMomentEnergy uniformSphere
        (fun x : KernelSphere (EuclideanSpace ℝ ι) => (x : EuclideanSpace ℝ ι)) j f := by
  let S := featureEmbedding uniformSphere (sphereTensorFeature (ι := ι) j) (sphereTensorFeature_memLp j)
  change inner ℝ f (S (S.adjoint f)) = _
  rw [← S.adjoint_inner_left, real_inner_self_eq_norm_sq, featureAdjoint_norm_sq_eq_kernel_integral]
  simp_rw [sphereTensorFeature_gram]
  exact integral_tensor_kernel_eq_momentEnergy _ measurable_subtype_coe
    (fun x => (mem_sphere_zero_iff_norm.mp x.property).le)
    ((Lp.memLp f).integrable (by norm_num)) j

section Feature
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [DecidableEq ι] in
theorem spherePowerPredictionOperator_series_hasSum
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      inner ℝ (k x) (k y) = Φ (inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι))) :
    HasSum (fun j => a j • spherePowerPredictionOperator ι j)
      (predictionCovariance (featureEmbedding uniformSphere k hk)) := by
  let S := featureEmbedding uniformSphere k hk
  let L := predictionCovariance S
  let F : SphereL2 →L[ℝ] SphereL2 := ∑' j, a j • spherePowerPredictionOperator ι j
  have hsa : Summable a := by simpa only [one_pow, mul_one] using (hseries 1 (by norm_num)).summable
  have hs : Summable (fun j => a j • spherePowerPredictionOperator ι j) := by
    apply Summable.of_norm_bounded hsa
    intro j
    rw [norm_smul, Real.norm_of_nonneg (ha j)]
    exact mul_le_of_le_one_right (ha j) (spherePowerPredictionOperator_norm_le j)
  have happly (f : SphereL2) : HasSum (fun j => a j • spherePowerPredictionOperator ι j f) (F f) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, smul_apply] using
      (ContinuousLinearMap.apply ℝ SphereL2 f).hasSum hs.hasSum
  have hFsym : F.IsSymmetric := by
    intro x y
    have hx : HasSum (fun j => inner ℝ y (a j • spherePowerPredictionOperator ι j x))
        (inner ℝ y (F x)) := (innerSL ℝ y).hasSum (happly x)
    have hy : HasSum (fun j => inner ℝ x (a j • spherePowerPredictionOperator ι j y))
        (inner ℝ x (F y)) := (innerSL ℝ x).hasSum (happly y)
    have he : (fun j => inner ℝ y (a j • spherePowerPredictionOperator ι j x)) =
        (fun j => inner ℝ x (a j • spherePowerPredictionOperator ι j y)) := by
      funext j
      rw [inner_smul_right, inner_smul_right, real_inner_comm (spherePowerPredictionOperator ι j x) y]
      congr 1
      exact (predictionCovariance_isPositive (featureEmbedding uniformSphere (sphereTensorFeature j)
        (sphereTensorFeature_memLp j))).isSymmetric x y
    rw [he] at hx
    exact (real_inner_comm y (F x)).trans (hx.unique hy)
  have hq (f : SphereL2) : inner ℝ f (F f) = inner ℝ f (L f) := by
    have hf : HasSum (fun j => inner ℝ f (a j • spherePowerPredictionOperator ι j f))
        (inner ℝ f (F f)) := (innerSL ℝ f).hasSum (happly f)
    simp_rw [inner_smul_right, spherePowerPredictionOperator_quadratic] at hf
    have hnorm := featureAdjoint_powerSeries_energy_hasSum k hk
      (fun x : KernelSphere (EuclideanSpace ℝ ι) => (x : EuclideanSpace ℝ ι))
      measurable_subtype_coe (fun x => (mem_sphere_zero_iff_norm.mp x.property).le)
      a ha Φ hseries hkernel f
    change inner ℝ f (F f) = inner ℝ f (S (S.adjoint f))
    rw [← S.adjoint_inner_left, real_inner_self_eq_norm_sq]
    exact hf.unique hnorm
  have hD : (L-F).IsSymmetric := (predictionCovariance_isPositive S).isSymmetric.sub hFsym
  have hz : ∀ f : SphereL2, inner ℝ ((L-F) f) f = 0 := by
    intro f
    rw [real_inner_comm, sub_apply, inner_sub_right, hq, sub_self]
  have hzero := (hD.inner_map_self_eq_zero).mp hz
  have hident : L = F := by
    apply sub_eq_zero.mp
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun T : SphereL2 →ₗ[ℝ] SphereL2 => T f) hzero
  rw [show predictionCovariance (featureEmbedding uniformSphere k hk) = F from hident]
  exact hs.hasSum

end Feature
end
end KernelSeq
