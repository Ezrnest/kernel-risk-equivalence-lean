import KernelSeq.SpherePolynomialSpace
import KernelSeq.PolynomialKernelEnergy
import Mathlib.Algebra.BigOperators.Fin

/-!
# The actual tensor feature of a spherical monomial kernel

The polynomial kernel `<x,y>^m` is realized by an actual finite Euclidean
feature. Its prediction embedding has range in the constructed symmetric
polynomial L2 space. No rank, kernel positivity or range certificate is
an input.
-/

namespace KernelSeq
open MeasureTheory Submodule Set WithLp
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def sphereWordSym {m : ℕ} (a : Fin m → ι) : Sym ι m :=
  ⟨(List.ofFn a : Multiset ι), by simp⟩

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereMultisetMonomial_word {m : ℕ} (a : Fin m → ι)
    (x : KernelSphere (EuclideanSpace ℝ ι)) :
    sphereMultisetMonomial (sphereWordSym a).val x = ∏ r, (x : EuclideanSpace ℝ ι) (a r) := by
  simp only [sphereMultisetMonomial, sphereWordSym, Multiset.map_coe, Multiset.prod_coe,
    List.map_ofFn, Fin.prod_ofFn, Function.comp_apply]

def sphereTensorFeature (m : ℕ) (x : KernelSphere (EuclideanSpace ℝ ι)) :
    EuclideanSpace ℝ (Fin m → ι) :=
  toLp 2 (fun a => ∏ r, (x : EuclideanSpace ℝ ι) (a r))

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereTensorFeature_continuous (m : ℕ) : Continuous (sphereTensorFeature (ι := ι) m) := by
  unfold sphereTensorFeature
  fun_prop

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereTensorFeature_gram (m : ℕ) (x y : KernelSphere (EuclideanSpace ℝ ι)) :
    inner ℝ (sphereTensorFeature m x) (sphereTensorFeature m y) =
      inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)^m := by
  rw [PiLp.inner_apply, inner_pow_eq_tensorMonomial (fun z : KernelSphere (EuclideanSpace ℝ ι) => (z : EuclideanSpace ℝ ι))]
  apply Finset.sum_congr rfl
  intro a _
  change (∏ r, (y : EuclideanSpace ℝ ι) (a r)) * (∏ r, (x : EuclideanSpace ℝ ι) (a r)) = _
  unfold tensorMonomial
  ring

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereTensorFeature_norm (m : ℕ) (x : KernelSphere (EuclideanSpace ℝ ι)) :
    ‖sphereTensorFeature m x‖ = 1 := by
  have hh := sphereTensorFeature_gram m x x
  have hx : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx, one_pow, one_pow] at hh
  nlinarith [norm_nonneg (sphereTensorFeature m x)]

omit [DecidableEq ι] in
def sphereTensorFeature_memLp (m : ℕ) :
    MemLp (sphereTensorFeature (ι := ι) m) 2 (uniformSphere (E := EuclideanSpace ℝ ι)) :=
  MemLp.of_bound (sphereTensorFeature_continuous m).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (sphereTensorFeature_norm m x).le)

omit [DecidableEq ι] in
theorem sphereWordLp_ae {m : ℕ} (a : Fin m → ι) :
    sphereSymLp (sphereWordSym a) =ᵐ[uniformSphere (E := EuclideanSpace ℝ ι)]
      fun x => ∏ r, (x : EuclideanSpace ℝ ι) (a r) := by
  exact ((sphereMultisetMonomial_memLp (sphereWordSym a).val).coeFn_toLp).trans
    (Filter.Eventually.of_forall (sphereMultisetMonomial_word a))

omit [DecidableEq ι] in
theorem sphereTensorEmbedding_eq_sum (m : ℕ) (u : EuclideanSpace ℝ (Fin m → ι)) :
    featureEmbedding (uniformSphere (E := EuclideanSpace ℝ ι)) (sphereTensorFeature m)
      (sphereTensorFeature_memLp m) u =
      ∑ a : Fin m → ι, u a • sphereSymLp (sphereWordSym a) := by
  have hterm (a : Fin m → ι) :
      (u a • sphereSymLp (sphereWordSym a) : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) =ᵐ[uniformSphere]
        fun x => u a * ∏ r, (x : EuclideanSpace ℝ ι) (a r) := by
    filter_upwards [Lp.coeFn_smul (u a) (sphereSymLp (sphereWordSym a)), sphereWordLp_ae a] with x hx hy
    exact hx.trans (by change u a * (sphereSymLp (sphereWordSym a)) x = _; rw [hy])
  apply Lp.ext
  filter_upwards [featureEmbedding_ae uniformSphere (sphereTensorFeature m) (sphereTensorFeature_memLp m) u,
    Lp.coeFn_fun_finsetSum Finset.univ (fun a : Fin m → ι => u a • sphereSymLp (sphereWordSym a)),
    ae_all_iff.mpr hterm] with x hx hsum hterms
  rw [hx, hsum, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [hterms a]
  rfl

theorem sphereTensorEmbedding_mem_polynomialSpace (m : ℕ) (u : EuclideanSpace ℝ (Fin m → ι)) :
    featureEmbedding (uniformSphere (E := EuclideanSpace ℝ ι)) (sphereTensorFeature m)
      (sphereTensorFeature_memLp m) u ∈ homogeneousSpherePolynomialSpace ι m := by
  rw [sphereTensorEmbedding_eq_sum]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self (sphereWordSym a)))

theorem sphereTensorPrediction_mem_polynomialSpace (m : ℕ)
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) :
    predictionCovariance (featureEmbedding uniformSphere (sphereTensorFeature m) (sphereTensorFeature_memLp m)) f ∈
      homogeneousSpherePolynomialSpace ι m :=
  sphereTensorEmbedding_mem_polynomialSpace m _

end
end KernelSeq
