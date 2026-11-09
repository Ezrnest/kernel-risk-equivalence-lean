import KernelSeq.SphereTensorKernel
import KernelSeq.SphericalLeverage
import KernelSeq.PowerSeriesKernelEnergy
import KernelSeq.SingularSystem

/-!
# The actual prediction support of a positive zonal power-series kernel

Every homogeneous polynomial space is supported in the actual prediction
range closure. Conversely, a function orthogonal to all polynomial degrees
has zero adjoint energy, by the genuine convergent quadratic energy series.
Taking orthogonal complements identifies the two closed spaces. Neither a
complete harmonic basis nor separability of ambient `L²` is assumed.
-/

namespace KernelSeq
open MeasureTheory Filter Set Submodule
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Every unordered repeated word has an actual ordered representative. -/
theorem sphereWordSym_surjective (m : ℕ) :
    Function.Surjective (sphereWordSym (ι := ι) (m := m)) := by
  intro s
  let v : List.Vector ι m := ⟨s.val.toList, (Multiset.length_toList _).trans s.property⟩
  refine ⟨v.get, ?_⟩
  apply Subtype.ext
  change (List.ofFn v.get : Multiset ι) = s.val
  have hlist : List.ofFn v.get = v.val := by
    have hv : v.toList = v.val := by cases v; rfl
    simpa only [List.Vector.toList_ofFn, hv] using congrArg List.Vector.toList (List.Vector.ofFn_get v)
  rw [hlist]
  exact Multiset.coe_toList _

omit [DecidableEq ι] in
theorem inner_sphereWordLp_eq_tensorMoment
    (m : ℕ) (a : Fin m → ι)
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) :
    inner ℝ (sphereSymLp (sphereWordSym a)) f =
      ∫ x, f x*tensorMonomial (fun y : KernelSphere (EuclideanSpace ℝ ι) =>
        (y : EuclideanSpace ℝ ι)) m a x ∂uniformSphere := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sphereWordLp_ae a] with x hx
  rw [hx, Real.inner_apply]
  exact mul_comm _ _

theorem sphere_tensorMoment_eq_zero_iff_orthogonal_polynomial (m : ℕ)
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) :
    tensorMomentEnergy uniformSphere
      (fun y : KernelSphere (EuclideanSpace ℝ ι) => (y : EuclideanSpace ℝ ι)) m f = 0 ↔
      f ∈ (homogeneousSpherePolynomialSpace ι m)ᗮ := by
  classical
  let z := fun y : KernelSphere (EuclideanSpace ℝ ι) => (y : EuclideanSpace ℝ ι)
  constructor
  · intro hz
    have hword (a : Fin m → ι) : inner ℝ (sphereSymLp (sphereWordSym a)) f = 0 := by
      rw [inner_sphereWordLp_eq_tensorMoment]
      have hsq : (∫ x, f x*tensorMonomial z m a x ∂uniformSphere)^2 ≤ 0 := by
        have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin m → ι)))
          (fun j _ => sq_nonneg (∫ x, f x*tensorMonomial z m j x ∂uniformSphere)) (Finset.mem_univ a)
        exact hh.trans_eq hz
      exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    have hspan : homogeneousSpherePolynomialSpace ι m ≤ (innerSL ℝ f).ker := by
      apply Submodule.span_le.mpr
      rintro g ⟨s, rfl⟩
      obtain ⟨a, rfl⟩ := sphereWordSym_surjective m s
      change inner ℝ f (sphereSymLp (sphereWordSym a)) = 0
      rw [real_inner_comm]
      exact hword a
    apply (Submodule.mem_orthogonal' _ f).mpr
    intro g hg
    exact hspan hg
  · intro hf
    unfold tensorMomentEnergy
    apply Finset.sum_eq_zero
    intro a _
    have hw : sphereSymLp (sphereWordSym a) ∈ homogeneousSpherePolynomialSpace ι m :=
      Submodule.subset_span (Set.mem_range_self _)
    have hi := (Submodule.mem_orthogonal _ f).mp hf _ hw
    rw [inner_sphereWordLp_eq_tensorMoment] at hi
    rw [hi, zero_pow (by norm_num : 2 ≠ 0)]

/-- The algebraic span of all actual homogeneous polynomial degrees. -/
def spherePolynomialSpan (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Submodule ℝ (Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) :=
  ⨆ m : ℕ, homogeneousSpherePolynomialSpace ι m

theorem spherePolynomialSpan_eq_span_union :
    spherePolynomialSpan ι = Submodule.span ℝ
      (⋃ m : ℕ, (homogeneousSpherePolynomialSpace ι m :
        Set (Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))))) :=
  Submodule.iSup_eq_span _

section Feature
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [DecidableEq ι] in
theorem sphere_feature_adjoint_eq_zero_iff_all_moments_zero
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ m, 0 < a m) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun m => a m*t^m) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) :
    (featureEmbedding uniformSphere k hk).adjoint f = 0 ↔ ∀ m,
      tensorMomentEnergy uniformSphere
        (fun y : KernelSphere (EuclideanSpace ℝ ι) => (y : EuclideanSpace ℝ ι)) m f = 0 := by
  let z := fun y : KernelSphere (EuclideanSpace ℝ ι) => (y : EuclideanSpace ℝ ι)
  have hz : Measurable z := measurable_subtype_coe
  have hunit (x : KernelSphere (EuclideanSpace ℝ ι)) : ‖z x‖ ≤ 1 :=
    (mem_sphere_zero_iff_norm.mp x.property).le
  have hgram (x y : KernelSphere (EuclideanSpace ℝ ι)) :
      inner ℝ (k x) (k y) = Φ (inner ℝ (z x) (z y)) := hkernel x y
  constructor
  · intro hf m
    have hh := featureAdjoint_powerSeries_energy_lower k hk z hz hunit a
      (fun m => (ha m).le) Φ hseries hgram f m
    rw [hf, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hh
    have hn := tensorMomentEnergy_nonneg uniformSphere z m f
    by_contra hne
    have hp : 0 < tensorMomentEnergy uniformSphere z m f := lt_of_le_of_ne hn (Ne.symm hne)
    exact (not_le_of_gt (mul_pos (ha m) hp)) hh
  · intro hf
    have hh := featureAdjoint_powerSeries_energy_hasSum k hk z hz hunit a
      (fun m => (ha m).le) Φ hseries hgram f
    have hzenergy (m : ℕ) : tensorMomentEnergy uniformSphere z m f = 0 := hf m
    have hterms : (fun m => a m*tensorMomentEnergy uniformSphere z m f) = (fun _ => 0) := by
      funext m
      rw [hzenergy, mul_zero]
    rw [hterms] at hh
    have he : ‖(featureEmbedding uniformSphere k hk).adjoint f‖^2 = 0 := hh.unique hasSum_zero
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)

/-- Every actual homogeneous polynomial lies in the supported prediction
space; positive power coefficients are used to derive this fact. -/
theorem homogeneousSpherePolynomialSpace_le_predictionRange
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ m, 0 < a m) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun m => a m*t^m) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y) (m : ℕ) :
    homogeneousSpherePolynomialSpace ι m ≤ PredictionRange (featureEmbedding uniformSphere k hk) := by
  rw [PredictionRange, ← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range]
  intro g hg
  apply (Submodule.mem_orthogonal _ g).mpr
  intro f hf
  have hfm := (sphere_tensorMoment_eq_zero_iff_orthogonal_polynomial m f).mp
    ((sphere_feature_adjoint_eq_zero_iff_all_moments_zero k hk a ha Φ hseries hkernel f).mp hf m)
  rw [real_inner_comm]
  exact (Submodule.mem_orthogonal _ f).mp hfm g hg

/-- Actual prediction support equals the closed span of the actual
polynomial spaces, without polynomial-density or harmonic-basis premises. -/
theorem sphere_predictionRange_eq_polynomialClosure
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ m, 0 < a m) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun m => a m*t^m) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y) :
    PredictionRange (featureEmbedding uniformSphere k hk) = (spherePolynomialSpan ι).topologicalClosure := by
  have horth : (featureEmbedding uniformSphere k hk).rangeᗮ = (spherePolynomialSpan ι)ᗮ := by
    ext f
    rw [ContinuousLinearMap.orthogonal_range]
    change (featureEmbedding uniformSphere k hk).adjoint f = 0 ↔ _
    rw [sphere_feature_adjoint_eq_zero_iff_all_moments_zero k hk a ha Φ hseries hkernel f]
    simp_rw [sphere_tensorMoment_eq_zero_iff_orthogonal_polynomial]
    rw [spherePolynomialSpan, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
  have heq := congrArg (fun P : Submodule ℝ (Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) => Pᗮ) horth
  simpa only [Submodule.orthogonal_orthogonal_eq_closure, PredictionRange] using heq

end Feature

section RKHS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H (KernelSphere (EuclideanSpace ℝ ι)) ℝ]

theorem zonalSphereRKHS_predictionRange_eq_polynomialClosure
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (a : ℕ → ℝ) (ha : ∀ m, 0 < a m)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun m => a m*t^m) (Φ t)) :
    PredictionRange (featureEmbedding uniformSphere (rkhsFeature (H := H))
      (zonalSphereFeature_memLp Φ hΦ hkernel)) = (spherePolynomialSpan ι).topologicalClosure := by
  apply sphere_predictionRange_eq_polynomialClosure _ _ a ha Φ hseries
  intro x y
  rw [rkhsFeature_inner, rkhsFeature_apply, hkernel]

end RKHS
end
end KernelSeq
