import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The actual uniform sphere and orthogonal symmetries

The probability measure is the normalization of the genuine Haar-to-sphere
cone measure, not an assumed invariant probability. Orthogonal invariance is
proved by the cone definition and the proved invariance of ambient volume.
-/

namespace KernelSeq
open MeasureTheory Set Metric
open scoped Pointwise ENNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev KernelSphere (E : Type*) [NormedAddCommGroup E] := {x : E // x ∈ sphere (0 : E) 1}

/-- The genuine orthogonal action on the unit sphere. -/
def sphereRotation (U : E ≃ₗᵢ[ℝ] E) : KernelSphere E ≃ₜ KernelSphere E :=
  { toEquiv :=
      { toFun := fun x => ⟨U x, by simpa only [mem_sphere_zero_iff_norm, U.norm_map] using x.property⟩
        invFun := fun x => ⟨U.symm x, by simpa only [mem_sphere_zero_iff_norm, U.symm.norm_map] using x.property⟩
        left_inv := fun x => Subtype.ext (U.symm_apply_apply (x : E))
        right_inv := fun x => Subtype.ext (U.apply_symm_apply (x : E)) }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

@[simp] theorem sphereRotation_coe (U : E ≃ₗᵢ[ℝ] E) (x : KernelSphere E) :
    ((sphereRotation U x : KernelSphere E) : E) = U x := rfl

@[simp] theorem sphereRotation_symm (U : E ≃ₗᵢ[ℝ] E) :
    (sphereRotation U).symm = sphereRotation U.symm := rfl

private theorem sphere_cone_preimage (U : E ≃ₗᵢ[ℝ] E) (s : Set (KernelSphere E)) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereRotation U) ⁻¹' s)) =
      U ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext z
  constructor
  · rintro ⟨r, hr, v, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨r, hr, U x, ⟨sphereRotation U x, hx, rfl⟩, by simp⟩
  · rintro ⟨r, hr, v, ⟨x, hx, rfl⟩, hz⟩
    refine ⟨r, hr, U.symm x, ⟨sphereRotation U.symm x, ?_, rfl⟩, ?_⟩
    · change sphereRotation U (sphereRotation U.symm x) ∈ s
      simpa only [← sphereRotation_symm, Homeomorph.apply_symm_apply] using hx
    · apply U.injective
      simpa only [map_smul, U.apply_symm_apply] using hz

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Orthogonal invariance of the actual (unnormalized) spherical cone measure. -/
theorem sphereRotation_measurePreserving_toSphere (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereRotation U) (volume : Measure E).toSphere
      (volume : Measure E).toSphere := by
  refine ⟨(sphereRotation U).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereRotation U).measurable hs,
    Measure.toSphere_apply' _ ((sphereRotation U).measurable hs), Measure.toSphere_apply' _ hs,
    sphere_cone_preimage]
  congr 1
  have hh := U.toHomeomorph.measurableEmbedding.map_apply (volume : Measure E)
    (Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  change (Measure.map (U : E → E) volume) (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) = _ at hh
  rw [U.measurePreserving.map_eq] at hh
  exact hh.symm

/-- Normalized surface measure on the actual unit sphere. -/
def uniformSphere : Measure (KernelSphere E) :=
  ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere

instance uniformSphere_isProbabilityMeasure [Nontrivial E] :
    IsProbabilityMeasure (uniformSphere (E := E)) := by
  constructor
  change ((volume : Measure E).toSphere univ)⁻¹ * (volume : Measure E).toSphere univ = 1
  apply ENNReal.inv_mul_cancel
  · intro hz
    exact Measure.toSphere_ne_zero (volume : Measure E) (Measure.measure_univ_eq_zero.mp hz)
  · exact (measure_lt_top (volume : Measure E).toSphere univ).ne

/-- Rotations preserve the genuine uniform sphere probability measure. -/
theorem sphereRotation_measurePreserving (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereRotation U) (uniformSphere (E := E)) (uniformSphere (E := E)) := by
  refine ⟨(sphereRotation U).measurable, ?_⟩
  rw [uniformSphere, Measure.map_smul, (sphereRotation_measurePreserving_toSphere U).map_eq]

/-- The actual zonal scalar kernel; no eigenvalue or leverage estimate is
part of its definition. Positivity and harmonic spectral results are separate. -/
def zonalSphereKernel (Φ : ℝ → ℝ) (x y : KernelSphere E) : ℝ :=
  Φ (inner ℝ (x : E) (y : E))

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem zonalSphereKernel_rotation (Φ : ℝ → ℝ) (U : E ≃ₗᵢ[ℝ] E)
    (x y : KernelSphere E) :
    zonalSphereKernel Φ (sphereRotation U x) (sphereRotation U y) = zonalSphereKernel Φ x y := by
  simp only [zonalSphereKernel, sphereRotation_coe, U.inner_map_map]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem zonalSphereKernel_diag (Φ : ℝ → ℝ) (x : KernelSphere E) :
    zonalSphereKernel Φ x x = Φ 1 := by
  have hn : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simp only [zonalSphereKernel, real_inner_self_eq_norm_sq, hn, one_pow]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem exists_sphereRotation_eq (x y : KernelSphere E) :
    ∃ U : E ≃ₗᵢ[ℝ] E, sphereRotation U x = y := by
  by_cases hxy : x = y
  · subst y
    exact ⟨LinearIsometryEquiv.refl ℝ E, rfl⟩
  have hval : (x : E) ≠ y := fun h => hxy (Subtype.ext h)
  have hn0 : ‖(x : E) - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hval)
  have hx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hy : ‖(y : E)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
  have hi : 2 * inner ℝ ((x : E) - y) (x : E) = ‖(x : E) - y‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_comm (y : E) (x : E)]
    nlinarith
  refine ⟨(ℝ ∙ ((x : E) - y))ᗮ.reflection, Subtype.ext ?_⟩
  change (ℝ ∙ ((x : E) - y))ᗮ.reflection (x : E) = y
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  have hc : (2 : ℝ) * (inner ℝ ((x : E) - y) (x : E) / ‖(x : E) - y‖ ^ 2) = 1 := by
    rw [← mul_div_assoc]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hn0)).2
    exact hi
  rw [two_smul]
  have hc' : inner ℝ ((x : E) - y) (x : E) / ‖(x : E) - y‖ ^ 2 +
      inner ℝ ((x : E) - y) (x : E) / ‖(x : E) - y‖ ^ 2 = 1 := by linarith
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [← add_smul, hc', one_smul]
  abel

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Transitivity is proved by an actual orthogonal reflection; invariance
therefore implies pointwise constancy, not merely an a.e. statement. -/
theorem sphere_invariant_eq (f : KernelSphere E → ℝ)
    (hinv : ∀ (U : E ≃ₗᵢ[ℝ] E) (x : KernelSphere E), f (sphereRotation U x) = f x)
    (x y : KernelSphere E) : f x = f y := by
  obtain ⟨U, hU⟩ := exists_sphereRotation_eq x y
  simpa only [hU] using (hinv U x).symm

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem zonalSphereKernel_continuous (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1)) :
    Continuous (fun p : KernelSphere E × KernelSphere E => zonalSphereKernel Φ p.1 p.2) := by
  apply hΦ.comp_continuous (by fun_prop)
  intro p
  have hx : ‖(p.1 : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.property
  have hy : ‖(p.2 : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2.property
  have hi := abs_real_inner_le_norm (p.1 : E) (p.2 : E)
  rw [hx, hy, one_mul] at hi
  exact abs_le.mp hi

end
end KernelSeq
