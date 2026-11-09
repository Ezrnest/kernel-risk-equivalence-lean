import KernelSeq.UniformSphere
import KernelSeq.KernelSymmetry
import KernelSeq.FeatureLeverageSymmetry
import KernelSeq.OriginalScaleParameters

/-!
# Constant actual leverage for every zonal RKHS on the uniform sphere

Only the primitive RKHS kernel identity `k(x,y)=Φ(<x,y>)` is used. The unitary
action on H, covariance/resolvent symmetry, pointwise constant leverage and
the identity `Lλ=N1(λ)` are all conclusions. No spherical-harmonic spectrum,
addition formula, eigenvalue asymptotic, or leverage certificate is assumed.
This module does not yet construct the RKHS from positive power coefficients.
-/

namespace KernelSeq
open MeasureTheory Set
noncomputable section

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H (KernelSphere E) ℝ]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [SecondCountableTopology H] in
private theorem zonalSphereFeature_gram (Φ : ℝ → ℝ)
    (hkernel : ∀ x y : KernelSphere E, rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (U : E ≃ₗᵢ[ℝ] E) (x y : KernelSphere E) :
    inner ℝ (rkhsFeature (H := H) (sphereRotation U x)) (rkhsFeature (H := H) (sphereRotation U y)) =
      inner ℝ (rkhsFeature (H := H) x) (rkhsFeature (H := H) y) := by
  rw [rkhsFeature_inner, rkhsFeature_apply, rkhsFeature_inner, rkhsFeature_apply,
    hkernel, hkernel, zonalSphereKernel_rotation]

/-- The RKHS rotation is actually constructed by dense extension of the
permutation of its canonical kernel sections. -/
def zonalSphereRKHSRotation (Φ : ℝ → ℝ)
    (hkernel : ∀ x y : KernelSphere E, rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (U : E ≃ₗᵢ[ℝ] E) : H ≃ₗᵢ[ℝ] H :=
  featureSymmetry (rkhsFeature (H := H)) rkhsFeature_denseSpan (sphereRotation U).toEquiv
    (zonalSphereFeature_gram Φ hkernel U)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [SecondCountableTopology H] in
@[simp] theorem zonalSphereRKHSRotation_feature (Φ : ℝ → ℝ)
    (hkernel : ∀ x y : KernelSphere E, rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (U : E ≃ₗᵢ[ℝ] E) (x : KernelSphere E) :
    zonalSphereRKHSRotation Φ hkernel U (rkhsFeature (H := H) x) =
      rkhsFeature (H := H) (sphereRotation U x) :=
  featureSymmetry_apply _ _ _ _ _

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [SecondCountableTopology H] in
theorem zonalSphereRKHS_diag_nonneg (Φ : ℝ → ℝ)
    (hkernel : ∀ x y : KernelSphere E, rkhsKernel (H := H) x y = zonalSphereKernel Φ x y) :
    0 ≤ Φ 1 := by
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E) (x := 0) |>.mpr (zero_le_one : (0 : ℝ) ≤ 1)
  have hh : ‖rkhsFeature (H := H) (⟨x, hx⟩ : KernelSphere E)‖ ^ 2 = Φ 1 := by
    rw [rkhsFeature_norm_sq, hkernel, zonalSphereKernel_diag]
  exact hh ▸ sq_nonneg _

/-- Genuine L² feature integrability follows from continuity of Φ on the
actual inner-product interval and the constant kernel diagonal. -/
def zonalSphereFeature_memLp (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere E, rkhsKernel (H := H) x y = zonalSphereKernel Φ x y) :
    MemLp (rkhsFeature (H := H)) 2 (uniformSphere (E := E)) := by
  have hm : Measurable (fun p : KernelSphere E × KernelSphere E => rkhsKernel (H := H) p.1 p.2) := by
    have heq : (fun p : KernelSphere E × KernelSphere E => rkhsKernel (H := H) p.1 p.2) =
        (fun p => zonalSphereKernel Φ p.1 p.2) := funext fun p => hkernel p.1 p.2
    rw [heq]
    exact (zonalSphereKernel_continuous Φ hΦ).measurable
  apply rkhsFeature_memLp (uniformSphere (E := E)) hm (Real.sqrt (Φ 1)) (Real.sqrt_nonneg _)
  intro x
  rw [hkernel, zonalSphereKernel_diag, Real.sq_sqrt (zonalSphereRKHS_diag_nonneg Φ hkernel)]

/-- Every actual regularized leverage value equals the actual effective
dimension; this derives the addition-formula consequence without assuming it. -/
theorem zonalSphere_normalizedLeverage_eq_effectiveDimension
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere E, rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    {lam : ℝ} (hlam : 0 < lam) :
    let k := rkhsFeature (H := H)
    let hk := zonalSphereFeature_memLp Φ hΦ hkernel
    ∀ x, normalizedLeverage k hk lam x = featureEffectiveDimension k hk lam := by
  dsimp only
  let k := rkhsFeature (H := H)
  let hk := zonalSphereFeature_memLp Φ hΦ hkernel
  have hinv (U : E ≃ₗᵢ[ℝ] E) (x : KernelSphere E) :
      normalizedLeverage k hk lam (sphereRotation U x) = normalizedLeverage k hk lam x := by
    exact normalizedLeverage_featureSymmetry k hk (sphereRotation U).toMeasurableEquiv
      (sphereRotation_measurePreserving U) (zonalSphereRKHSRotation Φ hkernel U)
      (fun y => (zonalSphereRKHSRotation_feature Φ hkernel U y).symm) hlam x
  have hconst := sphere_invariant_eq (fun x => normalizedLeverage k hk lam x) hinv
  intro x
  rw [← integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam]
  calc
    normalizedLeverage k hk lam x = ∫ _ : KernelSphere E, normalizedLeverage k hk lam x
        ∂uniformSphere := by simp
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun y => hconst x y)

/-- The maximal regularized leverage is exactly N1, with the genuine real
essential supremum and the genuine uniform sphere measure. -/
theorem zonalSphere_leverageEssentialSup_eq_effectiveDimension
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere E, rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    {lam : ℝ} (hlam : 0 < lam) :
    let k := rkhsFeature (H := H)
    let hk := zonalSphereFeature_memLp Φ hΦ hkernel
    featureLeverageEssentialSup k hk lam = featureEffectiveDimension k hk lam := by
  dsimp only [featureLeverageEssentialSup]
  rw [essSup_congr_ae (Filter.Eventually.of_forall
    (zonalSphere_normalizedLeverage_eq_effectiveDimension Φ hΦ hkernel hlam)), essSup_const']

end
end KernelSeq
