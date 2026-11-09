import KernelSeq.FiniteSpectralCompression
import KernelSeq.CovarianceMoments
import Mathlib.Probability.Independence.Basic

/-!
# Actual finite-dimensional covariance compressions

Finite spectral subspaces and their isometric inclusions are constructed from
the actual basis. Compression is an actual continuous linear map on bounded
operators. In particular its square is dominated by the compressed square of
a selfadjoint operator, and the genuine Bochner variance majorant transfers to
the finite-dimensional space. No compressed variance certificate is assumed.
-/

open MeasureTheory ProbabilityTheory Submodule
open scoped BigOperators

namespace KernelSeq

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev FiniteSpectralSubspace (b : HilbertBasis ι ℝ H) (s : Finset ι) :=
  span ℝ (b '' (s : Set ι))

instance finiteSpectralSubspace_finiteDimensional (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    FiniteDimensional ℝ (FiniteSpectralSubspace b s) :=
  FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image b)

/-- The actual inclusion of the finite-dimensional spectral space. -/
noncomputable def finiteSpectralInclusion (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    FiniteSpectralSubspace b s →L[ℝ] H := (FiniteSpectralSubspace b s).subtypeL

theorem finiteSpectralInclusion_adjoint_comp_self (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    (finiteSpectralInclusion b s).adjoint.comp (finiteSpectralInclusion b s) = 1 := by
  exact (FiniteSpectralSubspace b s).subtypeₗᵢ.adjoint_comp_self

omit [CompleteSpace H] in
/-- The finite coordinate projection fixes every vector in the actual finite span. -/
theorem finiteBasisProjection_eq_self_of_mem (b : HilbertBasis ι ℝ H) (s : Finset ι)
    {x : H} (hx : x ∈ FiniteSpectralSubspace b s) : finiteBasisProjection b s x = x := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [finiteBasisProjection_basis]
    split_ifs with h
    · rfl
    · exact (h hi).elim
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

/-- Inclusion followed by its actual adjoint is exactly the previously
constructed finite coordinate projection. -/
theorem finiteSpectralInclusion_comp_adjoint (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    (finiteSpectralInclusion b s).comp (finiteSpectralInclusion b s).adjoint =
      finiteBasisProjection b s := by
  ext x
  have hx : finiteBasisProjection b s x ∈ FiniteSpectralSubspace b s :=
    finiteBasisProjection_range_le b s ⟨x, rfl⟩
  have hadj : (finiteSpectralInclusion b s).adjoint x =
      (⟨finiteBasisProjection b s x, hx⟩ : FiniteSpectralSubspace b s) := by
    apply ext_inner_left ℝ
    intro u
    rw [(finiteSpectralInclusion b s).adjoint_inner_right]
    change inner ℝ (u : H) x = inner ℝ (u : H) (finiteBasisProjection b s x)
    calc
      inner ℝ (u : H) x = inner ℝ (finiteBasisProjection b s (u : H)) x := by
        rw [finiteBasisProjection_eq_self_of_mem b s u.property]
      _ = _ := (finiteBasisProjection_isSelfAdjoint b s).isSymmetric _ _
  change finiteSpectralInclusion b s ((finiteSpectralInclusion b s).adjoint x) = _
  rw [hadj]
  rfl

section Subspace

variable (U : Submodule ℝ H) [CompleteSpace U]

/-- Actual compression to a complete subspace, using its actual inclusion. -/
noncomputable def subspaceCompression (Y : H →L[ℝ] H) : U →L[ℝ] U :=
  U.subtypeL.adjoint.comp (Y.comp U.subtypeL)

theorem subspaceCompression_inner (Y : H →L[ℝ] H) (u v : U) :
    inner ℝ u (subspaceCompression U Y v) = inner ℝ (u : H) (Y (v : H)) := by
  exact U.subtypeL.adjoint_inner_right u (Y (v : H))

theorem subspaceCompression_quadratic (Y : H →L[ℝ] H) (u : U) :
    inner ℝ u (subspaceCompression U Y u) = inner ℝ (u : H) (Y (u : H)) := by
  exact U.subtypeL.adjoint_inner_right u (Y (u : H))

theorem subspaceCompression_apply_norm_le (Y : H →L[ℝ] H) (u : U) :
    ‖subspaceCompression U Y u‖ ≤ ‖Y (u : H)‖ := by
  simpa only [subspaceCompression, ContinuousLinearMap.comp_apply, Submodule.adjoint_subtypeL,
    Submodule.subtypeL_apply] using U.norm_orthogonalProjectionOnto_apply_le (Y (u : H))

theorem subspaceCompression_norm_le (Y : H →L[ℝ] H) : ‖subspaceCompression U Y‖ ≤ ‖Y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Y)
  intro u
  exact (subspaceCompression_apply_norm_le U Y u).trans
    (by simpa only [Submodule.coe_norm] using Y.le_opNorm (u : H))

/-- Compression is an actual continuous linear operator, supplying all
measurability and Bochner-integral bridges used below. -/
noncomputable def subspaceCompressionL : (H →L[ℝ] H) →L[ℝ] (U →L[ℝ] U) :=
  LinearMap.mkContinuous
    { toFun := subspaceCompression U
      map_add' := by intro A B; ext u; simp [subspaceCompression]
      map_smul' := by intro a A; ext u; simp [subspaceCompression] }
    1 (fun Y => by
      change ‖subspaceCompression U Y‖ ≤ 1 * ‖Y‖
      simpa only [one_mul] using subspaceCompression_norm_le U Y)

@[simp]
theorem subspaceCompressionL_apply (Y : H →L[ℝ] H) :
    subspaceCompressionL U Y = subspaceCompression U Y := rfl

theorem subspaceCompression_isSelfAdjoint {Y : H →L[ℝ] H} (hY : IsSelfAdjoint Y) :
    IsSelfAdjoint (subspaceCompression U Y) := by
  change (subspaceCompression U Y).adjoint = subspaceCompression U Y
  simp only [subspaceCompression, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hY.adjoint_eq, ContinuousLinearMap.comp_assoc]

theorem subspaceCompression_isPositive {Y : H →L[ℝ] H} (hY : Y.IsPositive) :
    (subspaceCompression U Y).IsPositive := by
  simpa only [subspaceCompression, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc] using hY.conj_adjoint U.subtypeL.adjoint

theorem subspaceCompression_mono {A B : H →L[ℝ] H} (hAB : A ≤ B) :
    subspaceCompression U A ≤ subspaceCompression U B := by
  apply (ContinuousLinearMap.le_def _ _).mpr
  have hp := subspaceCompression_isPositive U ((ContinuousLinearMap.le_def A B).mp hAB)
  simpa only [← subspaceCompressionL_apply, map_sub] using hp

theorem selfAdjoint_square_quadratic (Y : H →L[ℝ] H) (hY : IsSelfAdjoint Y) (x : H) :
    inner ℝ x ((Y * Y) x) = ‖Y x‖ ^ 2 := by
  simpa only [hY.adjoint_eq, ContinuousLinearMap.comp_apply, mul_apply_eq_comp, RCLike.re_to_real] using
    (Y.apply_norm_sq_eq_inner_adjoint_right x).symm

/-- The actual compression-square inequality needed for the finite Bernstein
variance majorant. It follows from the true orthogonal contraction. -/
theorem subspaceCompression_square_le (Y : H →L[ℝ] H) (hY : IsSelfAdjoint Y) :
    subspaceCompression U Y * subspaceCompression U Y ≤ subspaceCompression U (Y * Y) := by
  have hC := subspaceCompression_isSelfAdjoint U hY
  have hY2 : IsSelfAdjoint (Y * Y) := by
    change (Y * Y).adjoint = Y * Y
    change (Y.comp Y).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, hY.adjoint_eq]
    rfl
  have hC2 : IsSelfAdjoint (subspaceCompression U Y * subspaceCompression U Y) := by
    change (subspaceCompression U Y * subspaceCompression U Y).adjoint = _
    change ((subspaceCompression U Y).comp (subspaceCompression U Y)).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, hC.adjoint_eq]
    rfl
  apply (real_loewner_iff_quadratic _ _ hC2 (subspaceCompression_isSelfAdjoint U hY2)).mpr
  intro u
  rw [selfAdjoint_square_quadratic _ hC, subspaceCompression_quadratic,
    selfAdjoint_square_quadratic _ hY]
  exact pow_le_pow_left₀ (norm_nonneg _) (subspaceCompression_apply_norm_le U Y u) 2

/-- A finite-space operator lifted back by the actual inclusion and adjoint. -/
noncomputable def subspaceLift (B : U →L[ℝ] U) : H →L[ℝ] H :=
  U.subtypeL.comp (B.comp U.subtypeL.adjoint)

/-- The lift preserves the actual operator norm exactly, including the zero
subspace. This identifies finite-space tails with ambient compression tails. -/
theorem subspaceLift_norm (B : U →L[ℝ] U) : ‖subspaceLift U B‖ = ‖B‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
    intro x
    change ‖((B (U.subtypeL.adjoint x) : U) : H)‖ ≤ ‖B‖ * ‖x‖
    rw [Submodule.norm_coe]
    have hx : ‖U.subtypeL.adjoint x‖ ≤ ‖x‖ := by
      simpa only [Submodule.adjoint_subtypeL] using U.norm_orthogonalProjectionOnto_apply_le x
    exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg B))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (subspaceLift U B))
    intro u
    have hid : U.subtypeL.adjoint (u : H) = u := by
      have h := congrArg (fun L : U →L[ℝ] U => L u) U.subtypeₗᵢ.adjoint_comp_self
      exact h
    have h := (subspaceLift U B).le_opNorm (u : H)
    change ‖((B (U.subtypeL.adjoint (u : H)) : U) : H)‖ ≤
      ‖subspaceLift U B‖ * ‖(u : H)‖ at h
    simpa only [hid, Submodule.norm_coe] using h

section Random

variable {Ω J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable local instance compressionSubspaceContinuousENorm : ContinuousENorm (U →L[ℝ] U) := by
  letI : NormedAddCommGroup (U →L[ℝ] U) := ContinuousLinearMap.toNormedAddCommGroup
  infer_instance

noncomputable local instance compressionAmbientMeasurableSpace : MeasurableSpace (H →L[ℝ] H) := borel _
local instance compressionAmbientBorelSpace : BorelSpace (H →L[ℝ] H) := ⟨rfl⟩
noncomputable local instance compressionSubspaceMeasurableSpace : MeasurableSpace (U →L[ℝ] U) := borel _
local instance compressionSubspaceBorelSpace : BorelSpace (U →L[ℝ] U) := ⟨rfl⟩

theorem aestronglyMeasurable_subspaceCompression (Y : Ω → H →L[ℝ] H)
    (hY : AEStronglyMeasurable Y μ) :
    AEStronglyMeasurable (fun ω => subspaceCompression U (Y ω)) μ :=
  (subspaceCompressionL U).continuous.comp_aestronglyMeasurable hY

theorem integrable_subspaceCompression (Y : Ω → H →L[ℝ] H) (hY : Integrable Y μ) :
    Integrable (fun ω => subspaceCompression U (Y ω)) μ := by
  apply hY.norm.mono' (f := fun ω => subspaceCompression U (Y ω))
    (aestronglyMeasurable_subspaceCompression U Y hY.1)
  exact Filter.Eventually.of_forall (fun ω => subspaceCompression_norm_le U (Y ω))

/-- Actual compression commutes with the Bochner expectation. -/
theorem integral_subspaceCompression (Y : Ω → H →L[ℝ] H) (hY : Integrable Y μ) :
    (∫ ω, subspaceCompression U (Y ω) ∂μ) = subspaceCompression U (∫ ω, Y ω ∂μ) := by
  have hCY := integrable_subspaceCompression U Y hY
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  rw [inner_integral_operator_apply _ hCY, subspaceCompression_inner,
    inner_integral_operator_apply Y hY]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun ω => subspaceCompression_inner U (Y ω) v u))

/-- True centering survives the actual bounded compression. -/
theorem integral_subspaceCompression_eq_zero (Y : Ω → H →L[ℝ] H) (hY : Integrable Y μ)
    (hmean : (∫ ω, Y ω ∂μ) = 0) : (∫ ω, subspaceCompression U (Y ω) ∂μ) = 0 := by
  rw [integral_subspaceCompression U Y hY, hmean]
  exact (subspaceCompressionL U).map_zero

/-- Full joint independence is preserved by this actual continuous operator
map, without any standard-Borel or ambient separability condition. -/
theorem iIndepFun_subspaceCompression (Y : J → Ω → H →L[ℝ] H) (hind : iIndepFun Y μ) :
    iIndepFun (fun i ω => subspaceCompression U (Y i ω)) μ :=
  hind.comp (fun _ => subspaceCompressionL U) (fun _ => (subspaceCompressionL U).continuous.measurable)

theorem subspaceCompression_norm_bound_ae (Y : Ω → H →L[ℝ] H) {R : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) :
    ∀ᵐ ω ∂μ, ‖subspaceCompression U (Y ω)‖ ≤ R :=
  hbound.mono (fun ω hω => (subspaceCompression_norm_le U (Y ω)).trans hω)

/-- Square-integrability of the compressed operator field follows from the
actual integrable field and its increment bound, rather than being supplied. -/
theorem integrable_subspaceCompression_square (Y : Ω → H →L[ℝ] H)
    (hY : Integrable Y μ) {R : ℝ} (hbound : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) :
    Integrable (fun ω => subspaceCompression U (Y ω) * subspaceCompression U (Y ω)) μ :=
  integrable_operator_square_of_bound _ (integrable_subspaceCompression U Y hY)
    (subspaceCompression_norm_bound_ae U Y hbound)

/-- The actual Bochner second moment is dominated by the compressed original
second moment. Both square-integrability statements are derived from the
original integrable bounded field. -/
theorem integral_subspaceCompression_square_le (Y : Ω → H →L[ℝ] H)
    (hY : Integrable Y μ) {R : ℝ} (hbound : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R)
    (hself : ∀ᵐ ω ∂μ, IsSelfAdjoint (Y ω)) :
    (∫ ω, subspaceCompression U (Y ω) * subspaceCompression U (Y ω) ∂μ) ≤
      subspaceCompression U (∫ ω, Y ω * Y ω ∂μ) := by
  have hY2 := integrable_operator_square_of_bound Y hY hbound
  have hi := integral_operator_mono
    (fun ω => subspaceCompression U (Y ω) * subspaceCompression U (Y ω))
    (fun ω => subspaceCompression U (Y ω * Y ω))
    (integrable_subspaceCompression_square U Y hY hbound)
    (integrable_subspaceCompression U _ hY2)
    (hself.mono (fun ω hω => subspaceCompression_square_le U (Y ω) hω))
  rwa [integral_subspaceCompression U _ hY2] at hi

/-- A genuine uncompressed variance majorant transfers to the finite-space
second moments. The compressed variance bound is a conclusion. -/
theorem sum_integral_subspaceCompression_square_le [Fintype J]
    (Y : J → Ω → H →L[ℝ] H) (hY : ∀ i, Integrable (Y i) μ)
    {R : ℝ} (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ R)
    (hself : ∀ i, ∀ᵐ ω ∂μ, IsSelfAdjoint (Y i ω)) (V : H →L[ℝ] H)
    (hvar : (∑ i, ∫ ω, Y i ω * Y i ω ∂μ) ≤ V) :
    (∑ i, ∫ ω, subspaceCompression U (Y i ω) * subspaceCompression U (Y i ω) ∂μ) ≤
      subspaceCompression U V := by
  have hi (i : J) := integral_subspaceCompression_square_le U (Y i) (hY i) (hbound i) (hself i)
  have hsum : (∑ i, ∫ ω, subspaceCompression U (Y i ω) * subspaceCompression U (Y i ω) ∂μ) ≤
      ∑ i, subspaceCompression U (∫ ω, Y i ω * Y i ω ∂μ) := by
    apply (ContinuousLinearMap.le_def _ _).mpr
    rw [← Finset.sum_sub_distrib]
    exact ContinuousLinearMap.isPositive_sum Finset.univ
      (fun i _ => (ContinuousLinearMap.le_def _ _).mp (hi i))
  have hmap : (∑ i, subspaceCompression U (∫ ω, Y i ω * Y i ω ∂μ)) =
      subspaceCompression U (∑ i, ∫ ω, Y i ω * Y i ω ∂μ) := by
    exact (map_sum (subspaceCompressionL U) _ _).symm
  exact (hsum.trans_eq hmap).trans (subspaceCompression_mono U hvar)

end Random

end Subspace

/-- The actual finite-dimensional operator map supplied to a finite Bernstein
theorem; its domain is the constructed finite spectral subspace. -/
noncomputable def finiteCovarianceCompression (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    (H →L[ℝ] H) →L[ℝ] (FiniteSpectralSubspace b s →L[ℝ] FiniteSpectralSubspace b s) :=
  subspaceCompressionL (FiniteSpectralSubspace b s)

@[simp]
theorem finiteCovarianceCompression_apply (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (Y : H →L[ℝ] H) :
    finiteCovarianceCompression b s Y =
      (finiteSpectralInclusion b s).adjoint.comp (Y.comp (finiteSpectralInclusion b s)) := rfl

/-- Lifting the finite-space compression gives exactly `P_s Y P_s`. -/
theorem finiteCovarianceCompression_lift (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (Y : H →L[ℝ] H) :
    subspaceLift (FiniteSpectralSubspace b s) (finiteCovarianceCompression b s Y) =
      finiteBasisProjection b s * Y * finiteBasisProjection b s := by
  let I := finiteSpectralInclusion b s
  have hP : I.comp I.adjoint = finiteBasisProjection b s := finiteSpectralInclusion_comp_adjoint b s
  change I.comp ((I.adjoint.comp (Y.comp I)).comp I.adjoint) = _
  have heq : I.comp ((I.adjoint.comp (Y.comp I)).comp I.adjoint) =
      (I.comp I.adjoint).comp (Y.comp (I.comp I.adjoint)) := by
    simp only [ContinuousLinearMap.comp_assoc]
  rw [heq, hP]
  rfl

/-- Finite Bernstein norms and the ambient compression norms agree exactly. -/
theorem finiteCovarianceCompression_norm_eq (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (Y : H →L[ℝ] H) :
    ‖finiteCovarianceCompression b s Y‖ =
      ‖finiteBasisProjection b s * Y * finiteBasisProjection b s‖ := by
  rw [← finiteCovarianceCompression_lift]
  exact (subspaceLift_norm _ _).symm

end KernelSeq
