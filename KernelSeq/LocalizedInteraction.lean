import KernelSeq.SpectralBlocks
import Mathlib.Tactic.NoncommRing

/-!
# The actual separated high/low localized interaction multiplier

This module realizes the interaction multiplier in operator norm on separated
spectral blocks. The high and low spaces are the spectral ranges constructed
in `SpectralBlocks`. Neither commutation of the
two original operators nor separability of their Hilbert spaces is assumed.
-/

open LinearMap Module.End Submodule

namespace KernelSeq

noncomputable section
attribute [local instance] Classical.propDecidable

section Rectangular

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The two regularization weights are part of the multiplier itself. -/
def regularizedRectangularSylvesterMap (U : F →L[ℝ] F) (V : E →L[ℝ] E) :
    (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (rectangularSandwichMap (1 + U) (1 + V)).comp (rectangularSylvesterMap U V)

omit [CompleteSpace F] in
@[simp]
theorem regularizedRectangularSylvesterMap_apply (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (C : E →L[ℝ] F) :
    regularizedRectangularSylvesterMap U V C =
      (1 + U).comp ((rectangularSylvesterSolution U V C).comp (1 + V)) := rfl

theorem regularizedRectangularSylvesterMap_norm_le (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (hU : IsUnit U) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hUinv : ‖Ring.inverse U‖ ≤ 1 / (2 * τ)) (hV : ‖V‖ ≤ τ) :
    ‖regularizedRectangularSylvesterMap U V‖ ≤ 6 / τ := by
  have hhalf : ‖Ring.inverse U‖ * ‖V‖ ≤ 1 / 2 := by
    calc
      _ ≤ (1 / (2 * τ)) * τ := mul_le_mul hUinv hV (norm_nonneg _) (by positivity)
      _ = 1 / 2 := by field_simp
  have hq : ‖Ring.inverse U‖ * ‖V‖ < 1 := by linarith
  have hright : ‖(1 : E →L[ℝ] E) + V‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : E →L[ℝ] E)‖ + ‖V‖ := norm_add_le _ _
      _ ≤ 1 + τ := add_le_add ContinuousLinearMap.norm_id_le hV
      _ ≤ 2 := by linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro C
  let X := rectangularSylvesterSolution U V C
  have hX : ‖X‖ ≤ ‖C‖ / τ := rectangularSylvester_norm_le_of_gap U V C hτ hUinv hV
  have heq : U.comp X - X.comp V = C := rectangularSylvester_equation U V C hU hq
  have hUX : U.comp X = C + X.comp V := (sub_eq_iff_eq_add).mp heq
  have hleft : ‖(1 + U).comp X‖ ≤ (3 / τ) * ‖C‖ := by
    have hnorm : ‖(1 + U).comp X‖ ≤ ‖C‖ + (1 + τ) * ‖X‖ := by
      calc
        _ = ‖X + (C + X.comp V)‖ := by rw [ContinuousLinearMap.add_comp, hUX]; rfl
        _ ≤ ‖X‖ + (‖C‖ + ‖X.comp V‖) :=
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
        _ ≤ ‖X‖ + (‖C‖ + ‖X‖ * τ) := by
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le X V).trans
            (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
        _ = _ := by ring
    calc
      _ ≤ ‖C‖ + (1 + τ) * (‖C‖ / τ) := hnorm.trans
        (add_le_add_right (mul_le_mul_of_nonneg_left hX (by linarith : 0 ≤ 1 + τ)) _)
      _ = ((1 + 2 * τ) / τ) * ‖C‖ := by field_simp; ring
      _ ≤ (3 / τ) * ‖C‖ := by gcongr; linarith
  rw [regularizedRectangularSylvesterMap_apply, ← ContinuousLinearMap.comp_assoc]
  calc
    _ ≤ ‖(1 + U).comp X‖ * ‖(1 : E →L[ℝ] E) + V‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((3 / τ) * ‖C‖) * 2 := mul_le_mul hleft hright (norm_nonneg _) (by positivity)
    _ = (6 / τ) * ‖C‖ := by ring

end Rectangular

section SpectralRestriction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem compactSpectralMultiplier_projection_commutes (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) :
    compactSpectralMultiplier T hc hp φ K hK hφ * compactSpectralProjection T hc hp s =
      compactSpectralProjection T hc hp s * compactSpectralMultiplier T hc hp φ K hK hφ := by
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [mul_apply_eq_comp, compactSpectralMultiplier_repr, compactSpectralProjection_repr]
  ring

theorem compactSpectralMultiplier_spectralSubspace_invariant (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) :
    ∀ x ∈ SpectralSubspace T hc hp s,
      compactSpectralMultiplier T hc hp φ K hK hφ x ∈ SpectralSubspace T hc hp s := by
  rintro x ⟨y, rfl⟩
  refine ⟨compactSpectralMultiplier T hc hp φ K hK hφ y, ?_⟩
  exact congrArg (fun F : H →L[ℝ] H => F y)
    (compactSpectralMultiplier_projection_commutes T hc hp s φ K hK hφ).symm

/-- A spectral function restricted to the actual closed spectral range. -/
def spectralSubspaceMultiplier (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) :
    SpectralSubspace T hc hp s →L[ℝ] SpectralSubspace T hc hp s :=
  (compactSpectralMultiplier T hc hp φ K hK hφ).restrict
    (compactSpectralMultiplier_spectralSubspace_invariant T hc hp s φ K hK hφ)

@[simp]
theorem spectralSubspaceMultiplier_coe (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K)
    (x : SpectralSubspace T hc hp s) :
    (spectralSubspaceMultiplier T hc hp s φ K hK hφ x : H) =
      compactSpectralMultiplier T hc hp φ K hK hφ (x : H) := rfl

theorem spectralSubspaceMultiplier_norm_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) :
    ‖spectralSubspaceMultiplier T hc hp s φ K hK hφ‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  exact (compactSpectralMultiplier T hc hp φ K hK hφ).le_of_opNorm_le
    (compactSpectralMultiplier_norm_le T hc hp φ K hK hφ) (x : H)

theorem spectralSubspaceMultiplier_eigen (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K)
    {x : SpectralSubspace T hc hp s} {t : ℝ}
    (hx : T (x : H) = t • (x : H)) :
    spectralSubspaceMultiplier T hc hp s φ K hK hφ x = φ t • x := by
  apply Subtype.ext
  exact compactSpectralMultiplier_eigen T hc hp φ K hK hφ hx

theorem spectralSubspaceMultiplier_isSymmetric (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) :
    (spectralSubspaceMultiplier T hc hp s φ K hK hφ).IsSymmetric := by
  have hs : (compactSpectralMultiplier T hc hp φ K hK hφ).IsSymmetric := by
    unfold compactSpectralMultiplier
    exact hilbertDiagonal_isSymmetric _ _ _ _ _
  intro x y
  exact hs (x : H) (y : H)

theorem spectralSubspaceMultiplier_commutes (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) :
    (spectralRestriction T hc hp s).comp (spectralSubspaceMultiplier T hc hp s φ K hK hφ) =
      (spectralSubspaceMultiplier T hc hp s φ K hK hφ).comp (spectralRestriction T hc hp s) := by
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  change (compactEigenbasis T hc hp.isSymmetric).repr
    (T (compactSpectralMultiplier T hc hp φ K hK hφ (x : H))) i =
      (compactEigenbasis T hc hp.isSymmetric).repr
        (compactSpectralMultiplier T hc hp φ K hK hφ (T (x : H))) i
  simp only [compactEigenbasis_repr_apply, compactSpectralMultiplier_repr]
  ring

end SpectralRestriction

section LowWeight

/-- The actual low-frequency residual is bounded away from zero at the
manuscript cutoff. This derives the inverse weight bound from the filter. -/
theorem localized_low_weight_lower {M ρ A α τ t : ℝ} {φ : ℝ → ℝ}
    (hM : 0 ≤ M) (_hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract 1 M ρ A φ) (hτ : 0 < τ)
    (hτA : τ ≤ 1 / (4 * (A + 1))) (ht : t ∈ Set.Icc (0 : ℝ) M) (htτ : t ≤ τ) :
    (1 / 2 : ℝ) ≤ residualWeight 1 α φ t := by
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) hM
  have hφ : |φ t| ≤ A := by simpa only [div_one] using h.profile_bound (by norm_num) ht
  have hs : τ * (4 * (A + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 4 * (A + 1))).mp hτA
  have hprod : t * φ t ≤ τ * A :=
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hφ) ht.1).trans
      (mul_le_mul_of_nonneg_right htτ hA)
  have hpower : 0 ≤ (1 / (t + 1)) ^ (α / 2) :=
    Real.rpow_nonneg (div_nonneg zero_le_one (by linarith [ht.1])) _
  dsimp only [residualWeight, ResidualFilter.residual, ResidualFilter.shrinkage]
  nlinarith

/-- A low-frequency ratio is extended by zero outside its actual block. -/
def localizedLowRatio (τ α : ℝ) (φ g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ τ then g t / residualWeight 1 α φ t else 0

theorem localizedLowRatio_bound {M ρ A α τ K : ℝ} {φ g : ℝ → ℝ}
    (hM : 0 ≤ M) (hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract 1 M ρ A φ) (hτ : 0 < τ)
    (hτA : τ ≤ 1 / (4 * (A + 1))) (hK : 0 ≤ K)
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) M, |g t| ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) M) : |localizedLowRatio τ α φ g t| ≤ 2 * K := by
  dsimp only [localizedLowRatio]
  split_ifs with htτ
  · have ha := localized_low_weight_lower (α := α) hM hf h hτ hτA ht htτ
    have hpos : 0 < residualWeight 1 α φ t := by linarith
    rw [abs_div, abs_of_pos hpos]
    apply (div_le_iff₀ hpos).mpr
    nlinarith [hg t ht, mul_nonneg hK (sub_nonneg.mpr ha)]
  · simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK

end LowWeight

section Dimensionless

/-- The inverse filter in the manuscript's dimensionless coordinates. -/
def localizedDimensionlessProfile (lam : ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℝ := lam * φ (lam * u)

theorem localizedDimensionless_inverseProfile (lam : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    ResidualFilter.inverseProfile 1 (localizedDimensionlessProfile lam φ) t =
      ResidualFilter.inverseProfile lam φ t := by
  simp only [ResidualFilter.inverseProfile, ResidualFilter.spectralCoordinate,
    localizedDimensionlessProfile, one_mul]
  ring

theorem localizedDimensionless_weightedResidual (lam : ℝ) (hlam : lam ≠ 0)
    (ρ : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    ResidualFilter.weightedResidual 1 ρ (localizedDimensionlessProfile lam φ) t =
      ResidualFilter.weightedResidual lam ρ φ t := by
  have hc : ResidualFilter.spectralCoordinate lam t =
      lam * ResidualFilter.spectralCoordinate 1 t := by
    simp only [ResidualFilter.spectralCoordinate, one_mul]
  have hb : (ResidualFilter.spectralCoordinate 1 t + 1) / 1 =
      (ResidualFilter.spectralCoordinate lam t + lam) / lam := by
    rw [hc]
    field_simp
  unfold ResidualFilter.weightedResidual
  rw [hb]
  congr 1
  simp only [ResidualFilter.residual, ResidualFilter.shrinkage,
    localizedDimensionlessProfile, hc]
  ring

/-- Passing to `U=T/lam` retains the original common `ρ,A` exactly. The new
spectral endpoint is `M/lam`; no new inverse-profile continuity is introduced. -/
theorem localizedDimensionless_contract {lam M ρ A : ℝ} {φ : ℝ → ℝ}
    (hlam : 0 < lam) (h : ResidualFilter.Contract lam M ρ A φ) :
    ResidualFilter.Contract 1 (M / lam) ρ A (localizedDimensionlessProfile lam φ) := by
  have hdomain : ResidualFilter.logDomain 1 (M / lam) = ResidualFilter.logDomain lam M := by
    simp only [ResidualFilter.logDomain, div_one]
  refine ⟨h.rho_pos, ?_, ?_⟩
  · intro u hu
    rw [localizedDimensionless_inverseProfile,
      localizedDimensionless_weightedResidual lam hlam.ne']
    exact h.size u (hdomain ▸ hu)
  · intro u hu v hv
    rw [localizedDimensionless_weightedResidual lam hlam.ne',
      localizedDimensionless_weightedResidual lam hlam.ne']
    exact h.residual_lipschitz u (hdomain ▸ hu) v (hdomain ▸ hv)

theorem localizedDimensionless_spectralFilter {lam M : ℝ} {φ : ℝ → ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter M φ) :
    ResidualFilter.SpectralFilter (M / lam) (localizedDimensionlessProfile lam φ) := by
  have hmem (u : Set.Icc (0 : ℝ) (M / lam)) : lam * (u : ℝ) ∈ Set.Icc (0 : ℝ) M := by
    refine ⟨mul_nonneg hlam.le u.property.1, ?_⟩
    have hu := (le_div_iff₀ hlam).mp u.property.2
    nlinarith only [hu]
  let f : Set.Icc (0 : ℝ) (M / lam) → Set.Icc (0 : ℝ) M := fun u => ⟨lam * u, hmem u⟩
  have hfm : Measurable f := (continuous_const.mul continuous_subtype_val).subtype_mk _ |>.measurable
  refine ⟨?_, ?_, ?_⟩
  · exact (hf.measurable.comp hfm).const_mul lam
  · intro u hu
    exact mul_nonneg hlam.le (hf.nonneg _ (hmem ⟨u, hu⟩))
  · intro u hu
    have hq := hf.shrinkage_mem (lam * u) (hmem ⟨u, hu⟩)
    convert hq using 1
    simp only [ResidualFilter.shrinkage, localizedDimensionlessProfile]
    ring

end Dimensionless

section Numerator

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The two separated products in the actual interaction numerator. -/
def localizedNumeratorMap (FU RU : F →L[ℝ] F) (GV HV : E →L[ℝ] E) :
    (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  rectangularSandwichMap FU GV - rectangularSandwichMap RU HV

omit [CompleteSpace F] in
@[simp]
theorem localizedNumeratorMap_apply (FU RU : F →L[ℝ] F) (GV HV : E →L[ℝ] E)
    (K : E →L[ℝ] F) : localizedNumeratorMap FU RU GV HV K =
      FU.comp (K.comp GV) - RU.comp (K.comp HV) := rfl

omit [CompleteSpace F] in
theorem localizedNumeratorMap_norm_le (FU RU : F →L[ℝ] F) (GV HV : E →L[ℝ] E)
    {A : ℝ} (hA : 0 ≤ A) (hFU : ‖FU‖ ≤ A) (hRU : ‖RU‖ ≤ 1)
    (hGV : ‖GV‖ ≤ 2) (hHV : ‖HV‖ ≤ 2 * A) :
    ‖localizedNumeratorMap FU RU GV HV‖ ≤ 4 * A := by
  calc
    _ ≤ ‖rectangularSandwichMap FU GV‖ + ‖rectangularSandwichMap RU HV‖ := by
      exact norm_sub_le (rectangularSandwichMap FU GV) (rectangularSandwichMap RU HV)
    _ ≤ ‖FU‖ * ‖GV‖ + ‖RU‖ * ‖HV‖ :=
      add_le_add (norm_rectangularSandwichMap_le _ _) (norm_rectangularSandwichMap_le _ _)
    _ ≤ A * 2 + 1 * (2 * A) := add_le_add
      (mul_le_mul hFU hGV (norm_nonneg _) hA)
      (mul_le_mul hRU hHV (norm_nonneg _) (by norm_num))
    _ = 4 * A := by ring

/-- A bounded linear map on the whole rectangular operator space, rather
than a merely pointwise bound for a scalar divided difference. -/
def localizedWeightedMultiplier (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (FU RU : F →L[ℝ] F) (GV HV : E →L[ℝ] E) :
    (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (regularizedRectangularSylvesterMap U V).comp (localizedNumeratorMap FU RU GV HV)

theorem localizedWeightedMultiplier_norm_le (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (FU RU : F →L[ℝ] F) (GV HV : E →L[ℝ] E)
    (hU : IsUnit U) {τ A : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hUinv : ‖Ring.inverse U‖ ≤ 1 / (2 * τ)) (hV : ‖V‖ ≤ τ)
    (hA : 0 ≤ A) (hFU : ‖FU‖ ≤ A) (hRU : ‖RU‖ ≤ 1)
    (hGV : ‖GV‖ ≤ 2) (hHV : ‖HV‖ ≤ 2 * A) :
    ‖localizedWeightedMultiplier U V FU RU GV HV‖ ≤ 24 * A / τ := by
  calc
    _ ≤ ‖regularizedRectangularSylvesterMap U V‖ * ‖localizedNumeratorMap FU RU GV HV‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (6 / τ) * (4 * A) := mul_le_mul
      (regularizedRectangularSylvesterMap_norm_le U V hU hτ hτ1 hUinv hV)
      (localizedNumeratorMap_norm_le FU RU GV HV hA hFU hRU hGV hHV)
      (norm_nonneg (localizedNumeratorMap FU RU GV HV)) (by positivity)
    _ = 24 * A / τ := by ring

end Numerator

section MatrixCoefficients

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem localizedNumeratorMap_coefficient
    (FU RU : F →L[ℝ] F) (GV HV : E →L[ℝ] E) (K : E →L[ℝ] F)
    (hsF : FU.IsSymmetric) (hsR : RU.IsSymmetric)
    {x : F} {y : E} {fu ru gv hv : ℝ}
    (hFx : FU x = fu • x) (hRx : RU x = ru • x)
    (hGy : GV y = gv • y) (hHy : HV y = hv • y) :
    inner ℝ x (localizedNumeratorMap FU RU GV HV K y) =
      (fu * gv - ru * hv) * inner ℝ x (K y) := by
  have hF (z : F) : inner ℝ x (FU z) = fu * inner ℝ x z := by
    calc
      _ = inner ℝ (FU x) z := (hsF x z).symm
      _ = _ := by rw [hFx]; simp only [inner_smul_left, conj_trivial]
  have hR (z : F) : inner ℝ x (RU z) = ru * inner ℝ x z := by
    calc
      _ = inner ℝ (RU x) z := (hsR x z).symm
      _ = _ := by rw [hRx]; simp only [inner_smul_left, conj_trivial]
  simp only [localizedNumeratorMap_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, inner_sub_right]
  rw [hF, hR, hGy, hHy]
  simp only [map_smul, inner_smul_right]
  ring

/-- The actual Sylvester solution has the genuine divided-difference matrix
coefficient on separated eigenvectors. -/
theorem regularizedRectangularSylvesterMap_coefficient
    (U : F →L[ℝ] F) (V : E →L[ℝ] E) (C : E →L[ℝ] F)
    (hU : IsUnit U) (hq : ‖Ring.inverse U‖ * ‖V‖ < 1) (hsU : U.IsSymmetric)
    {x : F} {y : E} {u v : ℝ} (hx : U x = u • x) (hy : V y = v • y)
    (huv : u - v ≠ 0) :
    inner ℝ x (regularizedRectangularSylvesterMap U V C y) =
      (1 + u) * (1 + v) / (u - v) * inner ℝ x (C y) := by
  let X := rectangularSylvesterSolution U V C
  have hUinner (z : F) : inner ℝ x (U z) = u * inner ℝ x z := by
    calc
      _ = inner ℝ (U x) z := (hsU x z).symm
      _ = _ := by rw [hx]; simp only [inner_smul_left, conj_trivial]
  have heq := congrArg (fun D : E →L[ℝ] F => inner ℝ x (D y))
    (rectangularSylvester_equation U V C hU hq)
  change inner ℝ x (U (X y) - X (V y)) = inner ℝ x (C y) at heq
  rw [inner_sub_right, hUinner, hy, map_smul] at heq
  simp only [inner_smul_right] at heq
  have hcoeff : inner ℝ x (X y) = inner ℝ x (C y) / (u - v) := by
    apply (eq_div_iff huv).mpr
    nlinarith only [heq]
  have hweight_left (z : F) : inner ℝ x (((1 : F →L[ℝ] F) + U) z) =
      (1 + u) * inner ℝ x z := by
    change inner ℝ x (z + U z) = _
    rw [inner_add_right, hUinner]
    ring
  have hweight_right : ((1 : E →L[ℝ] E) + V) y = (1 + v) • y := by
    change y + V y = _
    rw [hy]
    module
  rw [regularizedRectangularSylvesterMap_apply]
  change inner ℝ x (((1 : F →L[ℝ] F) + U) (X (((1 : E →L[ℝ] E) + V) y))) = _
  rw [hweight_right, map_smul, hweight_left, inner_smul_right, hcoeff]
  ring

end MatrixCoefficients

section SylvesterFactorization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The interaction numerator intertwines the actual rectangular Sylvester
operator. This is the termwise DOI identity, proved as an operator identity. -/
theorem localizedNumeratorMap_sylvester_intertwining
    (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (FU RU : F →L[ℝ] F) (GV HV : E →L[ℝ] E)
    (hFU : U.comp FU = FU.comp U) (hRU : U.comp RU = RU.comp U)
    (hGV : V.comp GV = GV.comp V) (hHV : V.comp HV = HV.comp V)
    (C : E →L[ℝ] F) :
    U.comp (localizedNumeratorMap FU RU GV HV C) -
      (localizedNumeratorMap FU RU GV HV C).comp V =
        localizedNumeratorMap FU RU GV HV (U.comp C - C.comp V) := by
  have hF z : U (FU z) = FU (U z) := congrArg (fun L : F →L[ℝ] F => L z) hFU
  have hR z : U (RU z) = RU (U z) := congrArg (fun L : F →L[ℝ] F => L z) hRU
  have hG z : V (GV z) = GV (V z) := congrArg (fun L : E →L[ℝ] E => L z) hGV
  have hH z : V (HV z) = HV (V z) := congrArg (fun L : E →L[ℝ] E => L z) hHV
  ext x
  simp only [localizedNumeratorMap_apply, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, hF, hR, hG, hH]

/-- Applying the divided-difference multiplier to the actual compressed
perturbation recovers the actual interaction, by uniqueness of the Sylvester
solution. No interaction identity is supplied as a premise. -/
theorem localizedWeightedMultiplier_perturbation_identity
    (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (FU RU : F →L[ℝ] F) (GV HV : E →L[ℝ] E)
    (hU : IsUnit U) (hq : ‖Ring.inverse U‖ * ‖V‖ < 1)
    (hFU : U.comp FU = FU.comp U) (hRU : U.comp RU = RU.comp U)
    (hGV : V.comp GV = GV.comp V) (hHV : V.comp HV = HV.comp V)
    (C : E →L[ℝ] F) :
    localizedWeightedMultiplier U V FU RU GV HV (U.comp C - C.comp V) =
      (1 + U).comp ((localizedNumeratorMap FU RU GV HV C).comp (1 + V)) := by
  have heq := localizedNumeratorMap_sylvester_intertwining U V FU RU GV HV hFU hRU hGV hHV C
  have hsol := rectangularSylvester_unique U V
    (localizedNumeratorMap FU RU GV HV (U.comp C - C.comp V))
    (rectangularSylvesterSolution U V
      (localizedNumeratorMap FU RU GV HV (U.comp C - C.comp V)))
    (localizedNumeratorMap FU RU GV HV C) hU hq
    (rectangularSylvester_equation U V _ hU hq) heq
  change (1 + U).comp
    ((rectangularSylvesterSolution U V
      (localizedNumeratorMap FU RU GV HV (U.comp C - C.comp V))).comp (1 + V)) = _
  rw [hsol]

end SylvesterFactorization

section ActualSeparatedMultiplier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance : NormedSpace ℝ H := InnerProductSpace.toNormedSpace

local instance localizedOperatorsNormedAddCommGroup
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedAddCommGroup (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ) :=
  inferInstance

local instance localizedOperatorsNormedSpace
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedSpace ℝ (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ) :=
  inferInstance

/-- The manuscript kernel on its separated support. -/
def localizedSeparatedKernel (φ : ℝ → ℝ) (α u v : ℝ) : ℝ :=
  (1 + u) * (1 + v) *
    (φ u * ResidualFilter.residual φ v - ResidualFilter.residual φ u * φ v) /
      ((u - v) * residualWeight 1 α φ v)

/-- The actual high/low block admits a genuine bounded operator-space
multiplier with the manuscript's divided-difference coefficients. All profile
and inverse-weight bounds follow from the single original filter contract.
The constant is uniform in the common spectral upper bound `M`. -/
theorem actual_localized_separated_multiplier
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτA : τ ≤ 1 / (4 * (A + 1))) :
    ∃ W : (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ) →L[ℝ]
        (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ),
      ‖W‖ ≤ 24 * A / τ ∧
      ∀ (K : LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ)
        (x : HighSpectralSpace U hcU hpU τ) (y : LowSpectralSpace V hcV hpV τ) (u v : ℝ),
        U (x : H) = u • (x : H) → V (y : H) = v • (y : H) →
        2 * τ ≤ u → v ∈ Set.Icc (0 : ℝ) τ →
        inner ℝ x (W K y) = localizedSeparatedKernel φ α u v * inner ℝ x (K y) := by
  have hM : 0 ≤ M := (norm_nonneg U).trans hMU
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) hM
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) M, |φ t| ≤ A := by
    intro t ht
    simpa only [div_one] using h.profile_bound (by norm_num) ht
  have hφU : ∀ t ∈ Set.Icc (0 : ℝ) ‖U‖, |φ t| ≤ A :=
    fun _ ht => hφ _ ⟨ht.1, ht.2.trans hMU⟩
  have hψU : ∀ t ∈ Set.Icc (0 : ℝ) ‖U‖, |ResidualFilter.residual φ t| ≤ 1 :=
    fun _ ht => hf.residual_abs_le_one ⟨ht.1, ht.2.trans hMU⟩
  have hG : ∀ t ∈ Set.Icc (0 : ℝ) ‖V‖,
      |localizedLowRatio τ α φ (ResidualFilter.residual φ) t| ≤ 2 := by
    intro t ht
    simpa only [mul_one] using localizedLowRatio_bound hM hf h hτ hτA zero_le_one
      (fun _ ht => hf.residual_abs_le_one ht) ⟨ht.1, ht.2.trans hMV⟩
  have hJ : ∀ t ∈ Set.Icc (0 : ℝ) ‖V‖, |localizedLowRatio τ α φ φ t| ≤ 2 * A :=
    fun _ ht => localizedLowRatio_bound hM hf h hτ hτA hA hφ ⟨ht.1, ht.2.trans hMV⟩
  let FU := spectralSubspaceMultiplier U hcU hpU (Set.Ici (2 * τ)) φ A hA hφU
  let RU := spectralSubspaceMultiplier U hcU hpU (Set.Ici (2 * τ))
    (ResidualFilter.residual φ) 1 zero_le_one hψU
  let GV := spectralSubspaceMultiplier V hcV hpV (Set.Icc 0 τ)
    (localizedLowRatio τ α φ (ResidualFilter.residual φ)) 2 (by norm_num) hG
  let HV := spectralSubspaceMultiplier V hcV hpV (Set.Icc 0 τ)
    (localizedLowRatio τ α φ φ) (2 * A) (by positivity) hJ
  let UH := highSpectralRestriction U hcU hpU τ
  let VL := lowSpectralRestriction V hcV hpV τ
  have hUnit : IsUnit UH := highSpectralRestriction_isUnit U hcU hpU τ hτ
  have hInv : ‖Ring.inverse UH‖ ≤ 1 / (2 * τ) :=
    highSpectralRestriction_inverse_norm_le U hcU hpU τ hτ
  have hLow : ‖VL‖ ≤ τ := lowSpectralRestriction_norm_le V hcV hpV τ hτ.le
  have hq : ‖Ring.inverse UH‖ * ‖VL‖ < 1 := by
    have hh := mul_le_mul hInv hLow (norm_nonneg VL) (by positivity : 0 ≤ 1 / (2 * τ))
    have hid : (1 / (2 * τ)) * τ = (1 / 2 : ℝ) := by field_simp
    rw [hid] at hh
    linarith
  refine ⟨localizedWeightedMultiplier UH VL FU RU GV HV,
    localizedWeightedMultiplier_norm_le UH VL FU RU GV HV hUnit hτ hτ1 hInv hLow hA
      (spectralSubspaceMultiplier_norm_le _ _ _ _ _ _ _ _)
      (spectralSubspaceMultiplier_norm_le _ _ _ _ _ _ _ _)
      (spectralSubspaceMultiplier_norm_le _ _ _ _ _ _ _ _)
      (spectralSubspaceMultiplier_norm_le _ _ _ _ _ _ _ _), ?_⟩
  intro K x y u v hx hy hu hv
  have hxu : UH x = u • x := Subtype.ext hx
  have hyv : VL y = v • y := Subtype.ext hy
  have huv : u - v ≠ 0 := by linarith [hv.2]
  have hFU : FU x = φ u • x := spectralSubspaceMultiplier_eigen _ _ _ _ _ _ _ _ hx
  have hRU : RU x = ResidualFilter.residual φ u • x :=
    spectralSubspaceMultiplier_eigen _ _ _ _ _ _ _ _ hx
  have hGV : GV y = (ResidualFilter.residual φ v / residualWeight 1 α φ v) • y := by
    simpa only [localizedLowRatio, if_pos hv.2] using
      spectralSubspaceMultiplier_eigen V hcV hpV (Set.Icc 0 τ)
        (localizedLowRatio τ α φ (ResidualFilter.residual φ)) 2 (by norm_num) hG hy
  have hHV : HV y = (φ v / residualWeight 1 α φ v) • y := by
    simpa only [localizedLowRatio, if_pos hv.2] using
      spectralSubspaceMultiplier_eigen V hcV hpV (Set.Icc 0 τ)
        (localizedLowRatio τ α φ φ) (2 * A) (by positivity) hJ hy
  have hnum := localizedNumeratorMap_coefficient FU RU GV HV K
    (spectralSubspaceMultiplier_isSymmetric _ _ _ _ _ _ _ _)
    (spectralSubspaceMultiplier_isSymmetric _ _ _ _ _ _ _ _) hFU hRU hGV hHV
  change inner ℝ x (regularizedRectangularSylvesterMap UH VL
    (localizedNumeratorMap FU RU GV HV K) y) = _
  rw [regularizedRectangularSylvesterMap_coefficient UH VL _ hUnit hq
    (spectralRestriction_isSymmetric U hcU hpU (Set.Ici (2 * τ))) hxu hyv huv, hnum]
  simp only [localizedSeparatedKernel, div_eq_mul_inv, mul_inv_rev]
  ring

end ActualSeparatedMultiplier

end
end KernelSeq
