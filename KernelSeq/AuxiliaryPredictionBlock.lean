import KernelSeq.AuxiliaryInteraction
import KernelSeq.LocalizedHighLow

/-!
# The actual auxiliary-difference prediction block

This module supplies the outside factors of the auxiliary correction multiplier.
All covariance operators, inverse roots, indicator projections, and interaction
differences are actual bounded operators. The closed high space used internally
contains the boundary atom; the final population high projection is strict.
-/

namespace KernelSeq

open Submodule
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance auxiliaryPredictionAmbientNormedSpace : NormedSpace ℝ H :=
  InnerProductSpace.toNormedSpace

local instance auxiliaryPredictionOperatorsNormedAddCommGroup
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedAddCommGroup (AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ) :=
  inferInstance

local instance auxiliaryPredictionOperatorsNormedSpace
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedSpace ℝ (AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ) :=
  inferInstance

/-- The difference of the genuine original and auxiliary interactions. The
auxiliary contract is derived from the original one, not a new premise. -/
def actualAuxiliaryInteractionDifference (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) : H →L[ℝ] H :=
  compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h -
    compactInteraction U V hcU hcV hpU hpV (ResidualFilter.auxiliaryFilter 1 τ φ)
      (by norm_num) hMU hMV hf.auxiliary (h.auxiliary_contract (by norm_num) hτ hτ1)

/-- The actual mixed normalized perturbation on the reversed low/high spaces. -/
def auxiliaryPredictionMixedBlock (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ :=
  (spectralRangeProjection U hcU hpU (Set.Icc 0 (2 * τ / 3))).comp
    ((manuscriptMixedPerturbation V U hcV hcU hpV hpU 1).comp
      (AuxiliaryHighSpace V hcV hpV τ).subtypeL)

theorem auxiliaryPredictionMixedBlock_norm_le (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ)
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4) :
    ‖auxiliaryPredictionMixedBlock U V hcU hcV hpU hpV τ‖ ≤
      2 * lowBlockDeviation U V hcV hpV := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg _))
  intro x
  have hP := (spectralRangeProjection U hcU hpU (Set.Icc 0 (2 * τ / 3))).le_of_opNorm_le
    (spectralRangeProjection_norm_le U hcU hpU (Set.Icc 0 (2 * τ / 3)))
    (manuscriptMixedPerturbation V U hcV hcU hpV hpU 1 (x : H))
  have hK := (manuscriptMixedPerturbation V U hcV hcU hpV hpU 1).le_of_opNorm_le
    (manuscriptMixedPerturbation_norm_le V U hcV hcU hpV hpU 1 (by norm_num) hδ) (x : H)
  simp only [one_mul] at hP
  exact hP.trans hK

/-- Actual entries of the compressed mixed perturbation. -/
theorem auxiliaryPredictionMixedBlock_cross_entry (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ)
    (i : CompactSpectralIndex U) (j : CompactSpectralIndex V)
    (hi : i.1 ∈ Set.Icc (0 : ℝ) (2 * τ / 3))
    (x : AuxiliaryLowSpace U hcU hpU τ) (y : AuxiliaryHighSpace V hcV hpV τ)
    (hx : (x : H) = compactEigenbasis U hcU hpU.isSymmetric i)
    (hy : (y : H) = compactEigenbasis V hcV hpV.isSymmetric j) :
    inner ℝ x (auxiliaryPredictionMixedBlock U V hcU hcV hpU hpV τ y) =
      ((i.1 - j.1) / (Real.sqrt (i.1 + 1) * Real.sqrt (j.1 + 1))) *
        inner ℝ (compactEigenbasis U hcU hpU.isSymmetric i)
          (compactEigenbasis V hcV hpV.isSymmetric j) := by
  have hproj : compactSpectralProjection U hcU hpU (Set.Icc 0 (2 * τ / 3))
      (compactEigenbasis U hcU hpU.isSymmetric i) = compactEigenbasis U hcU hpU.isSymmetric i := by
    simp only [compactSpectralProjection_eigenbasis, if_pos hi, one_smul]
  change inner ℝ (x : H) (compactSpectralProjection U hcU hpU (Set.Icc 0 (2 * τ / 3))
    (manuscriptMixedPerturbation V U hcV hcU hpV hpU 1 (y : H))) = _
  rw [hx, hy]
  calc
    _ = inner ℝ (compactSpectralProjection U hcU hpU (Set.Icc 0 (2 * τ / 3))
        (compactEigenbasis U hcU hpU.isSymmetric i))
        (manuscriptMixedPerturbation V U hcV hcU hpV hpU 1
          (compactEigenbasis V hcV hpV.isSymmetric j)) :=
      (compactSpectralProjection_isSymmetric U hcU hpU (Set.Icc 0 (2 * τ / 3)) _ _).symm
    _ = _ := by rw [hproj]; exact compactMixedDifference_cross_entry U V hcU hcV hpU hpV 1 (by norm_num) i j

/-- The exact auxiliary correction numerator on the actual population high
spectrum, with no commutation of `U` and `V`. -/
theorem actualAuxiliaryInteractionDifference_cross_entry (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (i : CompactSpectralIndex U) (j : CompactSpectralIndex V) (hj : τ ≤ j.1) :
    inner ℝ (compactEigenbasis U hcU hpU.isSymmetric i)
      (actualAuxiliaryInteractionDifference U V hcU hcV hpU hpV φ hMU hMV hf h hτ hτ1
        (compactEigenbasis V hcV hpV.isSymmetric j)) =
      auxiliaryDifference τ φ i.1 * (ResidualFilter.residual φ j.1 + i.1 * φ j.1) *
        inner ℝ (compactEigenbasis U hcU hpU.isSymmetric i)
          (compactEigenbasis V hcV hpV.isSymmetric j) := by
  unfold actualAuxiliaryInteractionDifference
  rw [_root_.sub_apply, inner_sub_right, compactInteraction_cross_entry, compactInteraction_cross_entry]
  rw [← sub_mul, auxiliary_interaction_difference hτ hj]

/-- Complete actual factorization of the auxiliary correction on the closed
population high space. The multiplier is constructed from the actual cutoff
filter, and its perturbation input is the actual compressed mixed difference.
No operator-factorization or multiplier certificate is a premise. -/
theorem auxiliaryPrediction_factorization (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ W : (AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ) →L[ℝ]
        (AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ),
      ‖W‖ ≤ 12 * A * (A + 1) / τ ∧
      actualAuxiliaryInteractionDifference U V hcU hcV hpU hpV φ hMU hMV hf h hτ hτ1 *
          compactSpectralProjection V hcV hpV (Set.Ici (2 * (τ / 2))) =
        compactRegularizedInvSqrt U hcU hpU 1 *
          (((AuxiliaryLowSpace U hcU hpU τ).subtypeL.comp
            (W (auxiliaryPredictionMixedBlock U V hcU hcV hpU hpV τ))).comp
              (spectralRangeProjection V hcV hpV (Set.Ici (2 * (τ / 2))))) *
          compactRegularizedInvSqrt V hcV hpV 1 *
          compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
            (by norm_num) hα0 hMV hf := by
  let W := actualAuxiliaryMultiplier U V hcU hcV hpU hpV φ hMU hMV hf h hα2 (τ := τ)
  refine ⟨W, actualAuxiliaryMultiplier_norm_le U V hcU hcV hpU hpV φ hMU hMV hf h hα2 hτ hτ1, ?_⟩
  let bU := compactEigenbasis U hcU hpU.isSymmetric
  let bV := compactEigenbasis V hcV hpV.isSymmetric
  let RU := compactRegularizedInvSqrt U hcU hpU 1
  let RV := compactRegularizedInvSqrt V hcV hpV 1
  let PH := compactSpectralProjection V hcV hpV (Set.Ici (2 * (τ / 2)))
  let D := actualAuxiliaryInteractionDifference U V hcU hcV hpU hpV φ hMU hMV hf h hτ hτ1
  let a := compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α) (by norm_num) hα0 hMV hf
  let K := auxiliaryPredictionMixedBlock U V hcU hcV hpU hpV τ
  let B := ((AuxiliaryLowSpace U hcU hpU τ).subtypeL.comp (W K)).comp
    (spectralRangeProjection V hcV hpV (Set.Ici (2 * (τ / 2))))
  change D * PH = RU * B * RV * a
  apply highLow_hilbertBasis_ext bV
  intro j
  have hae : a (bV j) = residualWeight 1 α φ j.1 • bV j := by
    exact compactSpectralMultiplier_eigen V hcV hpV _ _ _ _ (compactEigenbasis_eigen V hcV hpV.isSymmetric j)
  have hRV : RV (bV j) = (Real.sqrt (j.1 + 1))⁻¹ • bV j :=
    compactRegularizedInvSqrt_eigenbasis V hcV hpV 1 (by norm_num) j
  by_cases hj : j.1 ∈ Set.Ici (2 * (τ / 2))
  · have hjτ : τ ≤ j.1 := by simpa only [show 2 * (τ / 2) = τ by ring, Set.mem_Ici] using hj
    have hPH : PH (bV j) = bV j := by
      simp only [PH, bV, compactSpectralProjection_eigenbasis, if_pos hj, one_smul]
    let y : AuxiliaryHighSpace V hcV hpV τ := ⟨bV j, ⟨bV j, hPH⟩⟩
    have hPHy : spectralRangeProjection V hcV hpV (Set.Ici (2 * (τ / 2))) (bV j) = y := Subtype.ext hPH
    have hright : (RU * B * RV * a) (bV j) =
        ((Real.sqrt (j.1 + 1))⁻¹ * residualWeight 1 α φ j.1) • RU (W K y : H) := by
      simp only [mul_apply_eq_comp, hae, hRV, map_smul, B, ContinuousLinearMap.comp_apply, hPHy,
        Submodule.subtypeL_apply, smul_smul]
      congr 1
      ring
    have hleft : (D * PH) (bV j) = D (bV j) := by simp only [mul_apply_eq_comp, hPH]
    rw [hright, hleft]
    apply bU.repr.injective
    ext i
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    have hRU : bU.repr (RU (W K y : H)) i =
        (Real.sqrt (i.1 + 1))⁻¹ * bU.repr (W K y : H) i :=
      compactRegularizedInvSqrt_repr U hcU hpU 1 (by norm_num) _ i
    rw [hRU]
    have hD := actualAuxiliaryInteractionDifference_cross_entry U V hcU hcV hpU hpV φ
      hMU hMV hf h hτ hτ1 i j hjτ
    rw [bU.repr_apply_apply]
    change inner ℝ (bU i) (D (bV j)) = _
    rw [hD]
    by_cases hi : i.1 ∈ Set.Icc (0 : ℝ) (2 * τ / 3)
    · have hPL : compactSpectralProjection U hcU hpU (Set.Icc 0 (2 * τ / 3)) (bU i) = bU i := by
        simp only [bU, compactSpectralProjection_eigenbasis, if_pos hi, one_smul]
      let x : AuxiliaryLowSpace U hcU hpU τ := ⟨bU i, ⟨bU i, hPL⟩⟩
      have hw := actualAuxiliaryMultiplier_coefficient U V hcU hcV hpU hpV φ hMU hMV hf h hα2 hτ
        K x y (compactEigenbasis_eigen U hcU hpU.isSymmetric i)
        (compactEigenbasis_eigen V hcV hpV.isSymmetric j) hi.2 hjτ
      have hk := auxiliaryPredictionMixedBlock_cross_entry U V hcU hcV hpU hpV τ i j hi x y rfl rfl
      have ht : j.1 ∈ Set.Icc (0 : ℝ) M :=
        ⟨compactEigenvalue_nonneg V hcV hpV j,
          ((le_abs_self j.1).trans (compactEigenvalue_norm_le V hcV hpV.isSymmetric j)).trans hMV⟩
      have ha : residualWeight 1 α φ j.1 ≠ 0 := ne_of_gt (auxiliary_weight_positive hf ht)
      rw [bU.repr_apply_apply]
      change _ = ((Real.sqrt (j.1 + 1))⁻¹ * residualWeight 1 α φ j.1) *
        ((Real.sqrt (i.1 + 1))⁻¹ * inner ℝ x (W K y))
      rw [hw, hk]
      unfold auxiliarySeparatedKernel
      simpa only [mul_assoc] using (highLow_scalar_root_cancellation
        (N := auxiliaryDifference τ φ i.1 * (ResidualFilter.residual φ j.1 + i.1 * φ j.1))
        (c := inner ℝ (bU i) (bV j)) (compactEigenvalue_nonneg U hcU hpU i)
        (compactEigenvalue_nonneg V hcV hpV j) (by linarith [hi.2]) ha).symm
    · have hz := spectralSubspace_coefficient_eq_zero U hcU hpU (Set.Icc 0 (2 * τ / 3))
        (W K y) i hi
      change bU.repr (W K y : H) i = 0 at hz
      have hH : auxiliaryDifference τ φ i.1 = 0 := auxiliaryDifference_eq_zero hτ φ
        (by have hn := compactEigenvalue_nonneg U hcU hpU i; by_contra hh; exact hi ⟨hn, le_of_not_ge hh⟩)
      simp only [hH, zero_mul, hz, mul_zero]
  · have hPH : PH (bV j) = 0 := by
      simp only [PH, bV, compactSpectralProjection_eigenbasis, if_neg hj, zero_smul]
    have hPHy : spectralRangeProjection V hcV hpV (Set.Ici (2 * (τ / 2))) (bV j) = 0 := Subtype.ext hPH
    simp only [mul_apply_eq_comp, hPH, map_zero, hae, hRV, map_smul, B,
      ContinuousLinearMap.comp_apply, hPHy, smul_zero]

/-- The closed auxiliary high space contains every strictly high population
vector after applying the actual square root. An atom at `τ` remains excluded
by the strict right projection. -/
theorem auxiliaryPrediction_closedHigh_sqrt_strict (V : H →L[ℝ] H)
    (hcV : IsCompactOperator V) (hpV : V.IsPositive) (τ : ℝ) :
    compactSpectralProjection V hcV hpV (Set.Ici (2 * (τ / 2))) *
        compactRegularizedSqrt V hcV hpV 0 * compactSpectralProjection V hcV hpV (Set.Ioi τ) =
      compactRegularizedSqrt V hcV hpV 0 * compactSpectralProjection V hcV hpV (Set.Ioi τ) := by
  ext z
  apply (compactEigenbasis V hcV hpV.isSymmetric).repr.injective
  ext i
  simp only [mul_apply_eq_comp, compactSpectralProjection_repr, compactRegularizedSqrt_repr,
    show 2 * (τ / 2) = τ by ring, Set.mem_Ici, Set.mem_Ioi]
  by_cases hi : τ < i.1
  · simp only [if_pos hi, if_pos hi.le, one_mul]
  · simp only [if_neg hi, zero_mul, mul_zero]

/-- The actual right outside vector is controlled by the exact source weight
on the strict population high space. This uses the population contraction,
not a bound involving the spectral endpoint. -/
theorem auxiliaryPrediction_right_vector_bound (V : H →L[ℝ] H)
    (hcV : IsCompactOperator V) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M α τ : ℝ} (hMV : ‖V‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ)
    (hα0 : 0 ≤ α) (z : H) :
    ‖spectralRangeProjection V hcV hpV (Set.Ici (2 * (τ / 2)))
        (compactRegularizedInvSqrt V hcV hpV 1
          (compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
            (by norm_num) hα0 hMV hf
              (compactRegularizedSqrt V hcV hpV 0
                (compactSpectralProjection V hcV hpV (Set.Ioi τ) z))))‖ ≤
      ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
        (by norm_num) hα0 hMV hf (compactSpectralProjection V hcV hpV (Set.Ioi τ) z)‖ := by
  let S := compactRegularizedSqrt V hcV hpV 0
  let RV := compactRegularizedInvSqrt V hcV hpV 1
  let a := compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
    (by norm_num) hα0 hMV hf
  let R := compactSpectralProjection V hcV hpV (Set.Ioi τ)
  have heq : RV (a (S (R z))) = (S * RV) (a (R z)) := by
    apply (compactEigenbasis V hcV hpV.isSymmetric).repr.injective
    ext i
    simp only [S, RV, a, compactResidualWeightOperator, mul_apply_eq_comp,
      compactRegularizedSqrt_repr, compactRegularizedInvSqrt_repr V hcV hpV 1 (by norm_num),
      compactSpectralMultiplier_repr]
    ring
  change ‖spectralRangeProjection V hcV hpV (Set.Ici (2 * (τ / 2))) (RV (a (S (R z))))‖ ≤ ‖a (R z)‖
  calc
    _ ≤ 1 * ‖RV (a (S (R z)))‖ :=
      (spectralRangeProjection V hcV hpV (Set.Ici (2 * (τ / 2)))).le_of_opNorm_le
        (spectralRangeProjection_norm_le V hcV hpV (Set.Ici (2 * (τ / 2)))) _
    _ = ‖(S * RV) (a (R z))‖ := by rw [heq, one_mul]
    _ ≤ _ := by simpa only [one_mul] using
      (S * RV).le_of_opNorm_le (compactSqrt_invSqrt_norm_le_one V hcV hpV) (a (R z))

/-- The full auxiliary-difference prediction block from the localized proof.
The exponent range needed by this block is the broader `0 ≤ α ≤ 2`; in
particular it applies to the manuscript's `0 < α ≤ min 1 (2ρ)`. Both original
covariance operators and the actual cutoff filter act on the full Hilbert
space, with no commutation or separability assumption. -/
theorem auxiliary_prediction_difference_bound (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4) (z : H) :
    ‖(compactRegularizedSqrt V hcV hpV 0 *
        actualAuxiliaryInteractionDifference U V hcU hcV hpU hpV φ hMU hMV hf h hτ hτ1 *
        compactRegularizedSqrt V hcV hpV 0 * (1 - lowBlockProjection V hcV hpV τ)) z‖ ≤
      48 * A * (A + 1) * (lowBlockDeviation U V hcV hpV / τ) *
        ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
          (by norm_num) hα0 hMV hf ((1 - lowBlockProjection V hcV hpV τ) z)‖ := by
  obtain ⟨W, hW, hfactor⟩ := auxiliaryPrediction_factorization U V hcU hcV hpU hpV φ
    hMU hMV hf h hα0 hα2 hτ hτ1
  let S := compactRegularizedSqrt V hcV hpV 0
  let RU := compactRegularizedInvSqrt U hcU hpU 1
  let RV := compactRegularizedInvSqrt V hcV hpV 1
  let PH := compactSpectralProjection V hcV hpV (Set.Ici (2 * (τ / 2)))
  let R := compactSpectralProjection V hcV hpV (Set.Ioi τ)
  let D := actualAuxiliaryInteractionDifference U V hcU hcV hpU hpV φ hMU hMV hf h hτ hτ1
  let a := compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α) (by norm_num) hα0 hMV hf
  let K := auxiliaryPredictionMixedBlock U V hcU hcV hpU hpV τ
  let B := ((AuxiliaryLowSpace U hcU hpU τ).subtypeL.comp (W K)).comp
    (spectralRangeProjection V hcV hpV (Set.Ici (2 * (τ / 2))))
  let y := spectralRangeProjection V hcV hpV (Set.Ici (2 * (τ / 2))) (RV (a (S (R z))))
  let δ := lowBlockDeviation U V hcV hpV
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) ((norm_nonneg V).trans hMV)
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hW0 : 0 ≤ 12 * A * (A + 1) / τ := by positivity
  have hK : ‖K‖ ≤ 2 * δ := auxiliaryPredictionMixedBlock_norm_le U V hcU hcV hpU hpV τ hδ
  have hWK : ‖W K‖ ≤ (12 * A * (A + 1) / τ) * (2 * δ) :=
    (W.le_of_opNorm_le hW K).trans (mul_le_mul_of_nonneg_left hK hW0)
  have hy : ‖y‖ ≤ ‖a (R z)‖ := auxiliaryPrediction_right_vector_bound V hcV hpV φ hMV hf hα0 z
  have hleft : ‖S * RU‖ ≤ 2 := (compactSqrt_cross_invSqrt_norm_le U V hcU hcV hpU hpV hδ).trans
    (by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)])
  have hPHR : PH * S * R = S * R := auxiliaryPrediction_closedHigh_sqrt_strict V hcV hpV τ
  change D * PH = RU * B * RV * a at hfactor
  have hid : S * D * S * R = (S * RU) * B * RV * a * S * R := by
    calc
      _ = S * D * (PH * S * R) := by rw [hPHR]; simp only [mul_assoc]
      _ = S * (D * PH) * S * R := by simp only [mul_assoc]
      _ = _ := by rw [hfactor]; simp only [mul_assoc]
  rw [one_sub_lowBlockProjection_eq_strict]
  change ‖(S * D * S * R) z‖ ≤ _
  rw [hid]
  change ‖(S * RU) (W K y : H)‖ ≤ _
  calc
    _ ≤ 2 * ‖(W K y : H)‖ := (S * RU).le_of_opNorm_le hleft _
    _ = 2 * ‖W K y‖ := rfl
    _ ≤ 2 * (((12 * A * (A + 1) / τ) * (2 * δ)) * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((W K).le_of_opNorm_le hWK y) (by norm_num)
    _ ≤ 2 * (((12 * A * (A + 1) / τ) * (2 * δ)) * ‖a (R z)‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (by positivity)) (by norm_num)
    _ = _ := by simp only [div_eq_mul_inv]; ring

end
end KernelSeq
