import KernelSeq.LocalizedInteraction
import KernelSeq.LocalizedLowBlock
import KernelSeq.FilteredRHSBound
import KernelSeq.LipschitzHS

/-!
# The actual noncommuting localized high--low block

The closed high spectral restriction used by the separated multiplier contains
its boundary atom. The final strict high projection is applied separately, so
an atom at `2τ` is never silently identified with the strict high block.
-/

namespace KernelSeq

open Submodule
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance highLowAmbientNormedSpace : NormedSpace ℝ H := InnerProductSpace.toNormedSpace

local instance highLowOperatorsNormedAddCommGroup
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedAddCommGroup (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ) :=
  inferInstance

local instance highLowOperatorsNormedSpace
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedSpace ℝ (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ) :=
  inferInstance

/-- The actual projection into the constructed spectral range. -/
def spectralRangeProjection (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hp : T.IsPositive) (s : Set ℝ) : H →L[ℝ] SpectralSubspace T hc hp s :=
  (compactSpectralProjection T hc hp s).rangeRestrict

theorem spectralRangeProjection_norm_le (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hp : T.IsPositive) (s : Set ℝ) : ‖spectralRangeProjection T hc hp s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (compactSpectralProjection T hc hp s).le_of_opNorm_le
    (compactSpectralProjection_norm_le_one T hc hp s) x

/-- Every selected eigenvector has the expected actual projection action. -/
theorem compactSpectralProjection_eigenbasis (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (i : CompactSpectralIndex T) :
    compactSpectralProjection T hc hp s (compactEigenbasis T hc hp.isSymmetric i) =
      (if i.1 ∈ s then (1 : ℝ) else 0) • compactEigenbasis T hc hp.isSymmetric i := by
  classical
  unfold compactSpectralProjection
  exact compactSpectralMultiplier_eigen T hc hp (fun t => if t ∈ s then 1 else 0) 1
    zero_le_one (fun _ _ => by split_ifs <;> norm_num) (compactEigenbasis_eigen T hc hp.isSymmetric i)

/-- The complement of the closed low projection is the strict high projection,
including the boundary atom in the low component as in the manuscript. -/
theorem one_sub_lowBlockProjection_eq_strict (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) :
    1 - lowBlockProjection T hc hp τ = compactSpectralProjection T hc hp (Set.Ioi τ) := by
  classical
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [lowBlockProjection, _root_.sub_apply, one_apply_eq_self, map_sub,
    lp.coeFn_sub, Pi.sub_apply, compactSpectralProjection_repr]
  have hi := compactEigenvalue_nonneg T hc hp i
  by_cases h : i.1 ≤ τ
  · simp [Set.mem_Icc, Set.mem_Ioi, hi, h, not_lt.mpr h]
  · simp [Set.mem_Icc, Set.mem_Ioi, hi, h, lt_of_not_ge h]

/-- The strict high projection factors through the closed high space; this
keeps a possible spectral atom at `2τ` explicit. -/
theorem strictHigh_mul_closedHigh (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) :
    compactSpectralProjection T hc hp (Set.Ioi (2 * τ)) *
      compactSpectralProjection T hc hp (Set.Ici (2 * τ)) =
        compactSpectralProjection T hc hp (Set.Ioi (2 * τ)) := by
  classical
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [mul_apply_eq_comp, compactSpectralProjection_repr]
  by_cases hi : 2 * τ < i.1
  · simp [Set.mem_Ioi, Set.mem_Ici, hi, hi.le]
  · simp [Set.mem_Ioi, hi]

/-- The normalized mixed perturbation compressed to the genuine closed
high/low spectral spaces. -/
def localizedMixedBlock (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ :=
  (spectralRangeProjection U hcU hpU (Set.Ici (2 * τ))).comp
    ((manuscriptMixedPerturbation V U hcV hcU hpV hpU 1).comp
      (LowSpectralSpace V hcV hpV τ).subtypeL)

theorem localizedMixedBlock_norm_le (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ)
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4) :
    ‖localizedMixedBlock U V hcU hcV hpU hpV τ‖ ≤ 2 * lowBlockDeviation U V hcV hpV := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg _))
  intro x
  have hP := (spectralRangeProjection U hcU hpU (Set.Ici (2 * τ))).le_of_opNorm_le
    (spectralRangeProjection_norm_le U hcU hpU (Set.Ici (2 * τ)))
    (manuscriptMixedPerturbation V U hcV hcU hpV hpU 1 (x : H))
  have hK := (manuscriptMixedPerturbation V U hcV hcU hpV hpU 1).le_of_opNorm_le
    (manuscriptMixedPerturbation_norm_le V U hcV hcU hpV hpU 1 (by norm_num) hδ) (x : H)
  simp only [one_mul] at hP
  exact hP.trans hK

/-- Actual cross coefficients of the compressed normalized perturbation. -/
theorem localizedMixedBlock_cross_entry (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ)
    (i : CompactSpectralIndex U) (j : CompactSpectralIndex V)
    (hi : 2 * τ ≤ i.1)
    (x : HighSpectralSpace U hcU hpU τ) (y : LowSpectralSpace V hcV hpV τ)
    (hx : (x : H) = compactEigenbasis U hcU hpU.isSymmetric i)
    (hy : (y : H) = compactEigenbasis V hcV hpV.isSymmetric j) :
    inner ℝ x (localizedMixedBlock U V hcU hcV hpU hpV τ y) =
      ((i.1 - j.1) / (Real.sqrt (i.1 + 1) * Real.sqrt (j.1 + 1))) *
        inner ℝ (compactEigenbasis U hcU hpU.isSymmetric i)
          (compactEigenbasis V hcV hpV.isSymmetric j) := by
  have hproj : compactSpectralProjection U hcU hpU (Set.Ici (2 * τ))
      (compactEigenbasis U hcU hpU.isSymmetric i) = compactEigenbasis U hcU hpU.isSymmetric i := by
    simp only [compactSpectralProjection_eigenbasis, Set.mem_Ici, if_pos hi, one_smul]
  change inner ℝ (x : H) (compactSpectralProjection U hcU hpU (Set.Ici (2 * τ))
    (manuscriptMixedPerturbation V U hcV hcU hpV hpU 1 (y : H))) = _
  rw [hx, hy]
  calc
    _ = inner ℝ (compactSpectralProjection U hcU hpU (Set.Ici (2 * τ))
        (compactEigenbasis U hcU hpU.isSymmetric i))
        (manuscriptMixedPerturbation V U hcV hcU hpV hpU 1
          (compactEigenbasis V hcV hpV.isSymmetric j)) :=
      (compactSpectralProjection_isSymmetric U hcU hpU (Set.Ici (2 * τ)) _ _).symm
    _ = _ := by rw [hproj]; exact compactMixedDifference_cross_entry U V hcU hcV hpU hpV 1 (by norm_num) i j

omit [CompleteSpace H] in
/-- Equality on a genuine Hilbert basis extends to bounded operators by their
actual norm-convergent expansions, without a countable-index assumption. -/
theorem highLow_hilbertBasis_ext {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : HilbertBasis ι ℝ H) {L R : H →L[ℝ] E} (he : ∀ i, L (b i) = R (b i)) : L = R := by
  ext z
  have hL := (b.hasSum_repr z).mapL L
  have hR := (b.hasSum_repr z).mapL R
  have heq : (fun i => L (b.repr z i • b i)) = (fun i => R (b.repr z i • b i)) := by
    funext i
    simp only [map_smul, he i]
  rw [heq] at hL
  exact hL.unique hR

theorem compactInteraction_cross_entry (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (i : CompactSpectralIndex U) (j : CompactSpectralIndex V) :
    inner ℝ (compactEigenbasis U hcU hpU.isSymmetric i)
      (compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h
        (compactEigenbasis V hcV hpV.isSymmetric j)) =
      (φ i.1 * ResidualFilter.residual φ j.1 - ResidualFilter.residual φ i.1 * φ j.1) *
        inner ℝ (compactEigenbasis U hcU hpU.isSymmetric i)
          (compactEigenbasis V hcV hpV.isSymmetric j) := by
  have hF : compactFilterOperator V hcV hpV φ (by norm_num) hMV h
      (compactEigenbasis V hcV hpV.isSymmetric j) =
      φ j.1 • compactEigenbasis V hcV hpV.isSymmetric j := by
    unfold compactFilterOperator
    exact compactSpectralMultiplier_eigen _ _ _ _ _ _ _ (compactEigenbasis_eigen V hcV hpV.isSymmetric j)
  have hR : compactResidualOperator V hcV hpV φ hMV hf
      (compactEigenbasis V hcV hpV.isSymmetric j) =
      ResidualFilter.residual φ j.1 • compactEigenbasis V hcV hpV.isSymmetric j := by
    unfold compactResidualOperator
    exact compactSpectralMultiplier_eigen _ _ _ _ _ _ _ (compactEigenbasis_eigen V hcV hpV.isSymmetric j)
  change inner ℝ _ (compactFilterOperator U hcU hpU φ (by norm_num) hMU h
      (compactResidualOperator V hcV hpV φ hMV hf _) -
    compactResidualOperator U hcU hpU φ hMU hf
      (compactFilterOperator V hcV hpV φ (by norm_num) hMV h _)) = _
  rw [hF, hR, map_smul, map_smul, inner_sub_right, inner_smul_right, inner_smul_right]
  simp only [compactFilterOperator, compactResidualOperator,
    ← HilbertBasis.repr_apply_apply, compactSpectralMultiplier_repr]
  ring

/-- The population square-root/inverse-root pair is an actual contraction. -/
theorem compactSqrt_invSqrt_norm_le_one (V : H →L[ℝ] H)
    (hcV : IsCompactOperator V) (hpV : V.IsPositive) :
    ‖compactRegularizedSqrt V hcV hpV 0 * compactRegularizedInvSqrt V hcV hpV 1‖ ≤ 1 := by
  let R := compactRegularizedInvSqrt V hcV hpV 1
  let S := compactRegularizedSqrt V hcV hpV 0
  have heq : (S * R).adjoint * (S * R) = compactNormalizedCovariance V hcV hpV 1 := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      (compactRegularizedInvSqrt_isSelfAdjoint V hcV hpV 1).adjoint_eq,
      (compactRegularizedSqrt_isSelfAdjoint V hcV hpV 0).adjoint_eq, S, R]
    change R * S * (S * R) = R * V * R
    rw [show R * S * (S * R) = R * (S * S) * R by simp only [mul_assoc],
      compactRegularizedSqrt_sq V hcV hpV 0 (by norm_num)]
    simp
  have hs : ‖S * R‖ ^ 2 ≤ 1 := by
    rw [pow_two, ← ContinuousLinearMap.norm_adjoint_comp_self]
    exact (congrArg norm heq).trans_le (compactNormalizedCovariance_norm_le_one V hcV hpV 1 (by norm_num))
  change ‖S * R‖ ≤ 1
  nlinarith [norm_nonneg (S * R)]

theorem highLow_scalar_root_cancellation {u v a N c : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u - v ≠ 0) (ha : a ≠ 0) :
    ((Real.sqrt (v + 1))⁻¹ * a) * (Real.sqrt (u + 1))⁻¹ *
      ((1 + u) * (1 + v) * N / ((u - v) * a) *
        ((u - v) / (Real.sqrt (u + 1) * Real.sqrt (v + 1))) * c) = N * c := by
  have hsu : Real.sqrt (u + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have hsv : Real.sqrt (v + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  rw [show 1 + u = (Real.sqrt (u + 1)) ^ 2 by rw [Real.sq_sqrt (by linarith)]; ring,
    show 1 + v = (Real.sqrt (v + 1)) ^ 2 by rw [Real.sq_sqrt (by linarith)]; ring]
  field_simp

/-- The separated multiplier recovers the genuine ambient closed high/low
interaction from the actual mixed normalized perturbation. This identity is
proved on two complete compact spectral bases, rather than assumed as a DOI
factorization certificate. The weight exponent zero suffices on the low block. -/
theorem localized_highLow_factorization (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτA : τ ≤ 1 / (4 * (A + 1))) :
    ∃ W : (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ) →L[ℝ]
        (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ),
      ‖W‖ ≤ 24 * A / τ ∧
      compactSpectralProjection U hcU hpU (Set.Ici (2 * τ)) *
          compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h *
          lowBlockProjection V hcV hpV τ =
        compactRegularizedInvSqrt U hcU hpU 1 *
          (((HighSpectralSpace U hcU hpU τ).subtypeL.comp
            (W (localizedMixedBlock U V hcU hcV hpU hpV τ))).comp
              (spectralRangeProjection V hcV hpV (Set.Icc 0 τ))) *
          compactRegularizedInvSqrt V hcV hpV 1 *
          compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := 0)
            (by norm_num) (by norm_num) hMV hf := by
  obtain ⟨W, hW, hcoeff⟩ := actual_localized_separated_multiplier (α := 0)
    U V hcU hcV hpU hpV φ hMU hMV hf h hτ hτ1 hτA
  refine ⟨W, hW, ?_⟩
  let bU := compactEigenbasis U hcU hpU.isSymmetric
  let bV := compactEigenbasis V hcV hpV.isSymmetric
  let RU := compactRegularizedInvSqrt U hcU hpU 1
  let RV := compactRegularizedInvSqrt V hcV hpV 1
  let PH := compactSpectralProjection U hcU hpU (Set.Ici (2 * τ))
  let Q := lowBlockProjection V hcV hpV τ
  let J := compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h
  let a := compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := 0)
    (by norm_num) (by norm_num) hMV hf
  let K := localizedMixedBlock U V hcU hcV hpU hpV τ
  let B := ((HighSpectralSpace U hcU hpU τ).subtypeL.comp (W K)).comp
    (spectralRangeProjection V hcV hpV (Set.Icc 0 τ))
  change PH * J * Q = RU * B * RV * a
  apply highLow_hilbertBasis_ext bV
  intro j
  have hae : a (bV j) = residualWeight 1 0 φ j.1 • bV j := by
    exact compactSpectralMultiplier_eigen V hcV hpV _ _ _ _ (compactEigenbasis_eigen V hcV hpV.isSymmetric j)
  have hRV : RV (bV j) = (Real.sqrt (j.1 + 1))⁻¹ • bV j :=
    compactRegularizedInvSqrt_eigenbasis V hcV hpV 1 (by norm_num) j
  by_cases hj : j.1 ∈ Set.Icc (0 : ℝ) τ
  · have hQ : Q (bV j) = bV j := by
      simp only [Q, bV, lowBlockProjection, compactSpectralProjection_eigenbasis, if_pos hj, one_smul]
    let y : LowSpectralSpace V hcV hpV τ := ⟨bV j, ⟨bV j, hQ⟩⟩
    have hQy : spectralRangeProjection V hcV hpV (Set.Icc 0 τ) (bV j) = y := Subtype.ext hQ
    have hright : (RU * B * RV * a) (bV j) =
        ((Real.sqrt (j.1 + 1))⁻¹ * residualWeight 1 0 φ j.1) • RU (W K y : H) := by
      simp only [mul_apply_eq_comp, hae, hRV, map_smul, B, ContinuousLinearMap.comp_apply, hQy,
        Submodule.subtypeL_apply, smul_smul]
      congr 1
      ring
    have hleft : (PH * J * Q) (bV j) = PH (J (bV j)) := by
      simp only [mul_apply_eq_comp, hQ]
    rw [hright, hleft]
    apply bU.repr.injective
    ext i
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    have hRU : bU.repr (RU (W K y : H)) i =
        (Real.sqrt (i.1 + 1))⁻¹ * bU.repr (W K y : H) i :=
      compactRegularizedInvSqrt_repr U hcU hpU 1 (by norm_num) _ i
    rw [hRU]
    change bU.repr (compactSpectralProjection U hcU hpU (Set.Ici (2 * τ)) (J (bV j))) i = _
    rw [compactSpectralProjection_repr]
    by_cases hi : 2 * τ ≤ i.1
    · have hPH : PH (bU i) = bU i := by
        simp only [PH, bU, compactSpectralProjection_eigenbasis, Set.mem_Ici, if_pos hi, one_smul]
      let x : HighSpectralSpace U hcU hpU τ := ⟨bU i, ⟨bU i, hPH⟩⟩
      have hw := hcoeff K x y i.1 j.1 (compactEigenbasis_eigen U hcU hpU.isSymmetric i)
        (compactEigenbasis_eigen V hcV hpV.isSymmetric j) hi hj
      have hk := localizedMixedBlock_cross_entry U V hcU hcV hpU hpV τ i j hi x y rfl rfl
      have hJ := compactInteraction_cross_entry U V hcU hcV hpU hpV φ hMU hMV hf h i j
      have ha : residualWeight 1 0 φ j.1 ≠ 0 := by
        have ht : j.1 ∈ Set.Icc (0 : ℝ) M :=
          ⟨hj.1, ((le_abs_self j.1).trans (compactEigenvalue_norm_le V hcV hpV.isSymmetric j)).trans hMV⟩
        have hh := localized_low_weight_lower (α := 0) ((norm_nonneg V).trans hMV) hf h hτ hτA ht hj.2
        linarith
      simp only [Set.mem_Ici, if_pos hi, one_mul]
      rw [bU.repr_apply_apply, bU.repr_apply_apply]
      change inner ℝ (bU i) (J (bV j)) = _
      rw [hJ]
      change _ = ((Real.sqrt (j.1 + 1))⁻¹ * residualWeight 1 0 φ j.1) *
        ((Real.sqrt (i.1 + 1))⁻¹ * inner ℝ x (W K y))
      rw [hw, hk]
      unfold localizedSeparatedKernel
      simpa only [mul_assoc] using (highLow_scalar_root_cancellation
        (N := φ i.1 * ResidualFilter.residual φ j.1 - ResidualFilter.residual φ i.1 * φ j.1)
        (c := inner ℝ (bU i) (bV j)) (compactEigenvalue_nonneg U hcU hpU i)
        (compactEigenvalue_nonneg V hcV hpV j) (by linarith [hj.2]) ha).symm
    · have hz := spectralSubspace_coefficient_eq_zero U hcU hpU (Set.Ici (2 * τ))
        (W K y) i hi
      change bU.repr (W K y : H) i = 0 at hz
      simp only [Set.mem_Ici, if_neg hi, zero_mul, hz, mul_zero]
  · have hQ : Q (bV j) = 0 := by
      simp only [Q, bV, lowBlockProjection, compactSpectralProjection_eigenbasis, if_neg hj, zero_smul]
    have hQy : spectralRangeProjection V hcV hpV (Set.Icc 0 τ) (bV j) = 0 := Subtype.ext hQ
    simp only [mul_apply_eq_comp, hQ, map_zero, hae, hRV, map_smul, B,
      ContinuousLinearMap.comp_apply, hQy, smul_zero]

/-- An inverse root commutes with its own actual spectral projection. -/
theorem compactInvSqrt_spectralProjection_commute (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    compactSpectralProjection T hc hp s * compactRegularizedInvSqrt T hc hp 1 =
      compactRegularizedInvSqrt T hc hp 1 * compactSpectralProjection T hc hp s := by
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [mul_apply_eq_comp, compactSpectralProjection_repr,
    compactRegularizedInvSqrt_repr T hc hp 1 (by norm_num)]
  ring

/-- The actual outside empirical inverse-root factor follows from population
normalization and the actual relative-Loewner root transition. -/
theorem compactSqrt_cross_invSqrt_norm_le (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive)
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4) :
    ‖compactRegularizedSqrt V hcV hpV 0 * compactRegularizedInvSqrt U hcU hpU 1‖ ≤
      Real.sqrt 2 := by
  let S := compactRegularizedSqrt V hcV hpV 0
  let RV := compactRegularizedInvSqrt V hcV hpV 1
  let RU := compactRegularizedInvSqrt U hcU hpU 1
  let B := rootTransition V U hcV hcU hpV hpU 1
  have hfac : S * RU = (S * RV) * B := by
    dsimp only [B, rootTransition]
    calc
      _ = S * (RV * compactRegularizedSqrt V hcV hpV 1) * RU := by
        rw [show RV * compactRegularizedSqrt V hcV hpV 1 = 1 from
          compactRegularizedInvSqrt_mul_sqrt V hcV hpV 1 (by norm_num)]
        simp
      _ = _ := by simp only [RU, mul_assoc]
  rw [show compactRegularizedSqrt V hcV hpV 0 * compactRegularizedInvSqrt U hcU hpU 1 = S * RU from rfl, hfac]
  calc
    _ ≤ ‖S * RV‖ * ‖B‖ := norm_mul_le _ _
    _ ≤ 1 * Real.sqrt 2 := mul_le_mul (compactSqrt_invSqrt_norm_le_one V hcV hpV)
      (rootTransition_norm_le V U hcV hcU hpV hpU 1 (by norm_num)
        (hδ.trans (by norm_num))) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The actual right outside vector is controlled on the population low
space. The weight `a=ψ+1` is the exponent-zero weight used in the exact
factorization above; its bound two follows from the original spectral filter. -/
theorem localized_highLow_right_vector_bound (V : H →L[ℝ] H)
    (hcV : IsCompactOperator V) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A τ : ℝ} (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hτ : 0 < τ) (hτA : τ ≤ 1 / (4 * (A + 1))) (z : H) :
    ‖spectralRangeProjection V hcV hpV (Set.Icc 0 τ)
        (compactRegularizedInvSqrt V hcV hpV 1
          (compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := 0)
            (by norm_num) (by norm_num) hMV hf (compactRegularizedSqrt V hcV hpV 0 z)))‖ ≤
      4 * ‖compactResidualOperator V hcV hpV φ hMV hf z‖ := by
  let S := compactRegularizedSqrt V hcV hpV 0
  let RV := compactRegularizedInvSqrt V hcV hpV 1
  let a := compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := 0)
    (by norm_num) (by norm_num) hMV hf
  let Q := lowBlockProjection V hcV hpV τ
  have ha : ‖a‖ ≤ 2 := compactSpectralMultiplier_norm_le _ _ _ _ _ _ _
  have heq : Q (RV (a (S z))) = (S * RV) (a (Q z)) := by
    apply (compactEigenbasis V hcV hpV.isSymmetric).repr.injective
    ext i
    simp only [Q, lowBlockProjection, S, RV, a, compactResidualWeightOperator,
      mul_apply_eq_comp, compactSpectralProjection_repr, compactRegularizedSqrt_repr,
      compactRegularizedInvSqrt_repr V hcV hpV 1 (by norm_num), compactSpectralMultiplier_repr]
    ring
  change ‖Q (RV (a (S z)))‖ ≤ _
  rw [heq]
  calc
    _ ≤ 1 * ‖a (Q z)‖ := (S * RV).le_of_opNorm_le (compactSqrt_invSqrt_norm_le_one V hcV hpV) _
    _ ≤ 2 * ‖Q z‖ := by simpa only [one_mul] using a.le_of_opNorm_le ha (Q z)
    _ ≤ 2 * (2 * ‖compactResidualOperator V hcV hpV φ hMV hf z‖) :=
      mul_le_mul_of_nonneg_left (lowBlockProjection_norm_le_residual V hcV hpV φ hMV hf h hτ.le hτA z)
        (by norm_num)
    _ = _ := by ring

/-- The full actual strict-high/population-low interaction block. The only
smallness event is the actual normalized covariance deviation. The multiplier,
its perturbation input, both outside factors, and the residual domination are
all constructed and proved in this module or its imports. -/
theorem localized_high_low_interaction_bound (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hτ : 0 < τ) (hsmall : τ ≤ min 1 (1 / (4 * (A + 1))))
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4) (z : H) :
    ‖(compactRegularizedSqrt V hcV hpV 0 * (1 - lowBlockProjection U hcU hpU (2 * τ)) *
        compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h *
        lowBlockProjection V hcV hpV τ * compactRegularizedSqrt V hcV hpV 0) z‖ ≤
      384 * A * (lowBlockDeviation U V hcV hpV / τ) *
        ‖compactResidualOperator V hcV hpV φ hMV hf z‖ := by
  have hτ1 : τ ≤ 1 := hsmall.trans (min_le_left _ _)
  have hτA : τ ≤ 1 / (4 * (A + 1)) := hsmall.trans (min_le_right _ _)
  obtain ⟨W, hW, hfactor⟩ := localized_highLow_factorization U V hcU hcV hpU hpV φ
    hMU hMV hf h hτ hτ1 hτA
  let S := compactRegularizedSqrt V hcV hpV 0
  let RU := compactRegularizedInvSqrt U hcU hpU 1
  let RV := compactRegularizedInvSqrt V hcV hpV 1
  let PH := compactSpectralProjection U hcU hpU (Set.Ici (2 * τ))
  let D := compactSpectralProjection U hcU hpU (Set.Ioi (2 * τ))
  let Q := lowBlockProjection V hcV hpV τ
  let J := compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h
  let a := compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := 0)
    (by norm_num) (by norm_num) hMV hf
  let K := localizedMixedBlock U V hcU hcV hpU hpV τ
  let B := ((HighSpectralSpace U hcU hpU τ).subtypeL.comp (W K)).comp
    (spectralRangeProjection V hcV hpV (Set.Icc 0 τ))
  let y := spectralRangeProjection V hcV hpV (Set.Icc 0 τ) (RV (a (S z)))
  let δ := lowBlockDeviation U V hcV hpV
  let Ψ := compactResidualOperator V hcV hpV φ hMV hf
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) ((norm_nonneg V).trans hMV)
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hW0 : 0 ≤ 24 * A / τ := by positivity
  have hK : ‖K‖ ≤ 2 * δ := localizedMixedBlock_norm_le U V hcU hcV hpU hpV τ hδ
  have hWK : ‖W K‖ ≤ (24 * A / τ) * (2 * δ) :=
    (W.le_of_opNorm_le hW K).trans (mul_le_mul_of_nonneg_left hK hW0)
  have hy : ‖y‖ ≤ 4 * ‖Ψ z‖ :=
    localized_highLow_right_vector_bound V hcV hpV φ hMV hf h hτ hτA z
  have hleft : ‖S * RU‖ ≤ 2 := (compactSqrt_cross_invSqrt_norm_le U V hcU hcV hpU hpV hδ).trans
    (by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)])
  have hD : ‖D‖ ≤ 1 := compactSpectralProjection_norm_le_one U hcU hpU (Set.Ioi (2 * τ))
  have hDPH : D * PH = D := strictHigh_mul_closedHigh U hcU hpU τ
  have hDRU : D * RU = RU * D := compactInvSqrt_spectralProjection_commute U hcU hpU (Set.Ioi (2 * τ))
  change PH * J * Q = RU * B * RV * a at hfactor
  have hid : S * D * J * Q * S = (S * RU) * D * B * RV * a * S := by
    calc
      _ = S * (D * PH) * J * Q * S := by rw [hDPH]
      _ = S * D * (PH * J * Q) * S := by simp only [mul_assoc]
      _ = S * D * (RU * B * RV * a) * S := by rw [hfactor]
      _ = (S * (D * RU)) * B * RV * a * S := by simp only [mul_assoc]
      _ = _ := by rw [hDRU]; simp only [mul_assoc]
  rw [one_sub_lowBlockProjection_eq_strict]
  change ‖(S * D * J * Q * S) z‖ ≤ _
  rw [hid]
  change ‖(S * RU) (D (W K y : H))‖ ≤ _
  calc
    _ ≤ 2 * ‖D (W K y : H)‖ := (S * RU).le_of_opNorm_le hleft _
    _ ≤ 2 * ‖W K y‖ := by
      change 2 * ‖D (W K y : H)‖ ≤ 2 * ‖(W K y : H)‖
      simpa only [one_mul] using mul_le_mul_of_nonneg_left (D.le_of_opNorm_le hD (W K y : H))
        (by norm_num : (0 : ℝ) ≤ 2)
    _ ≤ 2 * (((24 * A / τ) * (2 * δ)) * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((W K).le_of_opNorm_le hWK y) (by norm_num)
    _ ≤ 2 * (((24 * A / τ) * (2 * δ)) * (4 * ‖Ψ z‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (by positivity)) (by norm_num)
    _ = _ := by simp only [div_eq_mul_inv]; ring

end
end KernelSeq
