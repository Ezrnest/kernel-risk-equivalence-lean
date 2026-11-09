import KernelSeq.LocalizedInteraction
import KernelSeq.AuxiliaryFilter

/-!
# The auxiliary correction on the actual low/high spectral block

The difference from the constructed auxiliary filter is supported below
`2τ/3`. Its interaction with the population spectrum above `τ` is controlled
by a genuine bounded linear multiplier on rectangular operator space. The
high-frequency norm is eliminated with the Sylvester equation, so all
constants are independent of the common spectral endpoint.
-/

open LinearMap Module.End Submodule

namespace KernelSeq

noncomputable section
attribute [local instance] Classical.propDecidable

section ReverseSylvester

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Right-inverse Neumann solution of `U X - X V = C`, when `V` is high. -/
def reverseSylvesterSolution (U : F →L[ℝ] F) (V : E →L[ℝ] E) (C : E →L[ℝ] F) :
    E →L[ℝ] F :=
  -rectangularSandwichResolvent U (Ring.inverse V) (C.comp (Ring.inverse V))

theorem reverseSylvester_equation (U : F →L[ℝ] F) (V : E →L[ℝ] E) (C : E →L[ℝ] F)
    (hV : IsUnit V) (hq : ‖U‖ * ‖Ring.inverse V‖ < 1) :
    U.comp (reverseSylvesterSolution U V C) - (reverseSylvesterSolution U V C).comp V = C := by
  have he := congrArg (fun D : E →L[ℝ] F => D.comp V)
    (rectangularSandwichResolvent_equation U (Ring.inverse V) (C.comp (Ring.inverse V)) hq)
  have hi : (Ring.inverse V).comp V = 1 := Ring.inverse_mul_cancel V hV
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc, hi,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id] at he
  simpa only [reverseSylvesterSolution, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.neg_comp, neg_sub_neg] using he

theorem reverseSylvester_norm_le (U : F →L[ℝ] F) (V : E →L[ℝ] E) (C : E →L[ℝ] F)
    {τ : ℝ} (hτ : 0 < τ) (hU : ‖U‖ ≤ 2 * τ / 3)
    (hVinv : ‖Ring.inverse V‖ ≤ 1 / τ) :
    ‖reverseSylvesterSolution U V C‖ ≤ (3 / τ) * ‖C‖ := by
  have htwo : ‖U‖ * ‖Ring.inverse V‖ ≤ 2 / 3 := by
    calc
      _ ≤ (2 * τ / 3) * (1 / τ) := mul_le_mul hU hVinv (norm_nonneg _) (by positivity)
      _ = 2 / 3 := by field_simp
  have hq : ‖U‖ * ‖Ring.inverse V‖ < 1 := by linarith
  have hR := norm_le_of_rectangularSandwich_equation U (Ring.inverse V)
    (C.comp (Ring.inverse V)) _ hq
    (rectangularSandwichResolvent_equation U (Ring.inverse V) (C.comp (Ring.inverse V)) hq)
  rw [reverseSylvesterSolution, norm_neg]
  calc
    _ ≤ ‖C.comp (Ring.inverse V)‖ / (1 - ‖U‖ * ‖Ring.inverse V‖) := hR
    _ ≤ (‖C‖ * (1 / τ)) / (1 - ‖U‖ * ‖Ring.inverse V‖) :=
      div_le_div_of_nonneg_right ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hVinv (norm_nonneg _))) (by linarith)
    _ ≤ (‖C‖ * (1 / τ)) / (1 / 3 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ = (3 / τ) * ‖C‖ := by ring

omit [CompleteSpace F] in
theorem reverseSylvester_unique (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (C X Y : E →L[ℝ] F) (hV : IsUnit V) (hq : ‖U‖ * ‖Ring.inverse V‖ < 1)
    (hX : U.comp X - X.comp V = C) (hY : U.comp Y - Y.comp V = C) : X = Y := by
  have hi : V.comp (Ring.inverse V) = 1 := Ring.mul_inverse_cancel V hV
  have hn (Z : E →L[ℝ] F) (hZ : U.comp Z - Z.comp V = C) :
      Z - U.comp (Z.comp (Ring.inverse V)) = -(C.comp (Ring.inverse V)) := by
    have he := congrArg (fun D : E →L[ℝ] F => D.comp (Ring.inverse V)) hZ
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc, hi,
      ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id] at he
    rw [← he]
    abel
  exact rectangularSandwich_equation_unique U (Ring.inverse V)
    (-(C.comp (Ring.inverse V))) X Y hq (hn X hX) (hn Y hY)

/-- The reverse solution itself is a bounded linear map on operator space. -/
def reverseSylvesterMap (U : F →L[ℝ] F) (V : E →L[ℝ] E) :
    (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (-rectangularSandwichResolvent U (Ring.inverse V)).comp
    ((ContinuousLinearMap.compL ℝ E E F).flip (Ring.inverse V))

omit [CompleteSpace F] in
@[simp]
theorem reverseSylvesterMap_apply (U : F →L[ℝ] F) (V : E →L[ℝ] E) (C : E →L[ℝ] F) :
    reverseSylvesterMap U V C = reverseSylvesterSolution U V C := rfl

/-- Both regularization weights are retained in the reverse multiplier. -/
def reverseRegularizedSylvesterMap (U : F →L[ℝ] F) (V : E →L[ℝ] E) :
    (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (rectangularSandwichMap (1 + U) (1 + V)).comp (reverseSylvesterMap U V)

omit [CompleteSpace F] in
@[simp]
theorem reverseRegularizedSylvesterMap_apply (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (C : E →L[ℝ] F) : reverseRegularizedSylvesterMap U V C =
      (1 + U).comp ((reverseSylvesterSolution U V C).comp (1 + V)) := rfl

/-- The high-frequency norm does not appear: use `X V = U X - C`. -/
theorem reverseRegularizedSylvesterMap_norm_le (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (hV : IsUnit V) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hU : ‖U‖ ≤ 2 * τ / 3) (hVinv : ‖Ring.inverse V‖ ≤ 1 / τ) :
    ‖reverseRegularizedSylvesterMap U V‖ ≤ 12 / τ := by
  have hlow : ‖U‖ ≤ 1 := hU.trans (by linarith)
  have hleft : ‖(1 : F →L[ℝ] F) + U‖ ≤ 2 :=
    (norm_add_le _ _).trans ((add_le_add ContinuousLinearMap.norm_id_le hlow).trans (by norm_num))
  have hq : ‖U‖ * ‖Ring.inverse V‖ < 1 := by
    have hh := mul_le_mul hU hVinv (norm_nonneg (Ring.inverse V))
      (by positivity : 0 ≤ 2 * τ / 3)
    have hid : (2 * τ / 3) * (1 / τ) = (2 / 3 : ℝ) := by field_simp
    rw [hid] at hh
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro C
  let X := reverseSylvesterSolution U V C
  have hX : ‖X‖ ≤ (3 / τ) * ‖C‖ := reverseSylvester_norm_le U V C hτ hU hVinv
  have he : U.comp X - X.comp V = C := reverseSylvester_equation U V C hV hq
  have hXV : X.comp V = U.comp X - C := by rw [← he]; abel
  have hright : ‖X.comp (1 + V)‖ ≤ (6 / τ) * ‖C‖ := by
    calc
      _ = ‖X + (U.comp X - C)‖ := by rw [ContinuousLinearMap.comp_add, hXV]; rfl
      _ ≤ ‖X‖ + (‖U.comp X‖ + ‖C‖) :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
      _ ≤ ‖X‖ + ((2 * τ / 3) * ‖X‖ + ‖C‖) := by
        gcongr
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
      _ = (1 + 2 * τ / 3) * ‖X‖ + ‖C‖ := by ring
      _ ≤ (1 + 2 * τ / 3) * ((3 / τ) * ‖C‖) + ‖C‖ := by gcongr
      _ = ((3 + 3 * τ) / τ) * ‖C‖ := by field_simp; ring
      _ ≤ (6 / τ) * ‖C‖ := by gcongr; linarith
  rw [reverseRegularizedSylvesterMap_apply]
  calc
    _ ≤ ‖(1 : F →L[ℝ] F) + U‖ * ‖X.comp (1 + V)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * ((6 / τ) * ‖C‖) := mul_le_mul hleft hright (norm_nonneg _) (by norm_num)
    _ = (12 / τ) * ‖C‖ := by ring

end ReverseSylvester

section AuxiliaryProfiles

/-- The difference is taken from the actual constructed auxiliary filter. -/
def auxiliaryDifference (τ : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  φ t - ResidualFilter.auxiliaryFilter 1 τ φ t

theorem auxiliaryDifference_factor (τ : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    auxiliaryDifference τ φ t = (1 - ResidualFilter.cutoff (t / τ)) * φ t := by
  unfold auxiliaryDifference ResidualFilter.auxiliaryFilter
  simp only [one_mul]
  ring

/-- Scaling the original auxiliary construction gives exactly the auxiliary
construction of the dimensionless original filter. -/
theorem auxiliaryFilter_dimensionless (lam : ℝ) (hlam : lam ≠ 0) (τ : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    localizedDimensionlessProfile lam (ResidualFilter.auxiliaryFilter lam τ φ) u =
      ResidualFilter.auxiliaryFilter 1 τ (localizedDimensionlessProfile lam φ) u := by
  have hratio : lam * u / (lam * τ) = u / τ := by field_simp
  simp only [localizedDimensionlessProfile, ResidualFilter.auxiliaryFilter, one_mul, hratio]
  ring

theorem auxiliaryDifference_dimensionless (lam : ℝ) (hlam : lam ≠ 0)
    (τ : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    auxiliaryDifference τ (localizedDimensionlessProfile lam φ) u =
      lam * (φ (lam * u) - ResidualFilter.auxiliaryFilter lam τ φ (lam * u)) := by
  unfold auxiliaryDifference
  rw [← auxiliaryFilter_dimensionless lam hlam]
  simp only [localizedDimensionlessProfile]
  ring

theorem auxiliaryDifference_eq_zero {τ t : ℝ} (hτ : 0 < τ) (φ : ℝ → ℝ)
    (ht : 2 * τ / 3 ≤ t) : auxiliaryDifference τ φ t = 0 := by
  have he := ResidualFilter.auxiliary_eq_original (lam := 1) (by norm_num) hτ φ
    (by simpa only [mul_one] using ht)
  simp only [auxiliaryDifference, he, sub_self]

theorem auxiliaryDifference_residual (τ : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    ResidualFilter.residual (ResidualFilter.auxiliaryFilter 1 τ φ) t -
      ResidualFilter.residual φ t = t * auxiliaryDifference τ φ t := by
  simp only [ResidualFilter.residual, ResidualFilter.shrinkage, auxiliaryDifference]
  ring

/-- Exact difference of the two interaction numerators on the population
high spectrum, where the actual auxiliary and original filters agree. -/
theorem auxiliary_interaction_difference {τ v : ℝ} (hτ : 0 < τ) (hv : τ ≤ v)
    (φ : ℝ → ℝ) (u : ℝ) :
    (φ u * ResidualFilter.residual φ v - ResidualFilter.residual φ u * φ v) -
      (ResidualFilter.auxiliaryFilter 1 τ φ u *
          ResidualFilter.residual (ResidualFilter.auxiliaryFilter 1 τ φ) v -
        ResidualFilter.residual (ResidualFilter.auxiliaryFilter 1 τ φ) u *
          ResidualFilter.auxiliaryFilter 1 τ φ v) =
      auxiliaryDifference τ φ u * (ResidualFilter.residual φ v + u * φ v) := by
  have he : ResidualFilter.auxiliaryFilter 1 τ φ v = φ v :=
    ResidualFilter.auxiliary_eq_original (lam := 1) (by norm_num) hτ φ (by nlinarith)
  simp only [ResidualFilter.residual, ResidualFilter.shrinkage, auxiliaryDifference, he]
  ring

/-- Its support, restricted to the true nonnegative spectrum, is below the
cutoff. No claim is made about arbitrary negative extensions of the filter. -/
theorem auxiliaryDifference_spectral_support {M τ : ℝ} (hτ : 0 < τ) (φ : ℝ → ℝ) :
    {t ∈ Set.Icc (0 : ℝ) M | auxiliaryDifference τ φ t ≠ 0} ⊆ Set.Icc 0 (2 * τ / 3) := by
  intro t ht
  refine ⟨ht.1.1, ?_⟩
  by_contra hn
  exact ht.2 (auxiliaryDifference_eq_zero hτ φ (le_of_not_ge hn))

theorem auxiliaryDifference_weighted_bound {M ρ A τ t : ℝ} {φ : ℝ → ℝ}
    (h : ResidualFilter.Contract 1 M ρ A φ) (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |(1 + t) * auxiliaryDifference τ φ t| ≤ A := by
  have hc := ResidualFilter.cutoff_mem (t / τ)
  have hid : (1 + t) * auxiliaryDifference τ φ t =
      (1 - ResidualFilter.cutoff (t / τ)) * ((t + 1) * φ t) := by
    rw [auxiliaryDifference_factor]
    ring
  rw [hid, abs_mul, abs_of_nonneg (sub_nonneg.mpr hc.2)]
  exact (mul_le_mul_of_nonneg_right (by linarith [hc.1] : 1 - ResidualFilter.cutoff (t / τ) ≤ 1)
    (abs_nonneg _)).trans (by simpa only [one_mul] using (h.spectral_size (by norm_num) ht).1)

theorem auxiliaryDifference_bounds {M ρ A τ t : ℝ} {φ : ℝ → ℝ}
    (h : ResidualFilter.Contract 1 M ρ A φ) (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |auxiliaryDifference τ φ t| ≤ A ∧ |t * auxiliaryDifference τ φ t| ≤ A := by
  have hs := auxiliaryDifference_weighted_bound (τ := τ) h ht
  rw [abs_mul, abs_of_nonneg (by linarith [ht.1] : 0 ≤ 1 + t)] at hs
  constructor
  · nlinarith [mul_nonneg ht.1 (abs_nonneg (auxiliaryDifference τ φ t))]
  · rw [abs_mul, abs_of_nonneg ht.1]
    nlinarith [abs_nonneg (auxiliaryDifference τ φ t)]

theorem auxiliary_weight_positive {M α t : ℝ} {φ : ℝ → ℝ}
    (hf : ResidualFilter.SpectralFilter M φ) (ht : t ∈ Set.Icc (0 : ℝ) M) :
    0 < residualWeight 1 α φ t := by
  have hb := regularization_weight_mem (by norm_num : (0 : ℝ) < 1) ht
  exact add_pos_of_nonneg_of_pos (hf.residual_nonneg ht) (Real.rpow_pos_of_pos hb.1 _)

/-- Uniform ratios used on the population high block. The exponent range
needed for this sublemma is only `α ≤ 2`. -/
theorem auxiliary_weight_ratios {M ρ A α t : ℝ} {φ : ℝ → ℝ}
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα : α ≤ 2) (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |ResidualFilter.residual φ t / residualWeight 1 α φ t| ≤ 1 ∧
      |φ t / residualWeight 1 α φ t| ≤ A := by
  have ha := auxiliary_weight_positive (α := α) hf ht
  have hψ := hf.residual_nonneg ht
  have hφ := hf.nonneg t ht
  have hb := regularization_weight_mem (by norm_num : (0 : ℝ) < 1) ht
  have hA := h.constant_nonneg (by norm_num) (ht.1.trans ht.2)
  have hpower : 1 / (t + 1) ≤ (1 / (t + 1)) ^ (α / 2) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hb.1 hb.2
      (show α / 2 ≤ (1 : ℝ) by linarith)
  have hbase : 1 / (t + 1) ≤ residualWeight 1 α φ t := by
    dsimp only [residualWeight]
    linarith
  have hfilter : φ t ≤ A * (1 / (t + 1)) := by
    have hs := h.inverse_size (by norm_num : (0 : ℝ) < 1) ht
    have ht1 : 0 < t + 1 := by linarith [ht.1]
    calc
      _ ≤ A / (t + 1) := (le_div_iff₀ ht1).mpr (by nlinarith only [hs])
      _ = _ := by ring
  rw [abs_div, abs_of_nonneg hψ, abs_of_pos ha,
    abs_div, abs_of_nonneg hφ, abs_of_pos ha]
  constructor
  · apply (div_le_one ha).mpr
    exact le_add_of_nonneg_right (Real.rpow_nonneg hb.1.le _)
  · apply (div_le_iff₀ ha).mpr
    exact hfilter.trans (mul_le_mul_of_nonneg_left hbase hA)

end AuxiliaryProfiles

section AuxiliaryMultiplier

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The plus sign is the exact auxiliary interaction-difference algebra. -/
def auxiliaryNumeratorMap (HU UHU : F →L[ℝ] F) (GV HV : E →L[ℝ] E) :
    (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  localizedNumeratorMap HU (-UHU) GV HV

omit [CompleteSpace F] in
@[simp]
theorem auxiliaryNumeratorMap_apply (HU UHU : F →L[ℝ] F) (GV HV : E →L[ℝ] E)
    (K : E →L[ℝ] F) : auxiliaryNumeratorMap HU UHU GV HV K =
      HU.comp (K.comp GV) + UHU.comp (K.comp HV) := by
  simp only [auxiliaryNumeratorMap, localizedNumeratorMap_apply,
    ContinuousLinearMap.neg_comp, sub_neg_eq_add]

omit [CompleteSpace F] in
theorem auxiliaryNumeratorMap_norm_le (HU UHU : F →L[ℝ] F) (GV HV : E →L[ℝ] E)
    {A : ℝ} (hA : 0 ≤ A) (hHU : ‖HU‖ ≤ A) (hUHU : ‖UHU‖ ≤ A)
    (hGV : ‖GV‖ ≤ 1) (hHV : ‖HV‖ ≤ A) :
    ‖auxiliaryNumeratorMap HU UHU GV HV‖ ≤ A * (A + 1) := by
  calc
    _ ≤ ‖rectangularSandwichMap HU GV‖ + ‖rectangularSandwichMap (-UHU) HV‖ :=
      norm_sub_le (rectangularSandwichMap HU GV) (rectangularSandwichMap (-UHU) HV)
    _ ≤ ‖HU‖ * ‖GV‖ + ‖UHU‖ * ‖HV‖ := by
      simpa only [norm_neg] using add_le_add
        (norm_rectangularSandwichMap_le HU GV) (norm_rectangularSandwichMap_le (-UHU) HV)
    _ ≤ A * 1 + A * A := add_le_add
      (mul_le_mul hHU hGV (norm_nonneg _) hA) (mul_le_mul hUHU hHV (norm_nonneg _) hA)
    _ = A * (A + 1) := by ring

def auxiliaryWeightedMultiplier (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (HU UHU : F →L[ℝ] F) (GV HV : E →L[ℝ] E) :
    (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (reverseRegularizedSylvesterMap U V).comp (auxiliaryNumeratorMap HU UHU GV HV)

theorem auxiliaryWeightedMultiplier_norm_le (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (HU UHU : F →L[ℝ] F) (GV HV : E →L[ℝ] E)
    (hV : IsUnit V) {τ A : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hU : ‖U‖ ≤ 2 * τ / 3) (hVinv : ‖Ring.inverse V‖ ≤ 1 / τ)
    (hA : 0 ≤ A) (hHU : ‖HU‖ ≤ A) (hUHU : ‖UHU‖ ≤ A)
    (hGV : ‖GV‖ ≤ 1) (hHV : ‖HV‖ ≤ A) :
    ‖auxiliaryWeightedMultiplier U V HU UHU GV HV‖ ≤ 12 * A * (A + 1) / τ := by
  calc
    _ ≤ ‖reverseRegularizedSylvesterMap U V‖ * ‖auxiliaryNumeratorMap HU UHU GV HV‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (12 / τ) * (A * (A + 1)) := mul_le_mul
      (reverseRegularizedSylvesterMap_norm_le U V hV hτ hτ1 hU hVinv)
      (auxiliaryNumeratorMap_norm_le HU UHU GV HV hA hHU hUHU hGV hHV)
      (norm_nonneg (auxiliaryNumeratorMap HU UHU GV HV)) (by positivity)
    _ = _ := by ring

theorem auxiliaryWeightedMultiplier_perturbation_identity
    (U : F →L[ℝ] F) (V : E →L[ℝ] E)
    (HU UHU : F →L[ℝ] F) (GV HV : E →L[ℝ] E)
    (hV : IsUnit V) (hq : ‖U‖ * ‖Ring.inverse V‖ < 1)
    (hHU : U.comp HU = HU.comp U) (hUHU : U.comp UHU = UHU.comp U)
    (hGV : V.comp GV = GV.comp V) (hHV : V.comp HV = HV.comp V)
    (C : E →L[ℝ] F) :
    auxiliaryWeightedMultiplier U V HU UHU GV HV (U.comp C - C.comp V) =
      (1 + U).comp ((auxiliaryNumeratorMap HU UHU GV HV C).comp (1 + V)) := by
  have hneg : U.comp (-UHU) = (-UHU).comp U := by
    simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.neg_comp, hUHU]
  have heq := localizedNumeratorMap_sylvester_intertwining U V HU (-UHU) GV HV
    hHU hneg hGV hHV C
  have hsol := reverseSylvester_unique U V
    (auxiliaryNumeratorMap HU UHU GV HV (U.comp C - C.comp V))
    (reverseSylvesterSolution U V (auxiliaryNumeratorMap HU UHU GV HV (U.comp C - C.comp V)))
    (auxiliaryNumeratorMap HU UHU GV HV C) hV hq (reverseSylvester_equation U V _ hV hq) heq
  change (1 + U).comp
    ((reverseSylvesterSolution U V
      (auxiliaryNumeratorMap HU UHU GV HV (U.comp C - C.comp V))).comp (1 + V)) = _
  rw [hsol]

end AuxiliaryMultiplier

section MatrixCoefficients

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem reverseRegularizedSylvesterMap_coefficient
    (U : F →L[ℝ] F) (V : E →L[ℝ] E) (C : E →L[ℝ] F)
    (hV : IsUnit V) (hq : ‖U‖ * ‖Ring.inverse V‖ < 1) (hsU : U.IsSymmetric)
    {x : F} {y : E} {u v : ℝ} (hx : U x = u • x) (hy : V y = v • y)
    (huv : u - v ≠ 0) :
    inner ℝ x (reverseRegularizedSylvesterMap U V C y) =
      (1 + u) * (1 + v) / (u - v) * inner ℝ x (C y) := by
  let X := reverseSylvesterSolution U V C
  have hUinner (z : F) : inner ℝ x (U z) = u * inner ℝ x z := by
    calc
      _ = inner ℝ (U x) z := (hsU x z).symm
      _ = _ := by rw [hx]; simp only [inner_smul_left, conj_trivial]
  have heq := congrArg (fun D : E →L[ℝ] F => inner ℝ x (D y))
    (reverseSylvester_equation U V C hV hq)
  change inner ℝ x (U (X y) - X (V y)) = inner ℝ x (C y) at heq
  rw [inner_sub_right, hUinner, hy, map_smul, inner_smul_right] at heq
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
  rw [reverseRegularizedSylvesterMap_apply]
  change inner ℝ x (((1 : F →L[ℝ] F) + U) (X (((1 : E →L[ℝ] E) + V) y))) = _
  rw [hweight_right, map_smul, hweight_left, inner_smul_right, hcoeff]
  ring

end MatrixCoefficients

section ActualBlocks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev AuxiliaryLowSpace (U : H →L[ℝ] H) (hcU : IsCompactOperator U) (hpU : U.IsPositive) (τ : ℝ) :=
  LowSpectralSpace U hcU hpU (2 * τ / 3)

abbrev AuxiliaryHighSpace (V : H →L[ℝ] H) (hcV : IsCompactOperator V) (hpV : V.IsPositive) (τ : ℝ) :=
  HighSpectralSpace V hcV hpV (τ / 2)

local instance : NormedSpace ℝ H := InnerProductSpace.toNormedSpace

local instance auxiliaryOperatorsNormedAddCommGroup
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedAddCommGroup (AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ) :=
  inferInstance

local instance auxiliaryOperatorsNormedSpace
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedSpace ℝ (AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ) :=
  inferInstance

/-- The full actual spectral difference operator before restriction. -/
def actualAuxiliaryDifferenceOperator (U : H →L[ℝ] H) (hcU : IsCompactOperator U)
    (hpU : U.IsPositive) (φ : ℝ → ℝ) {M ρ A τ : ℝ} (hMU : ‖U‖ ≤ M)
    (h : ResidualFilter.Contract 1 M ρ A φ) : H →L[ℝ] H :=
  compactSpectralMultiplier U hcU hpU (auxiliaryDifference τ φ) A
    (h.constant_nonneg (by norm_num) ((norm_nonneg U).trans hMU))
    (fun _ ht => (auxiliaryDifference_bounds h ⟨ht.1, ht.2.trans hMU⟩).1)

/-- Spectral support of the original auxiliary construction implies actual
range inclusion, without imposing a support certificate on the operator. -/
theorem actualAuxiliaryDifferenceOperator_mem_low (U : H →L[ℝ] H) (hcU : IsCompactOperator U)
    (hpU : U.IsPositive) (φ : ℝ → ℝ) {M ρ A τ : ℝ} (hMU : ‖U‖ ≤ M)
    (h : ResidualFilter.Contract 1 M ρ A φ) (hτ : 0 < τ) (x : H) :
    actualAuxiliaryDifferenceOperator U hcU hpU φ hMU h (τ := τ) x ∈
      AuxiliaryLowSpace U hcU hpU τ := by
  classical
  let F := actualAuxiliaryDifferenceOperator U hcU hpU φ hMU h (τ := τ)
  refine ⟨F x, ?_⟩
  apply (compactEigenbasis U hcU hpU.isSymmetric).repr.injective
  ext i
  change (compactEigenbasis U hcU hpU.isSymmetric).repr
      (compactSpectralProjection U hcU hpU (Set.Icc 0 (2 * τ / 3)) (F x)) i =
    (compactEigenbasis U hcU hpU.isSymmetric).repr (F x) i
  rw [compactSpectralProjection_repr]
  by_cases hi : i.1 ∈ Set.Icc (0 : ℝ) (2 * τ / 3)
  · simp only [if_pos hi, one_mul]
  · have hnonneg := compactEigenvalue_nonneg U hcU hpU i
    have hnot : ¬i.1 ≤ 2 * τ / 3 := fun ht => hi ⟨hnonneg, ht⟩
    have hz : auxiliaryDifference τ φ i.1 = 0 :=
      auxiliaryDifference_eq_zero hτ φ (le_of_lt (lt_of_not_ge hnot))
    simp only [if_neg hi, zero_mul]
    change 0 = (compactEigenbasis U hcU hpU.isSymmetric).repr
      (compactSpectralMultiplier U hcU hpU (auxiliaryDifference τ φ) A _ _ x) i
    rw [compactSpectralMultiplier_repr, hz, zero_mul]

/-- Four actual spectral operators needed in the auxiliary numerator. This
structure contains operators only; their bounds are proved below. -/
structure AuxiliaryBlockOperators (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) where
  difference : AuxiliaryLowSpace U hcU hpU τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ
  weightedDifference : AuxiliaryLowSpace U hcU hpU τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ
  residualRatio : AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryHighSpace V hcV hpV τ
  filterRatio : AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryHighSpace V hcV hpV τ

/-- Every field is constructed from the actual original and auxiliary
filters on the actual closed spectral ranges. -/
def actualAuxiliaryBlockOperators (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα : α ≤ 2) : AuxiliaryBlockOperators U V hcU hcV hpU hpV τ := by
  have hA := h.constant_nonneg (by norm_num) ((norm_nonneg U).trans hMU)
  exact
    { difference := spectralSubspaceMultiplier U hcU hpU (Set.Icc 0 (2 * τ / 3))
        (auxiliaryDifference τ φ) A hA
        (fun _ ht => (auxiliaryDifference_bounds h ⟨ht.1, ht.2.trans hMU⟩).1)
      weightedDifference := spectralSubspaceMultiplier U hcU hpU (Set.Icc 0 (2 * τ / 3))
        (fun t => t * auxiliaryDifference τ φ t) A hA
        (fun _ ht => (auxiliaryDifference_bounds h ⟨ht.1, ht.2.trans hMU⟩).2)
      residualRatio := spectralSubspaceMultiplier V hcV hpV (Set.Ici (2 * (τ / 2)))
        (fun t => ResidualFilter.residual φ t / residualWeight 1 α φ t) 1 zero_le_one
        (fun _ ht => (auxiliary_weight_ratios hf h hα ⟨ht.1, ht.2.trans hMV⟩).1)
      filterRatio := spectralSubspaceMultiplier V hcV hpV (Set.Ici (2 * (τ / 2)))
        (fun t => φ t / residualWeight 1 α φ t) A hA
        (fun _ ht => (auxiliary_weight_ratios hf h hα ⟨ht.1, ht.2.trans hMV⟩).2) }

/-- The weighted difference really is `U H(U)` on the actual low range. -/
theorem actualAuxiliaryBlockOperators_weightedDifference (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα : α ≤ 2) :
    let d := actualAuxiliaryBlockOperators U V hcU hcV hpU hpV φ hMU hMV hf h hα
    (lowSpectralRestriction U hcU hpU (2 * τ / 3)).comp d.difference = d.weightedDifference := by
  let d : AuxiliaryBlockOperators U V hcU hcV hpU hpV τ :=
    actualAuxiliaryBlockOperators U V hcU hcV hpU hpV φ hMU hMV hf h hα
  let b := compactEigenbasis U hcU hpU.isSymmetric
  have hD (z : AuxiliaryLowSpace U hcU hpU τ) (i : CompactSpectralIndex U) :
      b.repr (d.difference z : H) i = auxiliaryDifference τ φ i.1 * b.repr (z : H) i :=
    compactSpectralMultiplier_repr U hcU hpU (auxiliaryDifference τ φ) A
      (h.constant_nonneg (by norm_num) ((norm_nonneg U).trans hMU))
      (fun _ ht => (auxiliaryDifference_bounds h ⟨ht.1, ht.2.trans hMU⟩).1) (z : H) i
  have hWD (z : AuxiliaryLowSpace U hcU hpU τ) (i : CompactSpectralIndex U) :
      b.repr (d.weightedDifference z : H) i =
        (i.1 * auxiliaryDifference τ φ i.1) * b.repr (z : H) i :=
    compactSpectralMultiplier_repr U hcU hpU (fun t => t * auxiliaryDifference τ φ t) A
      (h.constant_nonneg (by norm_num) ((norm_nonneg U).trans hMU))
      (fun _ ht => (auxiliaryDifference_bounds h ⟨ht.1, ht.2.trans hMU⟩).2) (z : H) i
  ext x
  apply b.repr.injective
  ext i
  change b.repr (U (d.difference x : H)) i = b.repr (d.weightedDifference x : H) i
  rw [compactEigenbasis_repr_apply, hD, hWD]
  ring

theorem actualAuxiliaryBlockOperators_norm_le (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα : α ≤ 2) :
    let d := actualAuxiliaryBlockOperators U V hcU hcV hpU hpV φ hMU hMV hf h hα (τ := τ)
    ‖d.difference‖ ≤ A ∧ ‖d.weightedDifference‖ ≤ A ∧ ‖d.residualRatio‖ ≤ 1 ∧ ‖d.filterRatio‖ ≤ A := by
  exact ⟨spectralSubspaceMultiplier_norm_le _ _ _ _ _ _ _ _,
    spectralSubspaceMultiplier_norm_le _ _ _ _ _ _ _ _,
    spectralSubspaceMultiplier_norm_le _ _ _ _ _ _ _ _,
    spectralSubspaceMultiplier_norm_le _ _ _ _ _ _ _ _⟩

theorem actualAuxiliaryBlockOperators_commutes (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα : α ≤ 2) :
    let d := actualAuxiliaryBlockOperators U V hcU hcV hpU hpV φ hMU hMV hf h hα
    let UL := lowSpectralRestriction U hcU hpU (2 * τ / 3)
    let VH := highSpectralRestriction V hcV hpV (τ / 2)
    UL.comp d.difference = d.difference.comp UL ∧
      UL.comp d.weightedDifference = d.weightedDifference.comp UL ∧
      VH.comp d.residualRatio = d.residualRatio.comp VH ∧
      VH.comp d.filterRatio = d.filterRatio.comp VH := by
  exact ⟨spectralSubspaceMultiplier_commutes _ _ _ _ _ _ _ _,
    spectralSubspaceMultiplier_commutes _ _ _ _ _ _ _ _,
    spectralSubspaceMultiplier_commutes _ _ _ _ _ _ _ _,
    spectralSubspaceMultiplier_commutes _ _ _ _ _ _ _ _⟩

theorem auxiliary_actual_gap (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) {τ : ℝ} (hτ : 0 < τ) :
    let UL := lowSpectralRestriction U hcU hpU (2 * τ / 3)
    let VH := highSpectralRestriction V hcV hpV (τ / 2)
    IsUnit VH ∧ ‖UL‖ ≤ 2 * τ / 3 ∧ ‖Ring.inverse VH‖ ≤ 1 / τ ∧
      ‖UL‖ * ‖Ring.inverse VH‖ < 1 := by
  dsimp only
  have hu := highSpectralRestriction_isUnit V hcV hpV (τ / 2) (by positivity)
  have hl := lowSpectralRestriction_norm_le U hcU hpU (2 * τ / 3) (by positivity)
  have hi : ‖Ring.inverse (highSpectralRestriction V hcV hpV (τ / 2))‖ ≤ 1 / τ := by
    simpa only [show 2 * (τ / 2) = τ by ring] using
      highSpectralRestriction_inverse_norm_le V hcV hpV (τ / 2) (by positivity)
  refine ⟨hu, hl, hi, ?_⟩
  have hh := mul_le_mul hl hi
    (norm_nonneg (Ring.inverse (highSpectralRestriction V hcV hpV (τ / 2))))
    (by positivity : 0 ≤ 2 * τ / 3)
  have hid : (2 * τ / 3) * (1 / τ) = (2 / 3 : ℝ) := by field_simp
  rw [hid] at hh
  linarith

/-- The actual bounded operator-space multiplier for the auxiliary block. -/
def actualAuxiliaryMultiplier (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα : α ≤ 2) :
    (AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ) →L[ℝ]
      (AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ) :=
  let d := actualAuxiliaryBlockOperators U V hcU hcV hpU hpV φ hMU hMV hf h hα
  auxiliaryWeightedMultiplier (lowSpectralRestriction U hcU hpU (2 * τ / 3))
    (highSpectralRestriction V hcV hpV (τ / 2))
    d.difference d.weightedDifference d.residualRatio d.filterRatio

theorem actualAuxiliaryMultiplier_norm_le (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα : α ≤ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ‖actualAuxiliaryMultiplier U V hcU hcV hpU hpV φ hMU hMV hf h hα (τ := τ)‖ ≤
      12 * A * (A + 1) / τ := by
  have hb := actualAuxiliaryBlockOperators_norm_le U V hcU hcV hpU hpV φ hMU hMV hf h hα (τ := τ)
  have hg := auxiliary_actual_gap U V hcU hcV hpU hpV hτ
  exact auxiliaryWeightedMultiplier_norm_le _ _ _ _ _ _ hg.1 hτ hτ1 hg.2.1 hg.2.2.1
    (h.constant_nonneg (by norm_num) ((norm_nonneg U).trans hMU)) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2

theorem actualAuxiliaryMultiplier_perturbation_identity (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα : α ≤ 2) (hτ : 0 < τ)
    (C : AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ) :
    let d := actualAuxiliaryBlockOperators U V hcU hcV hpU hpV φ hMU hMV hf h hα
    let UL := lowSpectralRestriction U hcU hpU (2 * τ / 3)
    let VH := highSpectralRestriction V hcV hpV (τ / 2)
    actualAuxiliaryMultiplier U V hcU hcV hpU hpV φ hMU hMV hf h hα (UL.comp C - C.comp VH) =
      (1 + UL).comp
        ((auxiliaryNumeratorMap d.difference d.weightedDifference d.residualRatio d.filterRatio C).comp
          (1 + VH)) := by
  have hc := actualAuxiliaryBlockOperators_commutes U V hcU hcV hpU hpV φ hMU hMV hf h hα (τ := τ)
  have hg := auxiliary_actual_gap U V hcU hcV hpU hpV hτ
  exact auxiliaryWeightedMultiplier_perturbation_identity _ _ _ _ _ _ hg.1 hg.2.2.2
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 C

/-- The precise auxiliary correction kernel on its actual separated support. -/
def auxiliarySeparatedKernel (τ α : ℝ) (φ : ℝ → ℝ) (u v : ℝ) : ℝ :=
  (1 + u) * (1 + v) * auxiliaryDifference τ φ u *
    (ResidualFilter.residual φ v + u * φ v) / ((u - v) * residualWeight 1 α φ v)

/-- The named actual operator-space multiplier has exactly the manuscript's
`N(u,v)` matrix elements, with the actual constructed auxiliary difference. -/
theorem actualAuxiliaryMultiplier_coefficient (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα : α ≤ 2) (hτ : 0 < τ)
    (K : AuxiliaryHighSpace V hcV hpV τ →L[ℝ] AuxiliaryLowSpace U hcU hpU τ)
    (x : AuxiliaryLowSpace U hcU hpU τ) (y : AuxiliaryHighSpace V hcV hpV τ)
    {u v : ℝ} (hx : U (x : H) = u • (x : H)) (hy : V (y : H) = v • (y : H))
    (hu : u ≤ 2 * τ / 3) (hv : τ ≤ v) :
    inner ℝ x (actualAuxiliaryMultiplier U V hcU hcV hpU hpV φ hMU hMV hf h hα K y) =
      auxiliarySeparatedKernel τ α φ u v * inner ℝ x (K y) := by
  let d : AuxiliaryBlockOperators U V hcU hcV hpU hpV τ :=
    actualAuxiliaryBlockOperators U V hcU hcV hpU hpV φ hMU hMV hf h hα
  let UL := lowSpectralRestriction U hcU hpU (2 * τ / 3)
  let VH := highSpectralRestriction V hcV hpV (τ / 2)
  have hg := auxiliary_actual_gap U V hcU hcV hpU hpV hτ
  have hxu : UL x = u • x := Subtype.ext hx
  have hyv : VH y = v • y := Subtype.ext hy
  have huv : u - v ≠ 0 := by linarith
  have hH : d.difference x = auxiliaryDifference τ φ u • x :=
    spectralSubspaceMultiplier_eigen _ _ _ _ _ _ _ _ hx
  have hUH : d.weightedDifference x = (u * auxiliaryDifference τ φ u) • x :=
    spectralSubspaceMultiplier_eigen _ _ _ _ _ _ _ _ hx
  have hG : d.residualRatio y = (ResidualFilter.residual φ v / residualWeight 1 α φ v) • y :=
    spectralSubspaceMultiplier_eigen _ _ _ _ _ _ _ _ hy
  have hF : d.filterRatio y = (φ v / residualWeight 1 α φ v) • y :=
    spectralSubspaceMultiplier_eigen _ _ _ _ _ _ _ _ hy
  have hsH : d.difference.IsSymmetric := spectralSubspaceMultiplier_isSymmetric _ _ _ _ _ _ _ _
  have hsUH : d.weightedDifference.IsSymmetric := spectralSubspaceMultiplier_isSymmetric _ _ _ _ _ _ _ _
  have hsNeg : (-d.weightedDifference).IsSymmetric := by
    intro z w
    change inner ℝ (-(d.weightedDifference z)) w = inner ℝ z (-(d.weightedDifference w))
    simp only [inner_neg_left, inner_neg_right]
    exact congrArg Neg.neg (hsUH z w)
  have hNeg : (-d.weightedDifference) x = (-(u * auxiliaryDifference τ φ u)) • x := by
    simpa only [_root_.neg_apply, neg_smul] using congrArg Neg.neg hUH
  have hn := localizedNumeratorMap_coefficient d.difference (-d.weightedDifference)
    d.residualRatio d.filterRatio K hsH hsNeg hH hNeg hG hF
  change inner ℝ x (reverseRegularizedSylvesterMap UL VH
    (localizedNumeratorMap d.difference (-d.weightedDifference) d.residualRatio d.filterRatio K) y) = _
  rw [reverseRegularizedSylvesterMap_coefficient UL VH _ hg.1 hg.2.2.2
    (spectralRestriction_isSymmetric U hcU hpU (Set.Icc 0 (2 * τ / 3))) hxu hyv huv, hn]
  simp only [auxiliarySeparatedKernel, div_eq_mul_inv, mul_inv_rev]
  ring

end ActualBlocks

end
end KernelSeq
