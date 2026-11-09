import KernelSeq.AngularSineExpansion

/-!
# Actual rotated anisotropic Riesz symbols

Relates the angular reflection kernel to two concrete real translation
directions. The zero frequency is handled separately. The genuine scalar
bound and angular continuity supply the uniform HS bounds and measurability
needed by the later operator-valued averaging argument.
-/

namespace KernelSeq
noncomputable section

theorem planarRieszSymbol_homogeneous (A : Fin 2 → Fin 2 → ℝ) (s t : ℝ)
    {r : ℝ} (hr : r ≠ 0) :
    planarRieszSymbol A (r * s, r * t) = planarRieszSymbol A (s, t) := by
  have hn : planarQuadraticForm A (r * s, r * t) = r ^ 2 * planarQuadraticForm A (s, t) := by
    unfold planarQuadraticForm
    ring
  have hd : planarFrequencySq (r * s, r * t) = r ^ 2 * planarFrequencySq (s, t) := by
    unfold planarFrequencySq
    ring
  rw [planarRieszSymbol, hn, hd, mul_div_mul_left _ _ (pow_ne_zero 2 hr)]
  rfl

theorem planarReflectionSymbol_abs_le (s t : ℝ) :
    |planarRieszSymbol planarReflectionMatrix (s, t)| ≤ 1 := by
  have hform : planarRieszSymbol planarReflectionMatrix (s, t) = (s ^ 2 - t ^ 2) / (s ^ 2 + t ^ 2) := by
    simp [planarRieszSymbol, planarQuadraticForm, planarFrequencySq, planarReflectionMatrix,
      sub_eq_add_neg]
  rw [hform, abs_div, abs_of_nonneg (show 0 ≤ s ^ 2 + t ^ 2 by positivity)]
  by_cases hd : s ^ 2 + t ^ 2 = 0
  · rw [hd, div_zero]
    norm_num
  · apply (div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm hd))).mpr
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg t]

def rotatedAnisotropicRieszSymbol (r φ : ℝ) (ξ : ℝ × ℝ) : ℝ :=
  planarRieszSymbol planarReflectionMatrix
    ((1 - r) * (ξ.1 * Real.cos (φ / 2) + ξ.2 * Real.sin (φ / 2)),
      (1 + r) * (-ξ.1 * Real.sin (φ / 2) + ξ.2 * Real.cos (φ / 2)))

@[simp]
theorem rotatedAnisotropicRieszSymbol_zero (r φ : ℝ) :
    rotatedAnisotropicRieszSymbol r φ 0 = 0 := by
  simp [rotatedAnisotropicRieszSymbol, planarRieszSymbol, planarQuadraticForm, planarFrequencySq]

theorem rotatedAnisotropicRieszSymbol_abs_le (r φ : ℝ) (ξ : ℝ × ℝ) :
    |rotatedAnisotropicRieszSymbol r φ ξ| ≤ 1 := planarReflectionSymbol_abs_le _ _

/-- Actual nonzero-frequency identification with the angular kernel. -/
theorem rotatedAnisotropicRieszSymbol_eq_angular (r φ : ℝ) (ξ : ℝ × ℝ) (hξ : ξ ≠ 0) :
    rotatedAnisotropicRieszSymbol r φ ξ =
      angularRieszProfile r (2 * Complex.arg (⟨ξ.1, ξ.2⟩ : ℂ) - φ) := by
  let z : ℂ := ⟨ξ.1, ξ.2⟩
  have hz : z ≠ 0 := by
    intro h
    apply hξ
    exact Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hx : ξ.1 = ‖z‖ * Real.cos (Complex.arg z) := (Complex.norm_mul_cos_arg z).symm
  have hy : ξ.2 = ‖z‖ * Real.sin (Complex.arg z) := (Complex.norm_mul_sin_arg z).symm
  have hcoords :
      ((1 - r) * (ξ.1 * Real.cos (φ / 2) + ξ.2 * Real.sin (φ / 2)),
        (1 + r) * (-ξ.1 * Real.sin (φ / 2) + ξ.2 * Real.cos (φ / 2))) =
      (‖z‖ * ((1 - r) * Real.cos (Complex.arg z - φ / 2)),
        ‖z‖ * ((1 + r) * Real.sin (Complex.arg z - φ / 2))) := by
    apply Prod.ext
    · rw [hx, hy, Real.cos_sub]
      ring
    · rw [hx, hy, Real.sin_sub]
      ring
  unfold rotatedAnisotropicRieszSymbol
  rw [hcoords, planarRieszSymbol_homogeneous _ _ _ hr, angularRieszProfile_eq_reflection]
  congr 1
  dsimp only [z]
  ring

theorem angularPlanarRieszProfile_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (angularRieszProfile r) := by
  unfold angularRieszProfile
  apply Continuous.div (by fun_prop) (by unfold angularRieszDenominator; fun_prop)
  intro ψ
  exact ne_of_gt (angularRieszDenominator_pos hr0 hr1 ψ)

theorem rotatedAnisotropicRieszSymbol_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ξ : ℝ × ℝ) : Continuous (fun φ => rotatedAnisotropicRieszSymbol r φ ξ) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simpa only [rotatedAnisotropicRieszSymbol_zero] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · have he : (fun φ => rotatedAnisotropicRieszSymbol r φ ξ) =
        (fun φ => angularRieszProfile r (2 * Complex.arg (⟨ξ.1, ξ.2⟩ : ℂ) - φ)) :=
      funext fun φ => rotatedAnisotropicRieszSymbol_eq_angular r φ ξ hξ
    rw [he]
    exact (angularPlanarRieszProfile_continuous hr0 hr1).comp (by fun_prop)

end
end KernelSeq
