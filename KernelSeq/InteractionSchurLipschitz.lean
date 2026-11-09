import KernelSeq.LogInteractionBound
import KernelSeq.ChiSchurDyadic
import KernelSeq.DyadicSchattenEndpoint
import KernelSeq.FiniteDyadicLipschitz

/-!
# Actual interaction bounds with only the Lipschitz leaf

The actual chi multiplier is bounded by its proved strict-step integral.
Only dyadic exponents are needed at the original logarithmic endpoint.
No general HMS theorem or project-specific multiplier certificate is assumed.
-/

open MeasureTheory

namespace KernelSeq
noncomputable section

universe uι uκ uH uE
variable {ι : Type uι} {κ : Type uκ} {H : Type uH} {E : Type uE}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A numerical profile constant, independent of the spectral scale and cutoff.
The numerical value three comes from the proved actual chi step estimate. -/
def lipschitzInteractionConstant (CL α ρ A : ℝ) : ℝ :=
  actualLogInteractionConstant CL 3 α ρ A

theorem factorizedInteraction_dyadic_from_lipschitz {CL A LP LF K α : ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uι, uκ, uH, uE} CL)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (F P θ : ℝ → ℝ) (w : ℝ → ℂ) (hw : Integrable w)
    (hθ : ∀ z, θ z = (∫ ξ, w ξ * Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)).re)
    (hA : 0 ≤ A) (hF : ∀ t, |F t| ≤ A) (hP : ∀ t, |P t| ≤ A) (hP0 : ∀ t, 0 ≤ P t)
    (hLP : 0 ≤ LP) (hLF : 0 ≤ LF)
    (hPlip : ∀ s t, |P s - P t| ≤ LP * |s - t|)
    (hFlip : ∀ s t, |F s - F t| ≤ LF * |s - t|)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ) (m : ℕ)
    (hK : 0 ≤ K)
    (hgrid : ∀ i j, ‖factorizedInteractionGrid F P θ
      (fun t s => interactionChi α (t - s)) x y i j‖ ≤ K)
    (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (hsSchurMultiplier a
      (factorizedInteractionGrid F P θ (fun t s => interactionChi α (t - s)) x y)
      K hK hgrid c) (dyadicSchattenExponent m) ≤
      interactionSchurConstant CL 3 (dyadicSchattenExponent m) A LP LF
        (∫ ξ, ‖w ξ‖) (chiMikhlinBound α) * hsSchattenNorm b c (dyadicSchattenExponent m) := by
  let p := dyadicSchattenExponent m
  have hp : 2 ≤ p := dyadicSchattenExponent_ge_two m
  have hB1 : 1 ≤ chiMikhlinBound α := le_max_left _ _
  have hB : 0 ≤ chiMikhlinBound α := le_trans zero_le_one hB1
  have hfrac : p ≤ p ^ 2 / (p - 1) := by
    apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
    nlinarith
  have hcap : 3 * p ≤ schurSchattenConstant 3 p (chiMikhlinBound α) := by
    unfold schurSchattenConstant
    have hf0 : 0 ≤ p ^ 2 / (p - 1) := le_trans (by linarith) hfrac
    nlinarith [mul_le_mul_of_nonneg_left hB1 (show 0 ≤ 3 * (p ^ 2 / (p - 1)) by positivity)]
  apply hsSchur_schatten_bound_of_finite b a _ K hK hgrid hp
    (interactionSchurConstant_nonneg hLip.constant_nonneg (by norm_num)
      (by linarith) hA hLP hLF (integral_nonneg fun _ => norm_nonneg _) hB)
  intro s t d
  rw [← finiteMatrixSchurColumns_eq (finiteSpectralLabelBasis b s)
    (finiteSpectralLabelBasis a t) _ K hK (fun i j => hgrid i j) d]
  apply finite_factorizedInteraction_schatten_le_of_gridBounds
    (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
    F P θ (fun t s => interactionChi α (t - s)) w hw hθ hA hF hP hP0
    (fun i : t => x i) (fun j : s => y j) d hp
  · exact hLip.bound (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
      (fun i : t => x i) (fun j : s => y j) P LP hLP hPlip m d
  · exact hLip.bound (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
      (fun i : t => x i) (fun j : s => y j) F LF hLF hFlip m d
  · have hchi := finite_chiOffDiagonal_dyadic_le (finiteSpectralLabelBasis b s)
      (finiteSpectralLabelBasis a t) α hα0 hα1 (fun i : t => x i) (fun j : s => y j) m d
    exact hchi.trans (mul_le_mul_of_nonneg_right hcap (hsSchattenNorm_nonneg _ d p))

theorem actualLogInteractionGrid_dyadic_from_lipschitz {CL M α ρ A BF K : ℝ} {φ : ℝ → ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uι, uκ, uH, uE} CL)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (hM : 0 ≤ M) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hφ : ResidualFilter.SpectralFilter M φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ) (hBF : 0 ≤ BF)
    (hFlip : ∀ s ∈ ResidualFilter.logDomain 1 M, ∀ t ∈ ResidualFilter.logDomain 1 M,
      |ResidualFilter.inverseProfile 1 φ s - ResidualFilter.inverseProfile 1 φ t| ≤ BF * |s - t|)
    (u : κ → ℝ) (v : ι → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : ℝ) M) (hv : ∀ j, v j ∈ Set.Icc (0 : ℝ) M)
    (m : ℕ) (hK : 0 ≤ K) (hgrid : ∀ i j, ‖actualLogInteractionGrid α φ u v i j‖ ≤ K)
    (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (hsSchurMultiplier a (actualLogInteractionGrid α φ u v) K hK hgrid c)
        (dyadicSchattenExponent m) ≤
      lipschitzInteractionConstant CL α ρ A * (1 + BF) * dyadicSchattenExponent m *
        hsSchattenNorm b c (dyadicSchattenExponent m) := by
  have heq := actualLogInteractionGrid_factorization hM α φ u v hu hv
  have hgrid' := hgrid
  simp only [heq] at hgrid'
  have hA := h.constant_nonneg (by norm_num : (0 : ℝ) < 1) hM
  have hLP : 0 ≤ A * (1 + ρ - α / 2) := mul_nonneg hA (by linarith)
  have ht := factorizedInteraction_dyadic_from_lipschitz hLip b a
    (extendedLogProfile M hM (logInteractionInverseProfile φ))
    (extendedLogProfile M hM (logInteractionResidualProfile α φ))
    (interactionTheta α) (interactionThetaFourierDensity α)
    (interactionThetaFourierDensity_integrable hα0 hα1)
    (interactionTheta_real_density_integral hα0 hα1)
    hA (extendedLogProfile_abs_le hM _ (fun t ht => logInteractionInverseProfile_abs_le h ht))
    (extendedLogProfile_abs_le hM _ (fun t ht => logInteractionResidualProfile_abs_le h hαρ ht))
    (extendedLogProfile_nonneg hM _ (fun t ht => logInteractionResidualProfile_nonneg hφ hM ht))
    hLP hBF
    (extendedLogProfile_lipschitz hM _ hLP
      (fun s hs t ht => logInteractionResidualProfile_lipschitz h hαρ hs ht))
    (extendedLogProfile_lipschitz hM _ hBF (by
      intro s hs t ht
      simpa only [logInteractionInverseProfile_eq] using hFlip s hs t ht))
    hα0 hα1 (fun i => Real.log (1 + u i)) (fun j => Real.log (1 + v j)) m hK hgrid' c
  have hfinal := ht.trans (mul_le_mul_of_nonneg_right
    (interactionSchurConstant_le_profile hLip.constant_nonneg (by norm_num)
      (dyadicSchattenExponent_ge_two m) hA hLP hBF
      (interactionThetaFourierL1_nonneg α) (chiMikhlinBound_nonneg α))
        (hsSchattenNorm_nonneg b c (dyadicSchattenExponent m)))
  simpa only [heq, lipschitzInteractionConstant, actualLogInteractionConstant,
    interactionThetaFourierL1] using hfinal

end
end KernelSeq
