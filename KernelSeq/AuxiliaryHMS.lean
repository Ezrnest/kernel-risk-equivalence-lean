import KernelSeq.CompactInteractionBound
import KernelSeq.AuxiliaryInverse
import KernelSeq.LocalizedAssembly

/-!
# The actual auxiliary HMS bound and closed dimensionless localization

The proved auxiliary residual contract and inverse-profile Lipschitz bound
supply the actual compact interaction theorem. The auxiliary source weight is
proved equal to the original one on the strict population high space. The
bound is optimized over all p≥2 using the genuine Schatten endpoint, then fed
into the proved four-block localized assembly.

Only the general finite Lipschitz Schur and finite C1 HMS propositions remain
external. No auxiliary interaction, symbol, Schur-output, or localized core
bound is a premise. Constants are independent of M and the cutoff τ.
-/

namespace KernelSeq

noncomputable section
attribute [local instance] Classical.propDecidable

universe uH uI
variable {H : Type uH} {I : Type uI}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual auxiliary and original source weights agree on the strict
population high space. The cutoff atom itself is left in the low space. -/
theorem auxiliary_residualWeight_high_eq (V : H →L[ℝ] H) (hcV : IsCompactOperator V)
    (hpV : V.IsPositive) (φ : ℝ → ℝ) {M α τ : ℝ}
    (hMV : ‖V‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ) (hα : 0 ≤ α)
    (hτ : 0 < τ) (z : H) :
    compactResidualWeightOperator V hcV hpV (ResidualFilter.auxiliaryFilter 1 τ φ)
        (lam := 1) (α := α) (by norm_num) hα hMV hf.auxiliary ((1 - lowBlockProjection V hcV hpV τ) z) =
      compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α) (by norm_num) hα hMV hf
        ((1 - lowBlockProjection V hcV hpV τ) z) := by
  rw [one_sub_lowBlockProjection_eq_strict]
  apply (compactEigenbasis V hcV hpV.isSymmetric).repr.injective
  ext i
  simp only [compactResidualWeightOperator, compactSpectralMultiplier_repr, compactSpectralProjection_repr]
  by_cases hi : i.1 ∈ Set.Ioi τ
  · rw [if_pos hi]
    have heq : ResidualFilter.auxiliaryFilter 1 τ φ i.1 = φ i.1 :=
      ResidualFilter.auxiliary_eq_original (by norm_num) hτ φ (by change τ < i.1 at hi; nlinarith)
    simp only [residualWeight, ResidualFilter.residual, ResidualFilter.shrinkage, heq]
  · rw [if_neg hi]
    ring

/-- A uniform p-bound passes to the actual infimum endpoint. The zero
coefficient branch avoids division by zero and includes zero source weights. -/
theorem le_mul_hsSchattenEndpoint_of_forall (b : HilbertBasis I ℝ H)
    (c : HilbertSchmidtColumns I H) {N K : ℝ} (hK : 0 ≤ K)
    (h : ∀ p : ℝ, 2 ≤ p → N ≤ K * (p * hsSchattenNorm b c p)) :
    N ≤ K * hsSchattenEndpoint b c := by
  by_cases hK0 : K = 0
  · simpa only [hK0, zero_mul] using h 2 le_rfl
  · have hKp : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    have hi : N / K ≤ hsSchattenEndpoint b c := by
      apply le_csInf
      · exact ⟨_, Set.mem_range_self (⟨2, le_rfl⟩ : {p : ℝ // 2 ≤ p})⟩
      · rintro _ ⟨p, rfl⟩
        exact (div_le_iff₀ hKp).mpr (by simpa only [mul_comm K] using h p.1 p.2)
    exact (div_le_iff₀ hKp).mp hi |>.trans_eq (mul_comm _ _)

/-- The uniform auxiliary embedded constant. Absolute value only makes its
nonnegativity explicit; the actual multiplier constant was proved upstream.
It depends on the original filter constants and α, not M or τ. -/
def auxiliaryHMSConstant (CL CH α ρ A : ℝ) : ℝ :=
  Real.sqrt 2 * |actualLogInteractionConstant CL CH α ρ (ResidualFilter.auxiliaryConstant ρ A)| *
    (1 + A * (13 + 4 * ρ))

theorem auxiliaryHMSConstant_nonneg {CL CH α ρ A : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) :
    0 ≤ auxiliaryHMSConstant CL CH α ρ A := by
  unfold auxiliaryHMSConstant
  positivity

set_option maxHeartbeats 800000 in
/-- The actual high-space auxiliary interaction bound from only the two
universal finite analytic leaves and the original filter assumptions. The
inverse profile has its proved `A(13+4ρ)/τ` Lipschitz constant; no auxiliary
operator estimate is supplied as a premise. -/
theorem auxiliary_embedded_endpoint_bound {CL CH : ℝ}
    (hLip : FiniteLipschitzSchur.{uH, uH, uH, uH} CL)
    (hHMS : FiniteHMS.{uH, uH, uH, uH} CH) (b : HilbertBasis I ℝ H)
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4)
    (c : HilbertSchmidtColumns I H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation V U hcV hcU hpV hpU 1) (z : H) :
    ‖(compactRegularizedSqrt V hcV hpV 0 *
        compactInteraction U V hcU hcV hpU hpV (ResidualFilter.auxiliaryFilter 1 τ φ)
          (by norm_num) hMU hMV hf.auxiliary (h.auxiliary_contract (by norm_num) hτ hτ1) *
        compactRegularizedSqrt V hcV hpV 0 * (1 - lowBlockProjection V hcV hpV τ)) z‖ ≤
      auxiliaryHMSConstant CL CH α ρ A * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α) (by norm_num) hα0.le hMV hf
          ((1 - lowBlockProjection V hcV hpV τ) z)‖ := by
  let R := 1 - lowBlockProjection V hcV hpV τ
  let W := ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α) (by norm_num) hα0.le hMV hf (R z)‖
  let D := actualLogInteractionConstant CL CH α ρ (ResidualFilter.auxiliaryConstant ρ A)
  let L := A * (13 + 4 * ρ)
  let C := auxiliaryHMSConstant CL CH α ρ A
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) ((norm_nonneg V).trans hMV)
  have hρ : 0 ≤ ρ := h.rho_pos.le
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hC : 0 ≤ C := auxiliaryHMSConstant_nonneg hA hρ
  have hW : 0 ≤ W := norm_nonneg _
  have hratio : 1 + L / τ ≤ (1 + L) / τ := by
    apply (le_div_iff₀ hτ).mpr
    rw [add_mul, div_mul_cancel₀ L hτ.ne', one_mul]
    linarith
  have hAll : ∀ p : ℝ, 2 ≤ p →
      ‖(compactRegularizedSqrt V hcV hpV 0 *
          compactInteraction U V hcU hcV hpU hpV (ResidualFilter.auxiliaryFilter 1 τ φ)
            (by norm_num) hMU hMV hf.auxiliary (h.auxiliary_contract (by norm_num) hτ hτ1) *
          compactRegularizedSqrt V hcV hpV 0) (R z)‖ ≤ (C / τ * W) * (p * hsSchattenNorm b c p) := by
    intro p hp
    have hb := compact_embedded_interaction_bound (lam := 1) (M := M) (ρ := ρ)
      (A := ResidualFilter.auxiliaryConstant ρ A) (α := α) (BF := L / τ) (p := p)
      hLip hHMS b U V hcU hcV hpU hpV
      (ResidualFilter.auxiliaryFilter 1 τ φ) (by norm_num) hMU hMV hf.auxiliary
      (h.auxiliary_contract (by norm_num) hτ hτ1) hα0 hα1 hαρ
      (div_nonneg hL hτ.le) (fun s hs t ht => h.auxiliary_inverse_lipschitz (by norm_num) hτ hτ1 hs ht)
      hp hδ c hcK (R z)
    rw [auxiliary_residualWeight_high_eq V hcV hpV φ hMV hf hα0.le hτ z] at hb
    have hp0 : 0 ≤ p := by linarith
    have hSp : 0 ≤ hsSchattenNorm b c p := hsSchattenNorm_nonneg b c p
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_abs_self D) (Real.sqrt_nonneg 2))
          (by positivity : 0 ≤ 1 + L / τ)) hp0) hSp) hW
    have hrat := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ Real.sqrt 2 * |D|)) hp0) hSp) hW
    calc
      _ ≤ Real.sqrt 2 * D * (1 + L / τ) * p * hsSchattenNorm b c p * W := hb
      _ ≤ Real.sqrt 2 * |D| * (1 + L / τ) * p * hsSchattenNorm b c p * W := hmul
      _ ≤ Real.sqrt 2 * |D| * ((1 + L) / τ) * p * hsSchattenNorm b c p * W := hrat
      _ = _ := by dsimp only [C, auxiliaryHMSConstant, D, L]; ring
  have hopt := le_mul_hsSchattenEndpoint_of_forall b c (K := C / τ * W)
    (mul_nonneg (div_nonneg hC hτ.le) hW) hAll
  rw [mul_apply_eq_comp]
  simpa only [C, W, R] using hopt.trans_eq
    (show (C / τ * W) * hsSchattenEndpoint b c = C * (hsSchattenEndpoint b c / τ) * W by ring)


/-- Full actual dimensionless localized interaction. The original auxiliary
and localized core estimates are now conclusions, rather than hypotheses.
Only the two general finite analytic propositions remain external. -/
theorem localized_interaction_of_finite_analytic {CL CH : ℝ}
    (hLip : FiniteLipschitzSchur.{uH, uH, uH, uH} CL)
    (hHMS : FiniteHMS.{uH, uH, uH, uH} CH) (b : HilbertBasis I ℝ H)
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτA : τ ≤ 1 / (4 * (A + 1)))
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4)
    (c : HilbertSchmidtColumns I H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation V U hcV hcU hpV hpU 1) (z : H) :
    ‖(compactRegularizedSqrt V hcV hpV 0 * compactInteraction U V hcU hcV hpU hpV φ
        (by norm_num) hMU hMV hf h * compactRegularizedSqrt V hcV hpV 0) z‖ ≤
      localizedAssemblyConstant A (auxiliaryHMSConstant CL CH α ρ A) *
        (τ + lowBlockDeviation U V hcV hpV / τ) * ‖compactResidualOperator V hcV hpV φ hMV hf z‖ +
      localizedAssemblyConstant A (auxiliaryHMSConstant CL CH α ρ A) * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α) (by norm_num) hα0.le hMV hf z‖ := by
  exact localized_interaction_of_auxiliary_bound b U V hcU hcV hpU hpV φ hMU hMV hf h
    hα0.le (by linarith) hτ hτ1 hτA hδ c hcK (auxiliaryHMSConstant CL CH α ρ A)
    (auxiliary_embedded_endpoint_bound hLip hHMS b U V hcU hcV hpU hpV φ hMU hMV hf h
      hα0 hα1 hαρ hτ hτ1 hδ c hcK) z

end
end KernelSeq
