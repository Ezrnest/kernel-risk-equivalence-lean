import KernelSeq.AuxiliaryPredictionBlock
import KernelSeq.MixedEndpointLower

/-!
# Conditional assembly of the actual dimensionless localized interaction

The low--low, strict high--low, and auxiliary-difference blocks are proved
operator estimates. The remaining auxiliary embedded-interaction estimate is
an explicit `haux` binder in `localized_interaction_of_auxiliary_bound`. This
module does not assert that remaining HMS-dependent estimate.

All projections and operators are actual compact spectral constructions, and
the optimized endpoint comes from actual HS columns reconstructing the mixed
perturbation. No scalar kernel bound replaces an operator estimate.
-/

namespace KernelSeq

open scoped BigOperators

noncomputable section

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual source weight is contracted by the strict population high
projection. The spectral atom at the cutoff remains in the low space. -/
theorem residualWeight_high_projection_norm_le (V : H →L[ℝ] H)
    (hcV : IsCompactOperator V) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M α : ℝ} (hMV : ‖V‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ)
    (hα0 : 0 ≤ α) (τ : ℝ) (z : H) :
    ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
        (by norm_num) hα0 hMV hf ((1 - lowBlockProjection V hcV hpV τ) z)‖ ≤
      ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
        (by norm_num) hα0 hMV hf z‖ := by
  rw [one_sub_lowBlockProjection_eq_strict]
  let R := compactSpectralProjection V hcV hpV (Set.Ioi τ)
  let a := compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
    (by norm_num) hα0 hMV hf
  have heq : a (R z) = R (a z) := by
    apply (compactEigenbasis V hcV hpV.isSymmetric).repr.injective
    ext i
    simp only [a, R, compactResidualWeightOperator,
      compactSpectralMultiplier_repr, compactSpectralProjection_repr]
    ring
  change ‖a (R z)‖ ≤ ‖a z‖
  rw [heq]
  simpa only [one_mul] using R.le_of_opNorm_le
    (compactSpectralProjection_norm_le_one V hcV hpV (Set.Ioi τ)) (a z)

/-- The actual normalized covariance deviation is controlled by the actual
mixed optimized Schatten endpoint on the source quarter event. -/
theorem lowBlockDeviation_le_mixedEndpoint (b : HilbertBasis ι ℝ H)
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive)
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4)
    (c : HilbertSchmidtColumns ι H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation V U hcV hcU hpV hpU 1) :
    lowBlockDeviation U V hcV hpV ≤ hsSchattenEndpoint b c :=
  normalizedPerturbation_norm_le_endpoint b V U hcV hcU hpV hpU 1 (by norm_num)
    (hδ.trans (by norm_num)) c hcK

/-- The proved actual auxiliary-difference prediction estimate with the
actual mixed endpoint in place of the normalized deviation. -/
theorem auxiliary_prediction_difference_endpoint_bound (b : HilbertBasis ι ℝ H)
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4)
    (c : HilbertSchmidtColumns ι H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation V U hcV hcU hpV hpU 1) (z : H) :
    ‖(compactRegularizedSqrt V hcV hpV 0 *
        actualAuxiliaryInteractionDifference U V hcU hcV hpU hpV φ hMU hMV hf h hτ hτ1 *
        compactRegularizedSqrt V hcV hpV 0 * (1 - lowBlockProjection V hcV hpV τ)) z‖ ≤
      48 * A * (A + 1) * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
          (by norm_num) hα0 hMV hf ((1 - lowBlockProjection V hcV hpV τ) z)‖ := by
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) ((norm_nonneg V).trans hMV)
  refine (auxiliary_prediction_difference_bound U V hcU hcV hpU hpV φ hMU hMV hf h
    hα0 hα2 hτ hτ1 hδ z).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 48 * A * (A + 1))
  exact div_le_div_of_nonneg_right (lowBlockDeviation_le_mixedEndpoint b U V hcU hcV hpU hpV hδ c hcK) hτ.le

/-- A common constant for conditional localized assembly. It depends only on
`A` and the visible auxiliary-bound constant, and not on `M`, `τ`, or spectra. -/
def localizedAssemblyConstant (A Caux : ℝ) : ℝ :=
  396 * A + 48 * A * (A + 1) + |Caux|

theorem localizedAssemblyConstant_nonneg {A Caux : ℝ} (hA : 0 ≤ A) :
    0 ≤ localizedAssemblyConstant A Caux := by
  unfold localizedAssemblyConstant
  positivity

/-- Conditional localized interaction assembly for actual dimensionless
operators. The binder `haux` is precisely the remaining auxiliary embedded
interaction estimate. It is visible and is not proved or certified here.
All other localized blocks, the endpoint absorption, projection contraction,
and the four-block operator identity are derived from the actual operators. -/
theorem localized_interaction_of_auxiliary_bound (b : HilbertBasis ι ℝ H)
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hτA : τ ≤ 1 / (4 * (A + 1)))
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4)
    (c : HilbertSchmidtColumns ι H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation V U hcV hcU hpV hpU 1)
    (Caux : ℝ)
    (haux : ∀ z : H,
      ‖(compactRegularizedSqrt V hcV hpV 0 *
          compactInteraction U V hcU hcV hpU hpV (ResidualFilter.auxiliaryFilter 1 τ φ)
            (by norm_num) hMU hMV hf.auxiliary (h.auxiliary_contract (by norm_num) hτ hτ1) *
          compactRegularizedSqrt V hcV hpV 0 * (1 - lowBlockProjection V hcV hpV τ)) z‖ ≤
        Caux * (hsSchattenEndpoint b c / τ) *
          ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
            (by norm_num) hα0 hMV hf ((1 - lowBlockProjection V hcV hpV τ) z)‖)
    (z : H) :
    ‖(compactRegularizedSqrt V hcV hpV 0 *
        compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h *
        compactRegularizedSqrt V hcV hpV 0) z‖ ≤
      localizedAssemblyConstant A Caux * (τ + lowBlockDeviation U V hcV hpV / τ) *
        ‖compactResidualOperator V hcV hpV φ hMV hf z‖ +
      localizedAssemblyConstant A Caux * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
          (by norm_num) hα0 hMV hf z‖ := by
  let S := compactRegularizedSqrt V hcV hpV 0
  let P := lowBlockProjection U hcU hpU (2 * τ)
  let Q := lowBlockProjection V hcV hpV τ
  let R := 1 - Q
  let J := compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h
  let Jt := compactInteraction U V hcU hcV hpU hpV (ResidualFilter.auxiliaryFilter 1 τ φ)
    (by norm_num) hMU hMV hf.auxiliary (h.auxiliary_contract (by norm_num) hτ hτ1)
  let D := actualAuxiliaryInteractionDifference U V hcU hcV hpU hpV φ hMU hMV hf h hτ hτ1
  let a := compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α)
    (by norm_num) hα0 hMV hf
  let Ψ := compactResidualOperator V hcV hpV φ hMV hf
  let δ := lowBlockDeviation U V hcV hpV
  let Ξ := hsSchattenEndpoint b c
  let r := τ + δ / τ
  let t := Ξ / τ
  let C := localizedAssemblyConstant A Caux
  let Cdiff := 48 * A * (A + 1)
  let L₁ := S * P * J * Q * S
  let L₂ := S * (1 - P) * J * Q * S
  let L₃ := S * D * S * R
  let L₄ := S * Jt * S * R
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) ((norm_nonneg V).trans hMV)
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδΞ : δ ≤ Ξ := lowBlockDeviation_le_mixedEndpoint b U V hcU hcV hpU hpV hδ c hcK
  have hΞ0 : 0 ≤ Ξ := hδ0.trans hδΞ
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have ht : 0 ≤ t := div_nonneg hΞ0 hτ.le
  have hCdiff : 0 ≤ Cdiff := by dsimp only [Cdiff]; positivity
  have hC1 : 396 * A ≤ C := by
    dsimp only [C, localizedAssemblyConstant]
    linarith [hCdiff, abs_nonneg Caux]
  have hC2 : Cdiff + |Caux| ≤ C := by
    dsimp only [C, localizedAssemblyConstant, Cdiff]
    linarith
  have hproj : ‖a (R z)‖ ≤ ‖a z‖ := residualWeight_high_projection_norm_le V hcV hpV φ hMV hf hα0 τ z
  have hlow₁ : ‖L₁ z‖ ≤ 12 * A * r * ‖Ψ z‖ :=
    localized_low_low_interaction_bound U V hcU hcV hpU hpV φ hMU hMV hf h hτ
      (le_min hτ1 hτA) hδ z
  have hlow₂ : ‖L₂ z‖ ≤ 384 * A * (δ / τ) * ‖Ψ z‖ :=
    localized_high_low_interaction_bound U V hcU hcV hpU hpV φ hMU hMV hf h hτ
      (le_min hτ1 hτA) hδ z
  have hlow₂' : ‖L₂ z‖ ≤ 384 * A * r * ‖Ψ z‖ := hlow₂.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by dsimp only [r]; linarith : δ / τ ≤ r) (by positivity)) (norm_nonneg _))
  have hlow : ‖L₁ z‖ + ‖L₂ z‖ ≤ 396 * A * r * ‖Ψ z‖ := by
    calc
      _ ≤ 12 * A * r * ‖Ψ z‖ + 384 * A * r * ‖Ψ z‖ := add_le_add hlow₁ hlow₂'
      _ = _ := by ring
  have hdiff : ‖L₃ z‖ ≤ Cdiff * t * ‖a (R z)‖ :=
    auxiliary_prediction_difference_endpoint_bound b U V hcU hcV hpU hpV φ hMU hMV hf h
      hα0 hα2 hτ hτ1 hδ c hcK z
  have hdiff' : ‖L₃ z‖ ≤ Cdiff * t * ‖a z‖ := hdiff.trans
    (mul_le_mul_of_nonneg_left hproj (mul_nonneg hCdiff ht))
  have haux0 : ‖L₄ z‖ ≤ |Caux| * t * ‖a (R z)‖ := (haux z).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Caux) ht) (norm_nonneg _))
  have haux' : ‖L₄ z‖ ≤ |Caux| * t * ‖a z‖ := haux0.trans
    (mul_le_mul_of_nonneg_left hproj (mul_nonneg (abs_nonneg _) ht))
  have hhigh : ‖L₃ z‖ + ‖L₄ z‖ ≤ (Cdiff + |Caux|) * t * ‖a z‖ := by
    calc
      _ ≤ Cdiff * t * ‖a z‖ + |Caux| * t * ‖a z‖ := add_le_add hdiff' haux'
      _ = _ := by ring
  have hQS : Q * S = S * Q := compactSqrt_spectralProjection_commute V hcV hpV (Set.Icc 0 τ)
  have hsplit : Q * S + S * R = S := by
    dsimp only [R]
    rw [hQS]
    noncomm_ring
  have heq : S * J * S = L₁ + L₂ + (L₃ + L₄) := by
    calc
      _ = S * J * (Q * S + S * R) := by rw [hsplit]
      _ = _ := by
        dsimp only [L₁, L₂, L₃, L₄, D, actualAuxiliaryInteractionDifference, J, Jt, R]
        noncomm_ring
  have hvec : (S * J * S) z = L₁ z + L₂ z + (L₃ z + L₄ z) := congrArg (fun F : H →L[ℝ] H => F z) heq
  change ‖(S * J * S) z‖ ≤ C * r * ‖Ψ z‖ + C * t * ‖a z‖
  rw [hvec]
  calc
    _ ≤ ‖L₁ z + L₂ z‖ + ‖L₃ z + L₄ z‖ := norm_add_le _ _
    _ ≤ (‖L₁ z‖ + ‖L₂ z‖) + (‖L₃ z‖ + ‖L₄ z‖) :=
      add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ 396 * A * r * ‖Ψ z‖ + (Cdiff + |Caux|) * t * ‖a z‖ := add_le_add hlow hhigh
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hr) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 ht) (norm_nonneg _))

end
end KernelSeq
