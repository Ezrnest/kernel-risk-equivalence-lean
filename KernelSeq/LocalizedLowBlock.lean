import KernelSeq.SpectralBlocks
import KernelSeq.SpectralInteraction
import KernelSeq.VarianceTraceComparison
import KernelSeq.SpectralEnergy

/-!
# The actual localized low--low interaction block

All projections below are actual indicator multipliers on constructed compact
spectral bases. The two covariance operators are not assumed to commute. The
outside square-root bounds follow from the actual relative Loewner comparison,
and low-frequency residual control follows from the original scalar contract.
No operator-Lipschitz or HMS estimate is used in this block.
-/

open Submodule
open scoped BigOperators

namespace KernelSeq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual dimensionless low-frequency indicator projection. -/
noncomputable def lowBlockProjection (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hp : T.IsPositive) (τ : ℝ) : H →L[ℝ] H :=
  compactSpectralProjection T hc hp (Set.Icc 0 τ)

/-- The actual normalized deviation in dimensionless coordinates. -/
noncomputable def lowBlockDeviation (U V : H →L[ℝ] H) (hcV : IsCompactOperator V)
    (hpV : V.IsPositive) : ℝ := ‖realNormalizedPerturbation V U hcV hpV 1‖

/-- Square roots commute with their own spectral projection, without any
commutation assertion about the two different covariance operators. -/
theorem compactSqrt_spectralProjection_commute (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    compactSpectralProjection T hc hp s * compactRegularizedSqrt T hc hp 0 =
      compactRegularizedSqrt T hc hp 0 * compactSpectralProjection T hc hp s := by
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [mul_apply_eq_comp, compactSpectralProjection_repr, compactRegularizedSqrt_repr]
  ring

/-- The low spectral restriction gives its actual square-root energy bound. -/
theorem compactSqrt_lowProjection_apply_sq_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) (hτ : 0 ≤ τ) (x : H) :
    ‖compactRegularizedSqrt T hc hp 0 (lowBlockProjection T hc hp τ x)‖ ^ 2 ≤
      τ * ‖lowBlockProjection T hc hp τ x‖ ^ 2 := by
  let y : LowSpectralSpace T hc hp τ := ⟨lowBlockProjection T hc hp τ x, ⟨x, rfl⟩⟩
  have hy := (lowSpectralRestriction T hc hp τ).le_of_opNorm_le
    (lowSpectralRestriction_norm_le T hc hp τ hτ) y
  change ‖T (lowBlockProjection T hc hp τ x)‖ ≤ τ * ‖lowBlockProjection T hc hp τ x‖ at hy
  rw [compactSqrt_norm_sq]
  have hinner := real_inner_le_norm (lowBlockProjection T hc hp τ x)
    (T (lowBlockProjection T hc hp τ x))
  have hmul := mul_le_mul_of_nonneg_left hy (norm_nonneg (lowBlockProjection T hc hp τ x))
  nlinarith

/-- The exact actual low-frequency square-root projection norm. -/
theorem compactSqrt_lowProjection_norm_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖compactRegularizedSqrt T hc hp 0 * lowBlockProjection T hc hp τ‖ ≤ Real.sqrt τ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hP : ‖lowBlockProjection T hc hp τ x‖ ≤ ‖x‖ := by
    simpa only [one_mul] using (lowBlockProjection T hc hp τ).le_of_opNorm_le
      (compactSpectralProjection_norm_le_one T hc hp (Set.Icc 0 τ)) x
  have hsq := (compactSqrt_lowProjection_apply_sq_le T hc hp τ hτ x).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hP 2) hτ)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  simpa only [mul_apply_eq_comp, mul_pow, Real.sq_sqrt hτ] using hsq

/-- The noncommuting outside left factor is controlled by the actual relative
quadratic comparison. The denominator is proved positive on the good event. -/
theorem compactSqrt_cross_lowProjection_norm_le (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) (hτ : 0 ≤ τ)
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4) :
    ‖compactRegularizedSqrt V hcV hpV 0 * lowBlockProjection U hcU hpU (2 * τ)‖ ≤
      Real.sqrt ((2 * τ + lowBlockDeviation U V hcV hpV) /
        (1 - lowBlockDeviation U V hcV hpV)) := by
  let δ := lowBlockDeviation U V hcV hpV
  let P := lowBlockProjection U hcU hpU (2 * τ)
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hden : 0 < 1 - δ := by linarith
  have hcoef : 0 ≤ (2 * τ + δ) / (1 - δ) := div_nonneg (by positivity) hden.le
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  let y := P x
  have hq := (compact_regularized_relative_comparison_real V U hcV hpV 1 (by norm_num) y).1
  have hδeq : ‖Ring.inverse (compactRegularizedSqrt V hcV hpV 1) *
      (U + (1 : ℝ) • (1 : H →L[ℝ] H) - (V + (1 : ℝ) • 1)) *
        Ring.inverse (compactRegularizedSqrt V hcV hpV 1)‖ = δ := by
    congr 1
    congr 2
    abel
  rw [hδeq] at hq
  have hV : inner ℝ y ((V + (1 : ℝ) • (1 : H →L[ℝ] H)) y) =
      ‖compactRegularizedSqrt V hcV hpV 0 y‖ ^ 2 + ‖y‖ ^ 2 := by
    simp only [one_smul, _root_.add_apply, one_apply_eq_self]
    rw [inner_add_right, ← compactSqrt_norm_sq V hcV hpV y, real_inner_self_eq_norm_sq]
  have hU : inner ℝ y ((U + (1 : ℝ) • (1 : H →L[ℝ] H)) y) =
      ‖compactRegularizedSqrt U hcU hpU 0 y‖ ^ 2 + ‖y‖ ^ 2 := by
    simp only [one_smul, _root_.add_apply, one_apply_eq_self]
    rw [inner_add_right, ← compactSqrt_norm_sq U hcU hpU y, real_inner_self_eq_norm_sq]
  rw [hV, hU] at hq
  have hUlow := compactSqrt_lowProjection_apply_sq_le U hcU hpU (2 * τ) (by positivity) x
  change ‖compactRegularizedSqrt U hcU hpU 0 y‖ ^ 2 ≤ 2 * τ * ‖y‖ ^ 2 at hUlow
  have hsq : ‖compactRegularizedSqrt V hcV hpV 0 y‖ ^ 2 ≤
      ((2 * τ + δ) / (1 - δ)) * ‖y‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith
  have hP : ‖y‖ ≤ ‖x‖ := by
    simpa only [one_mul] using P.le_of_opNorm_le
      (compactSpectralProjection_norm_le_one U hcU hpU (Set.Icc 0 (2 * τ))) x
  have hfinal := hsq.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hP 2) hcoef)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  simp only [mul_apply_eq_comp, mul_pow]
  change ‖compactRegularizedSqrt V hcV hpV 0 y‖ ^ 2 ≤
    (Real.sqrt ((2 * τ + δ) / (1 - δ))) ^ 2 * ‖x‖ ^ 2
  rw [Real.sq_sqrt hcoef]
  exact hfinal

/-- The original size assumption forces a small shrinkage on this low interval.
The zero spectral value is included, and no inverse residual is introduced. -/
theorem lowBlock_residual_ge_half {M ρ A τ t : ℝ} {φ : ℝ → ℝ}
    (h : ResidualFilter.Contract 1 M ρ A φ) (hM : 0 ≤ M)
    (hτ : 0 ≤ τ) (hsmall : τ ≤ 1 / (4 * (A + 1)))
    (ht : t ∈ Set.Icc (0 : ℝ) M) (htτ : t ≤ τ) :
    1 / 2 ≤ ResidualFilter.residual φ t := by
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) hM
  have hden : 0 < 4 * (A + 1) := by positivity
  have hτA := (le_div_iff₀ hden).mp hsmall
  have hAτ : A * τ ≤ 1 / 4 := by nlinarith
  have hφ : φ t ≤ A := by
    simpa only [div_one] using ((le_abs_self (φ t)).trans
      (h.profile_bound (by norm_num) ht))
  have hq : t * φ t ≤ A * τ := (mul_le_mul_of_nonneg_left hφ ht.1).trans
    (by nlinarith)
  dsimp only [ResidualFilter.residual, ResidualFilter.shrinkage]
  linarith

/-- Actual low-frequency vectors are controlled by the actual population
residual. Parseval works over the full arbitrary spectral index, including the
kernel, so there is no countability or separability assumption on `H`. -/
theorem lowBlockProjection_norm_le_residual (V : H →L[ℝ] H)
    (hcV : IsCompactOperator V) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A τ : ℝ} (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hτ : 0 ≤ τ) (hsmall : τ ≤ 1 / (4 * (A + 1))) (z : H) :
    ‖lowBlockProjection V hcV hpV τ z‖ ≤
      2 * ‖compactResidualOperator V hcV hpV φ hMV hf z‖ := by
  classical
  let b := compactEigenbasis V hcV hpV.isSymmetric
  let Q := lowBlockProjection V hcV hpV τ
  let Ψ := compactResidualOperator V hcV hpV φ hMV hf
  have hpoint : ∀ i, (b.repr (Q z) i) ^ 2 ≤ 4 * (b.repr (Ψ z) i) ^ 2 := by
    intro i
    have hQ : b.repr (Q z) i =
        (if i.1 ∈ Set.Icc (0 : ℝ) τ then 1 else 0) * b.repr z i :=
      by simp [b, Q, lowBlockProjection,
        compactSpectralProjection_repr]
    have hΨ : b.repr (Ψ z) i = ResidualFilter.residual φ i.1 * b.repr z i := by
      exact compactSpectralMultiplier_repr _ _ _ _ _ _ _ _ _
    rw [hQ, hΨ]
    split_ifs with hi
    · have hr := lowBlock_residual_ge_half h ((norm_nonneg V).trans hMV) hτ hsmall
        ⟨compactEigenvalue_nonneg V hcV hpV i,
          ((le_abs_self i.1).trans (compactEigenvalue_norm_le V hcV hpV.isSymmetric i)).trans hMV⟩ hi.2
      have hs : 1 ≤ 4 * (ResidualFilter.residual φ i.1) ^ 2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg (b.repr z i))
      nlinarith
    · nlinarith [sq_nonneg (ResidualFilter.residual φ i.1 * b.repr z i)]
  have hsum := (hilbertBasis_coefficients_sq_summable b (Q z)).tsum_le_tsum hpoint
    ((hilbertBasis_coefficients_sq_summable b (Ψ z)).mul_left 4)
  rw [tsum_mul_left, ← hilbertBasis_norm_sq_eq_tsum b (Q z),
    ← hilbertBasis_norm_sq_eq_tsum b (Ψ z)] at hsum
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mp
  nlinarith

/-- The full interaction is bounded by the original profile-size constant;
this coarse estimate is used only after both low-frequency localizations. -/
theorem compactInteraction_norm_le_two_mul (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ) :
    ‖compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h‖ ≤ 2 * A := by
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) ((norm_nonneg V).trans hMV)
  have hFU : ‖compactFilterOperator U hcU hpU φ (by norm_num) hMU h‖ ≤ A := by
    simpa only [compactFilterOperator, div_one] using
      (compactSpectralMultiplier_norm_le U hcU hpU φ (A / 1)
        (by simpa using hA) (fun _ ht => h.profile_bound (by norm_num) ⟨ht.1, ht.2.trans hMU⟩))
  have hFV : ‖compactFilterOperator V hcV hpV φ (by norm_num) hMV h‖ ≤ A := by
    simpa only [compactFilterOperator, div_one] using
      (compactSpectralMultiplier_norm_le V hcV hpV φ (A / 1)
        (by simpa using hA) (fun _ ht => h.profile_bound (by norm_num) ⟨ht.1, ht.2.trans hMV⟩))
  have hΨU : ‖compactResidualOperator U hcU hpU φ hMU hf‖ ≤ 1 := by
    apply compactSpectralMultiplier_norm_le
  have hΨV : ‖compactResidualOperator V hcV hpV φ hMV hf‖ ≤ 1 := by
    apply compactSpectralMultiplier_norm_le
  calc
    _ ≤ ‖compactFilterOperator U hcU hpU φ (by norm_num) hMU h *
        compactResidualOperator V hcV hpV φ hMV hf‖ +
        ‖compactResidualOperator U hcU hpU φ hMU hf *
          compactFilterOperator V hcV hpV φ (by norm_num) hMV h‖ := norm_sub_le _ _
    _ ≤ A * 1 + 1 * A := add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul hFU hΨV (norm_nonneg _) hA))
      ((norm_mul_le _ _).trans (mul_le_mul hΨU hFV (norm_nonneg _) zero_le_one))
    _ = 2 * A := by ring

/-- The right outside factor acts only on low-frequency population vectors. -/
theorem lowBlockProjection_sqrt_apply_norm_le (V : H →L[ℝ] H)
    (hcV : IsCompactOperator V) (hpV : V.IsPositive) (τ : ℝ) (hτ : 0 ≤ τ) (z : H) :
    ‖lowBlockProjection V hcV hpV τ (compactRegularizedSqrt V hcV hpV 0 z)‖ ≤
      Real.sqrt τ * ‖lowBlockProjection V hcV hpV τ z‖ := by
  let Q := lowBlockProjection V hcV hpV τ
  have hQQ : Q * Q = Q := compactSpectralProjection_isIdempotent V hcV hpV (Set.Icc 0 τ)
  have hcomm : Q * compactRegularizedSqrt V hcV hpV 0 =
      compactRegularizedSqrt V hcV hpV 0 * Q :=
    compactSqrt_spectralProjection_commute V hcV hpV (Set.Icc 0 τ)
  have heq : Q (compactRegularizedSqrt V hcV hpV 0 z) =
      (compactRegularizedSqrt V hcV hpV 0 * Q) (Q z) := by
    change (Q * compactRegularizedSqrt V hcV hpV 0) z = _
    rw [hcomm, ← mul_apply_eq_comp, mul_assoc, hQQ]
  rw [show lowBlockProjection V hcV hpV τ = Q from rfl, heq]
  exact (compactRegularizedSqrt V hcV hpV 0 * Q).le_of_opNorm_le
    (compactSqrt_lowProjection_norm_le V hcV hpV τ hτ) (Q z)

/-- Scalar absorption of the two actual outside factors. The positive cutoff
is used explicitly for the only division by `τ`. -/
theorem localized_lowBlock_sqrt_coefficient_le {τ δ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) :
    Real.sqrt ((2 * τ + δ) / (1 - δ)) * Real.sqrt τ ≤ 3 * (τ + δ / τ) := by
  have hden : 0 < 1 - δ := by linarith
  have hnum : 0 ≤ 2 * τ + δ := by positivity
  have hk0 : 0 ≤ (2 * τ + δ) / (1 - δ) := div_nonneg hnum hden.le
  have hk : (2 * τ + δ) / (1 - δ) ≤ 2 * (2 * τ + δ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hnum (show 0 ≤ 1 - 2 * δ by linarith)]
  have hδτ : δ * τ ≤ δ := by nlinarith
  have hkt : ((2 * τ + δ) / (1 - δ)) * τ ≤ 4 * τ ^ 2 + 2 * δ := by
    have hh := mul_le_mul_of_nonneg_right hk hτ.le
    nlinarith
  have hw : 0 ≤ δ / τ := div_nonneg hδ0 hτ.le
  have hcancel : τ * (δ / τ) = δ := by field_simp
  have hs : 4 * τ ^ 2 + 2 * δ ≤ (3 * (τ + δ / τ)) ^ 2 := by
    nlinarith [sq_nonneg τ, sq_nonneg (δ / τ), mul_nonneg hτ.le hw]
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (by positivity : 0 ≤ 3 * (τ + δ / τ))).mp
  rw [mul_pow, Real.sq_sqrt hk0, Real.sq_sqrt hτ.le]
  exact hkt.trans hs

/-- The manuscript's actual dimensionless low--low interaction estimate.
Both covariance operators act on the full Hilbert space and may fail to
commute. All outside factors and residual controls are derived above from
the actual deviation, compact spectral calculus, and original filter contract. -/
theorem localized_low_low_interaction_bound (U V : H →L[ℝ] H)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hτ : 0 < τ) (hsmall : τ ≤ min 1 (1 / (4 * (A + 1))))
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4) (z : H) :
    ‖(compactRegularizedSqrt V hcV hpV 0 * lowBlockProjection U hcU hpU (2 * τ) *
        compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h *
        lowBlockProjection V hcV hpV τ * compactRegularizedSqrt V hcV hpV 0) z‖ ≤
      12 * A * (τ + lowBlockDeviation U V hcV hpV / τ) *
        ‖compactResidualOperator V hcV hpV φ hMV hf z‖ := by
  let R := compactRegularizedSqrt V hcV hpV 0
  let P := lowBlockProjection U hcU hpU (2 * τ)
  let Q := lowBlockProjection V hcV hpV τ
  let J := compactInteraction U V hcU hcV hpU hpV φ (by norm_num) hMU hMV hf h
  let Ψ := compactResidualOperator V hcV hpV φ hMV hf
  let δ := lowBlockDeviation U V hcV hpV
  let k := (2 * τ + δ) / (1 - δ)
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) ((norm_nonneg V).trans hMV)
  have hleft : ‖R * P‖ ≤ Real.sqrt k :=
    compactSqrt_cross_lowProjection_norm_le U V hcU hcV hpU hpV τ hτ.le hδ
  have hright : ‖Q (R z)‖ ≤ Real.sqrt τ * ‖Q z‖ :=
    lowBlockProjection_sqrt_apply_norm_le V hcV hpV τ hτ.le z
  have hJ : ‖J‖ ≤ 2 * A :=
    compactInteraction_norm_le_two_mul U V hcU hcV hpU hpV φ hMU hMV hf h
  have hQ : ‖Q z‖ ≤ 2 * ‖Ψ z‖ := lowBlockProjection_norm_le_residual V hcV hpV φ hMV
    hf h hτ.le (le_trans hsmall (min_le_right _ _)) z
  have hcoef : Real.sqrt k * Real.sqrt τ ≤ 3 * (τ + δ / τ) :=
    localized_lowBlock_sqrt_coefficient_le hτ (le_trans hsmall (min_le_left _ _))
      (norm_nonneg _) hδ
  calc
    _ = ‖(R * P) (J (Q (R z)))‖ := by rfl
    _ ≤ Real.sqrt k * ‖J (Q (R z))‖ := (R * P).le_of_opNorm_le hleft _
    _ ≤ Real.sqrt k * (2 * A * ‖Q (R z)‖) :=
      mul_le_mul_of_nonneg_left (J.le_of_opNorm_le hJ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt k * (2 * A * (Real.sqrt τ * (2 * ‖Ψ z‖))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * A)
      exact hright.trans (mul_le_mul_of_nonneg_left hQ (Real.sqrt_nonneg _))
    _ = 4 * A * (Real.sqrt k * Real.sqrt τ) * ‖Ψ z‖ := by ring
    _ ≤ 4 * A * (3 * (τ + δ / τ)) * ‖Ψ z‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef (by positivity)) (norm_nonneg _)
    _ = _ := by ring

end KernelSeq
