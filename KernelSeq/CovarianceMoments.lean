import KernelSeq.PopulationCovariance
import KernelSeq.EmpiricalCovariance
import Mathlib.Tactic.NoncommRing

/-!
# Actual centered rank-one covariance moments

The population covariance is the actual `S* S` of a square-integrable feature.
An a.e. feature bound supplies operator-square Bochner integrability, zero
centered mean, selfadjointness, the bounded-increment estimate, and the actual
Loewner second-moment bound. No variance-majorant or trace certificate is input.
The argument uses scalar quadratic forms and Bochner integration, without real
CFC, separability, or finite-dimensional assumptions.
-/

open MeasureTheory Filter InnerProductSpace

namespace KernelSeq

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X}

/-- Scalar pairings commute with the actual operator-valued integral. -/
theorem inner_integral_operator_apply (A : X → H →L[ℝ] H) (hA : Integrable A μ)
    (v w : H) :
    inner ℝ v ((∫ x, A x ∂μ) w) = ∫ x, inner ℝ v (A x w) ∂μ := by
  rw [ContinuousLinearMap.integral_apply hA]
  exact (integral_inner (hA.apply_continuousLinearMap w) v).symm

/-- Symmetry is preserved by an integrable operator-valued expectation. -/
theorem integral_operator_isSymmetric (A : X → H →L[ℝ] H) (hA : Integrable A μ)
    (hsym : ∀ᵐ x ∂μ, (A x).IsSymmetric) :
    (∫ x, A x ∂μ : H →L[ℝ] H).IsSymmetric := by
  intro v w
  change inner ℝ ((∫ x, A x ∂μ) v) w = inner ℝ v ((∫ x, A x ∂μ) w)
  rw [real_inner_comm w ((∫ x, A x ∂μ) v),
    inner_integral_operator_apply A hA w v, inner_integral_operator_apply A hA v w]
  apply integral_congr_ae
  filter_upwards [hsym] with x hx
  rw [real_inner_comm]
  exact hx v w

/-- Positivity is preserved by the actual Bochner operator integral. -/
theorem integral_operator_isPositive (A : X → H →L[ℝ] H) (hA : Integrable A μ)
    (hpos : ∀ᵐ x ∂μ, (A x).IsPositive) :
    (∫ x, A x ∂μ : H →L[ℝ] H).IsPositive := by
  refine ⟨integral_operator_isSymmetric A hA (hpos.mono (fun _ hx => hx.isSymmetric)), ?_⟩
  intro v
  change 0 ≤ inner ℝ ((∫ x, A x ∂μ) v) v
  rw [real_inner_comm, inner_integral_operator_apply A hA]
  exact integral_nonneg_of_ae (hpos.mono (fun _ hx => hx.inner_nonneg_right v))

/-- Genuine Loewner monotonicity for integrable bounded-operator fields. -/
theorem integral_operator_mono (A B : X → H →L[ℝ] H)
    (hA : Integrable A μ) (hB : Integrable B μ) (hle : ∀ᵐ x ∂μ, A x ≤ B x) :
    (∫ x, A x ∂μ : H →L[ℝ] H) ≤ ∫ x, B x ∂μ := by
  apply (ContinuousLinearMap.le_def _ _).mpr
  rw [← integral_sub hB hA]
  exact integral_operator_isPositive (fun x => B x - A x) (hB.sub hA)
    (hle.mono (fun _ hx => (ContinuousLinearMap.le_def _ _).mp hx))

omit [CompleteSpace H] in
/-- Bounded operator fields with integrable norm have integrable squares. -/
theorem integrable_operator_square_of_bound (A : X → H →L[ℝ] H)
    (hA : Integrable A μ) {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ L) :
    Integrable (fun x => A x * A x) μ := by
  apply (hA.norm.const_mul L).mono' (hA.1.mul hA.1)
  filter_upwards [hbound] with x hx
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- Positivity of a selfadjoint operator square by the actual adjoint product;
no functional calculus or star-order instance is required. -/
theorem operator_square_isPositive_of_isSelfAdjoint (A : H →L[ℝ] H)
    (hA : IsSelfAdjoint A) : (A * A).IsPositive := by
  have hp := ContinuousLinearMap.isPositive_adjoint_comp_self A
  change (A.adjoint * A).IsPositive at hp
  rwa [hA.adjoint_eq] at hp

variable [IsProbabilityMeasure μ]

/-- Noncommutative centering of an actual integrable operator square. Both
centered-square integrability and the exact centered moment are conclusions. -/
theorem integral_centered_operator_square (A : X → H →L[ℝ] H)
    (hA : Integrable A μ) (hA2 : Integrable (fun x => A x * A x) μ)
    (C : H →L[ℝ] H) (hmean : (∫ x, A x ∂μ) = C) :
    Integrable (fun x => (A x - C) * (A x - C)) μ ∧
    (∫ x, (A x - C) * (A x - C) ∂μ) = (∫ x, A x * A x ∂μ) - C * C := by
  have hexp (x : X) : (A x - C) * (A x - C) =
      (A x * A x - A x * C) - C * A x + C * C := by noncomm_ring
  have hAC := hA.mul_const C
  have hCA := hA.const_mul C
  have hCC : Integrable (fun _ : X => C * C) μ := integrable_const _
  have hexpInt := ((hA2.sub hAC).sub hCA).add hCC
  constructor
  · exact hexpInt.congr (Eventually.of_forall (fun x => (hexp x).symm))
  · simp_rw [hexp]
    have hadd := integral_add ((hA2.sub hAC).sub hCA) hCC
    have hsub₂ := integral_sub (hA2.sub hAC) hCA
    have hsub₁ := integral_sub hA2 hAC
    simp only [Pi.sub_def] at hadd hsub₂ hsub₁
    rw [hadd, hsub₂, hsub₁,
      integral_mul_const_of_integrable hA, integral_const_mul_of_integrable hA,
      hmean, integral_const]
    simp only [probReal_univ, one_smul]
    noncomm_ring

/-- The feature bound supplies the actual covariance operator-norm bound. -/
theorem populationCovariance_norm_le_feature_bound (u : X → H) (hu : MemLp u 2 μ)
    {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) :
    ‖populationCovariance (featureEmbedding μ u hu)‖ ≤ L := by
  rw [populationCovariance_eq_integral]
  calc
    _ ≤ ∫ x, ‖rankOne ℝ (u x) (u x)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖u x‖ ^ 2 ∂μ := by simp only [norm_rankOne, ← pow_two]
    _ ≤ ∫ _ : X, L ∂μ := integral_mono_ae
      ((memLp_two_iff_integrable_sq_norm hu.1).mp hu) (integrable_const _) hbound
    _ = L := by simp

/-- Centered rank-one fluctuation around the actual population covariance. -/
noncomputable def centeredRankOne (u : X → H) (hu : MemLp u 2 μ) (x : X) : H →L[ℝ] H :=
  rankOne ℝ (u x) (u x) - populationCovariance (featureEmbedding μ u hu)

theorem integrable_centeredRankOne (u : X → H) (hu : MemLp u 2 μ) :
    Integrable (centeredRankOne u hu) μ :=
  (integrable_rankOne_feature u hu).sub (integrable_const _)

theorem integral_centeredRankOne (u : X → H) (hu : MemLp u 2 μ) :
    (∫ x, centeredRankOne u hu x ∂μ) = 0 := by
  unfold centeredRankOne
  rw [integral_sub (integrable_rankOne_feature u hu) (integrable_const _),
    ← populationCovariance_eq_integral u hu]
  simp

omit [IsProbabilityMeasure μ] in
theorem centeredRankOne_isSelfAdjoint (u : X → H) (hu : MemLp u 2 μ) (x : X) :
    IsSelfAdjoint (centeredRankOne u hu x) :=
  (isPositive_rankOne_self (u x)).isSelfAdjoint.sub
    (populationCovariance_isPositive (featureEmbedding μ u hu)).isSelfAdjoint

omit [IsProbabilityMeasure μ] in
theorem centeredRankOne_norm_le (u : X → H) (hu : MemLp u 2 μ)
    {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) :
    ∀ᵐ x ∂μ, ‖centeredRankOne u hu x‖ ≤
      L + ‖populationCovariance (featureEmbedding μ u hu)‖ := by
  filter_upwards [hbound] with x hx
  have hb : ‖rankOne ℝ (u x) (u x)‖ ≤ L := by
    simpa only [norm_rankOne, ← pow_two] using hx
  exact (norm_sub_le _ _).trans (add_le_add hb le_rfl)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A probability-space feature bound necessarily has a nonnegative bound. -/
theorem feature_sq_bound_nonneg (u : X → H) {L : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) : 0 ≤ L := by
  obtain ⟨x, hx⟩ := hbound.exists
  exact (sq_nonneg _).trans hx

/-- The standard twice-leverage bound is derived from the actual covariance. -/
theorem centeredRankOne_norm_le_two (u : X → H) (hu : MemLp u 2 μ)
    {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) :
    ∀ᵐ x ∂μ, ‖centeredRankOne u hu x‖ ≤ 2 * L := by
  filter_upwards [centeredRankOne_norm_le u hu hbound] with x hx
  have hC := populationCovariance_norm_le_feature_bound u hu hbound
  linarith

omit [CompleteSpace H] [IsProbabilityMeasure μ] in
/-- The uncentered rank-one operator square is genuinely Bochner integrable. -/
theorem integrable_rankOne_square_of_feature_bound (u : X → H) (hu : MemLp u 2 μ)
    {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) :
    Integrable (fun x => rankOne ℝ (u x) (u x) * rankOne ℝ (u x) (u x)) μ := by
  apply integrable_operator_square_of_bound _ (integrable_rankOne_feature u hu)
  filter_upwards [hbound] with x hx
  simpa only [norm_rankOne, ← pow_two] using hx

/-- Centered-square integrability follows from the feature bound and L² feature,
not from a presumed moment or concentration theorem. -/
theorem integrable_centeredRankOne_square (u : X → H) (hu : MemLp u 2 μ)
    {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) :
    Integrable (fun x => centeredRankOne u hu x * centeredRankOne u hu x) μ := by
  exact (integral_centered_operator_square _ (integrable_rankOne_feature u hu)
    (integrable_rankOne_square_of_feature_bound u hu hbound)
    (populationCovariance (featureEmbedding μ u hu))
    (populationCovariance_eq_integral u hu).symm).1

/-- The exact noncommutative centered moment of the actual rank-one field. -/
theorem integral_centeredRankOne_square (u : X → H) (hu : MemLp u 2 μ)
    {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) :
    (∫ x, centeredRankOne u hu x * centeredRankOne u hu x ∂μ) =
      (∫ x, rankOne ℝ (u x) (u x) * rankOne ℝ (u x) (u x) ∂μ) -
        populationCovariance (featureEmbedding μ u hu) * populationCovariance (featureEmbedding μ u hu) :=
  (integral_centered_operator_square _ (integrable_rankOne_feature u hu)
    (integrable_rankOne_square_of_feature_bound u hu hbound)
    (populationCovariance (featureEmbedding μ u hu))
    (populationCovariance_eq_integral u hu).symm).2

omit [IsProbabilityMeasure μ] in
/-- The rank-one square majorant is integrated in the actual Loewner order. -/
theorem integral_rankOne_square_le (u : X → H) (hu : MemLp u 2 μ)
    {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) :
    (∫ x, rankOne ℝ (u x) (u x) * rankOne ℝ (u x) (u x) ∂μ) ≤
      L • populationCovariance (featureEmbedding μ u hu) := by
  have hm := integral_operator_mono
    (fun x => rankOne ℝ (u x) (u x) * rankOne ℝ (u x) (u x))
    (fun x => L • rankOne ℝ (u x) (u x))
    (integrable_rankOne_square_of_feature_bound u hu hbound)
    ((integrable_rankOne_feature u hu).smul L)
    (hbound.mono (fun x hx => rankOne_square_le hx))
  rwa [integral_smul, ← populationCovariance_eq_integral u hu] at hm

/-- The actual centered second moment is positive, with no PSD certificate
assumed for that expectation. -/
theorem integral_centeredRankOne_square_isPositive (u : X → H) (hu : MemLp u 2 μ)
    {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) :
    (∫ x, centeredRankOne u hu x * centeredRankOne u hu x ∂μ : H →L[ℝ] H).IsPositive := by
  apply integral_operator_isPositive _ (integrable_centeredRankOne_square u hu hbound)
  exact Eventually.of_forall (fun x => operator_square_isPositive_of_isSelfAdjoint _
    (centeredRankOne_isSelfAdjoint u hu x))

/-- The genuine operator variance majorant required in the covariance
concentration application: `E[(u⊗u−C)²] ≤ L C`. -/
theorem integral_centeredRankOne_square_le (u : X → H) (hu : MemLp u 2 μ)
    {L : ℝ} (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) :
    (∫ x, centeredRankOne u hu x * centeredRankOne u hu x ∂μ : H →L[ℝ] H) ≤
      L • populationCovariance (featureEmbedding μ u hu) := by
  rw [integral_centeredRankOne_square u hu hbound]
  apply LE.le.trans ?_ (integral_rankOne_square_le u hu hbound)
  apply (ContinuousLinearMap.le_def _ _).mpr
  have hc := operator_square_isPositive_of_isSelfAdjoint _
    (populationCovariance_isPositive (featureEmbedding μ u hu)).isSelfAdjoint
  convert hc using 1
  noncomm_ring

end KernelSeq
