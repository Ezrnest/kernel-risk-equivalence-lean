import KernelSeq.SchattenIntegral
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Genuine probability averaging of actual Schatten moments

The objects being integrated are the original complete HS column space.
The previously proved actual Schatten integral estimate and scalar Jensen
give the moment estimate; Fubini then changes the two genuine integrals.
No complete Schatten Banach space or vector-valued Minkowski certificate
is assumed. Joint strong measurability and an actual uniform HS bound
derive every Bochner integrability condition in the angular theorem.
-/

open MeasureTheory Set
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section OneMeasure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A genuine uniform HS bound supplies integrability of every actual
Schatten moment with exponent at least two, on a finite measure. -/
theorem integrable_hsSchattenNorm_rpow_of_bound [IsFiniteMeasure μ]
    (b : HilbertBasis ι ℝ H) {q M : ℝ} (hq : 2 ≤ q) (_hM : 0 ≤ M)
    (F : Ω → HilbertSchmidtColumns ι E) (hF : StronglyMeasurable F)
    (hbound : ∀ ω, ‖F ω‖ ≤ M) :
    Integrable (fun ω => hsSchattenNorm b (F ω) q ^ q) μ := by
  have hq0 : 0 ≤ q := by linarith
  apply Integrable.of_bound
    (((Real.continuous_rpow_const hq0).comp_stronglyMeasurable
      ((hsSchattenNorm_continuous b hq).comp_stronglyMeasurable hF)).aestronglyMeasurable)
    (M ^ q)
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hsSchattenNorm_nonneg b _ q) q)]
    exact Real.rpow_le_rpow (hsSchattenNorm_nonneg b _ q)
      ((hsSchattenNorm_le_hsNorm b _ hq).trans (hbound ω)) hq0

/-- Jensen's true probability-moment estimate for the actual HS-valued
Bochner integral. Only genuine analytic integrability is an input. -/
theorem hsSchattenNorm_integral_rpow_le [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H) {q : ℝ} (hq : 2 ≤ q)
    (F : Ω → HilbertSchmidtColumns ι E) (hF : Integrable F μ)
    (hpow : Integrable (fun ω => hsSchattenNorm b (F ω) q ^ q) μ) :
    hsSchattenNorm b (∫ ω, F ω ∂μ) q ^ q ≤ ∫ ω, hsSchattenNorm b (F ω) q ^ q ∂μ := by
  have hs := integrable_hsSchattenNorm b hq hF
  have hJ := (convexOn_rpow (by linarith : 1 ≤ q)).map_integral_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ q)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun ω => hsSchattenNorm_nonneg b (F ω) q) hs hpow
  exact (Real.rpow_le_rpow (hsSchattenNorm_nonneg b _ q)
    (hsSchattenNorm_integral_le b hq F hF) (by linarith)).trans hJ

end OneMeasure

section Angular
variable {Φ Θ : Type*} [MeasurableSpace Φ] [MeasurableSpace Θ]
  {ν : Measure Φ} {μ : Measure Θ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

/-- Jointly strongly measurable, uniformly HS-bounded angular families
admit genuine weighted probability averaging without increasing their
integrated Schatten q-moment, for every real q ≥ 2 and |w| ≤ 1. -/
theorem hsSchattenNorm_angular_average_rpow_le (b : HilbertBasis ι ℝ H)
    {q M : ℝ} (hq : 2 ≤ q) (hM : 0 ≤ M)
    (G : Φ × Θ → HilbertSchmidtColumns ι E) (hG : StronglyMeasurable G)
    (hbound : ∀ φ θ, ‖G (φ, θ)‖ ≤ M)
    (w : Φ → ℝ) (hw : StronglyMeasurable w) (hw1 : ∀ φ, |w φ| ≤ 1) :
    (∫ θ, hsSchattenNorm b (∫ φ, w φ • G (φ, θ) ∂ν) q ^ q ∂μ) ≤
      ∫ φ, ∫ θ, hsSchattenNorm b (G (φ, θ)) q ^ q ∂μ ∂ν := by
  let W : Φ × Θ → HilbertSchmidtColumns ι E := fun z => w z.1 • G z
  have hW : StronglyMeasurable W := (hw.comp_measurable measurable_fst).smul hG
  have hWbound (φ : Φ) (θ : Θ) : ‖W (φ, θ)‖ ≤ M := by
    dsimp only [W]
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hw1 φ) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hbound φ θ)
  have hGsec (θ : Θ) : StronglyMeasurable (fun φ => G (φ, θ)) :=
    hG.comp_measurable (measurable_id.prodMk measurable_const)
  have hWsec (θ : Θ) : StronglyMeasurable (fun φ => W (φ, θ)) :=
    hW.comp_measurable (measurable_id.prodMk measurable_const)
  have hGi (θ : Θ) : Integrable (fun φ => G (φ, θ)) ν :=
    Integrable.of_bound (hGsec θ).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun φ => hbound φ θ)
  have hWi (θ : Θ) : Integrable (fun φ => W (φ, θ)) ν :=
    Integrable.of_bound (hWsec θ).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun φ => hWbound φ θ)
  have hAvm : StronglyMeasurable (fun θ => ∫ φ, W (φ, θ) ∂ν) := hW.integral_prod_left'
  have hAvbound (θ : Θ) : ‖∫ φ, W (φ, θ) ∂ν‖ ≤ M := by
    calc
      _ ≤ ∫ φ, ‖W (φ, θ)‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ _φ : Φ, M ∂ν := integral_mono (hWi θ).norm (integrable_const M) (fun φ => hWbound φ θ)
      _ = M := by simp
  have hAvi := integrable_hsSchattenNorm_rpow_of_bound b hq hM
    (fun θ => ∫ φ, W (φ, θ) ∂ν) hAvm hAvbound (μ := μ)
  have hPow := integrable_hsSchattenNorm_rpow_of_bound b hq hM G hG
    (fun z => hbound z.1 z.2) (μ := ν.prod μ)
  have hpoint (θ : Θ) : hsSchattenNorm b (∫ φ, W (φ, θ) ∂ν) q ^ q ≤
      ∫ φ, hsSchattenNorm b (G (φ, θ)) q ^ q ∂ν := by
    have hSp := integrable_hsSchattenNorm b hq (hGi θ)
    have hPowθ := integrable_hsSchattenNorm_rpow_of_bound b hq hM
      (fun φ => G (φ, θ)) (hGsec θ) (fun φ => hbound φ θ) (μ := ν)
    have hJ := (convexOn_rpow (by linarith : 1 ≤ q)).map_integral_le
      (Real.continuous_rpow_const (by linarith : 0 ≤ q)).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun φ => hsSchattenNorm_nonneg b (G (φ, θ)) q) hSp hPowθ
    have hSpAv := hsSchattenNorm_integral_le_of_ae_bound b hq (fun φ => W (φ, θ)) (hWi θ)
      (fun φ => hsSchattenNorm b (G (φ, θ)) q) hSp (Filter.Eventually.of_forall fun φ => by
        dsimp only [W]
        rw [hsSchattenNorm_smul b _ _ hq]
        exact (mul_le_mul_of_nonneg_right (hw1 φ) (hsSchattenNorm_nonneg b _ q)).trans_eq (one_mul _))
    exact (Real.rpow_le_rpow (hsSchattenNorm_nonneg b _ q) hSpAv (by linarith)).trans hJ
  calc
    _ ≤ ∫ θ, ∫ φ, hsSchattenNorm b (G (φ, θ)) q ^ q ∂ν ∂μ :=
      integral_mono hAvi hPow.integral_prod_right hpoint
    _ = _ := (integral_integral_swap hPow).symm

/-- The uniform inner-moment corollary includes B=0 directly, with no
normalization or division by B or the weight mass. -/
theorem hsSchattenNorm_angular_average_rpow_le_bound (b : HilbertBasis ι ℝ H)
    {q M B : ℝ} (hq : 2 ≤ q) (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (G : Φ × Θ → HilbertSchmidtColumns ι E) (hG : StronglyMeasurable G)
    (hbound : ∀ φ θ, ‖G (φ, θ)‖ ≤ M)
    (w : Φ → ℝ) (hw : StronglyMeasurable w) (hw1 : ∀ φ, |w φ| ≤ 1)
    (hmoment : ∀ φ, ∫ θ, hsSchattenNorm b (G (φ, θ)) q ^ q ∂μ ≤ B ^ q) :
    (∫ θ, hsSchattenNorm b (∫ φ, w φ • G (φ, θ) ∂ν) q ^ q ∂μ) ≤ B ^ q := by
  have hPow := integrable_hsSchattenNorm_rpow_of_bound b hq hM G hG
    (fun z => hbound z.1 z.2) (μ := ν.prod μ)
  exact (hsSchattenNorm_angular_average_rpow_le b hq hM G hG hbound w hw hw1).trans
    ((integral_mono hPow.integral_prod_left (integrable_const (B ^ q)) hmoment).trans_eq (by simp))

end Angular

section LpNorm
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Actual matching-exponent moment quantity on the original HS fields. -/
def hsSchattenLpNorm (b : HilbertBasis ι ℝ H) (μ : Measure Ω)
    (F : Ω → HilbertSchmidtColumns ι E) (q : ℝ) : ℝ :=
  (∫ ω, hsSchattenNorm b (F ω) q ^ q ∂μ) ^ q⁻¹

theorem hsSchattenLpNorm_nonneg (b : HilbertBasis ι ℝ H)
    (F : Ω → HilbertSchmidtColumns ι E) (q : ℝ) : 0 ≤ hsSchattenLpNorm b μ F q := by
  apply Real.rpow_nonneg
  exact integral_nonneg fun ω => Real.rpow_nonneg (hsSchattenNorm_nonneg b _ q) q

private theorem hsSchattenLpNorm_eLpNorm (b : HilbertBasis ι ℝ H) {q : ℝ} (hq : 0 < q)
    (F : Ω → HilbertSchmidtColumns ι E)
    (hF : MemLp (fun ω => hsSchattenNorm b (F ω) q) (ENNReal.ofReal q) μ) :
    eLpNorm (fun ω => hsSchattenNorm b (F ω) q) (ENNReal.ofReal q) μ =
      ENNReal.ofReal (hsSchattenLpNorm b μ F q) := by
  have h := hF.eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hq.le] at h
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hsSchattenNorm_nonneg b _ q)] at h
  exact h

private theorem memLp_hsSchatten_of_bound [IsFiniteMeasure μ]
    (b : HilbertBasis ι ℝ H) {q M : ℝ} (hq : 2 ≤ q)
    (F : Ω → HilbertSchmidtColumns ι E) (hF : StronglyMeasurable F)
    (hbound : ∀ ω, ‖F ω‖ ≤ M) :
    MemLp (fun ω => hsSchattenNorm b (F ω) q) (ENNReal.ofReal q) μ := by
  apply MemLp.of_bound ((hsSchattenNorm_continuous b hq).comp_stronglyMeasurable hF).aestronglyMeasurable M
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hsSchattenNorm_nonneg b _ q)]
    exact (hsSchattenNorm_le_hsNorm b _ hq).trans (hbound ω)

/-- The actual matching-Lq triangle follows from the proved pointwise
Schatten triangle and scalar integral Minkowski on a finite measure. -/
theorem hsSchattenLpNorm_add_le_of_bound [IsFiniteMeasure μ]
    (b : HilbertBasis ι ℝ H) {q M N : ℝ} (hq : 2 ≤ q)
    (F G : Ω → HilbertSchmidtColumns ι E) (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (hFb : ∀ ω, ‖F ω‖ ≤ M) (hGb : ∀ ω, ‖G ω‖ ≤ N) :
    hsSchattenLpNorm b μ (F + G) q ≤ hsSchattenLpNorm b μ F q + hsSchattenLpNorm b μ G q := by
  have hq0 : 0 < q := by linarith
  have hFp := memLp_hsSchatten_of_bound (μ := μ) b hq F hF hFb
  have hGp := memLp_hsSchatten_of_bound (μ := μ) b hq G hG hGb
  have hsum := memLp_hsSchatten_of_bound (μ := μ) b hq (F + G) (hF.add hG)
    (fun ω => (norm_add_le (F ω) (G ω)).trans (add_le_add (hFb ω) (hGb ω)))
  have hmono : eLpNorm (fun ω => hsSchattenNorm b ((F + G) ω) q) (ENNReal.ofReal q) μ ≤
      eLpNorm ((fun ω => hsSchattenNorm b (F ω) q) + (fun ω => hsSchattenNorm b (G ω) q))
        (ENNReal.ofReal q) μ := by
    apply eLpNorm_mono_ae
    exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs, Pi.add_apply,
        abs_of_nonneg (hsSchattenNorm_nonneg b _ q),
        abs_of_nonneg (add_nonneg (hsSchattenNorm_nonneg b _ q) (hsSchattenNorm_nonneg b _ q))]
      exact hsSchattenNorm_add_le b (F ω) (G ω) hq
  have h := hmono.trans (eLpNorm_add_le hFp.aestronglyMeasurable hGp.aestronglyMeasurable
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ q)))
  rw [hsSchattenLpNorm_eLpNorm b hq0 (F + G) hsum,
    hsSchattenLpNorm_eLpNorm b hq0 F hFp, hsSchattenLpNorm_eLpNorm b hq0 G hGp,
    ← ENNReal.ofReal_add (hsSchattenLpNorm_nonneg b F q) (hsSchattenLpNorm_nonneg b G q)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hsSchattenLpNorm_nonneg b F q)
    (hsSchattenLpNorm_nonneg b G q))).mp h

/-- Exact scalar homogeneity of the genuine integrated quantity. -/
theorem hsSchattenLpNorm_smul (b : HilbertBasis ι ℝ H)
    (F : Ω → HilbertSchmidtColumns ι E) (a : ℝ) {q : ℝ} (hq : 2 ≤ q) :
    hsSchattenLpNorm b μ (a • F) q = |a| * hsSchattenLpNorm b μ F q := by
  unfold hsSchattenLpNorm
  simp_rw [Pi.smul_apply, hsSchattenNorm_smul b _ _ hq,
    Real.mul_rpow (abs_nonneg a) (hsSchattenNorm_nonneg b _ q)]
  rw [integral_const_mul, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) q)
    (integral_nonneg fun ω => Real.rpow_nonneg (hsSchattenNorm_nonneg b (F ω) q) q),
    Real.rpow_rpow_inv (abs_nonneg a) (by linarith : q ≠ 0)]

theorem hsSchattenLpNorm_zero (b : HilbertBasis ι ℝ H) {q : ℝ} (hq : 2 ≤ q) :
    hsSchattenLpNorm b μ (0 : Ω → HilbertSchmidtColumns ι E) q = 0 := by
  have h := hsSchattenLpNorm_smul (μ := μ) b (0 : Ω → HilbertSchmidtColumns ι E) 0 hq
  simpa only [zero_smul, abs_zero, zero_mul] using h

/-- Actual finite-sum triangle on any finite measure, with measurability
and integrability supplied by the displayed genuine HS bounds. -/
theorem hsSchattenLpNorm_sum_le_of_bound [IsFiniteMeasure μ] {J : Type*}
    (b : HilbertBasis ι ℝ H) (s : Finset J) (F : J → Ω → HilbertSchmidtColumns ι E)
    (M : J → ℝ) {q : ℝ} (hq : 2 ≤ q)
    (hF : ∀ j, StronglyMeasurable (F j)) (hFb : ∀ j ω, ‖F j ω‖ ≤ M j) :
    hsSchattenLpNorm b μ (∑ j ∈ s, F j) q ≤ ∑ j ∈ s, hsSchattenLpNorm b μ (F j) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, hsSchattenLpNorm_zero b hq, le_refl]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hsum : StronglyMeasurable (∑ k ∈ s, F k) := s.stronglyMeasurable_sum fun k _ => hF k
    have hsumBound (ω : Ω) : ‖(∑ k ∈ s, F k) ω‖ ≤ ∑ k ∈ s, M k := by
      simp only [Finset.sum_apply]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hFb k ω)
    exact (hsSchattenLpNorm_add_le_of_bound b hq (F j) (∑ k ∈ s, F k)
      (hF j) hsum (hFb j) hsumBound).trans (add_le_add le_rfl ih)

end LpNorm

section AngularNorm
variable {Φ Θ : Type*} [MeasurableSpace Φ] [MeasurableSpace Θ]
  {ν : Measure Φ} {μ : Measure Θ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

/-- The actual angular estimate in matching-Lq norm form. Both zero B
and the zero weight are included without division or normalization. -/
theorem hsSchattenLpNorm_angular_average_le_bound (b : HilbertBasis ι ℝ H)
    {q M B : ℝ} (hq : 2 ≤ q) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (G : Φ × Θ → HilbertSchmidtColumns ι E) (hG : StronglyMeasurable G)
    (hbound : ∀ φ θ, ‖G (φ, θ)‖ ≤ M)
    (w : Φ → ℝ) (hw : StronglyMeasurable w) (hw1 : ∀ φ, |w φ| ≤ 1)
    (hmoment : ∀ φ, ∫ θ, hsSchattenNorm b (G (φ, θ)) q ^ q ∂μ ≤ B ^ q) :
    hsSchattenLpNorm b μ (fun θ => ∫ φ, w φ • G (φ, θ) ∂ν) q ≤ B := by
  have h := Real.rpow_le_rpow
    (integral_nonneg fun θ => Real.rpow_nonneg (hsSchattenNorm_nonneg b _ q) q)
    (hsSchattenNorm_angular_average_rpow_le_bound (μ := μ) (ν := ν) b hq hM hB G hG hbound w hw hw1 hmoment)
    (inv_nonneg.mpr (by linarith : 0 ≤ q))
  rwa [Real.rpow_rpow_inv hB (by linarith : q ≠ 0)] at h

end AngularNorm
end
end KernelSeq
