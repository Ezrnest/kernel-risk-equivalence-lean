import KernelSeq.CovarianceMoments
import KernelSeq.OperatorTrace
import KernelSeq.EffectiveDimension
import KernelSeq.UniformBernsteinInterface
import Mathlib.Probability.Independence.Basic

/-!
# The explicit external finite-dimensional Bernstein leaf and its application

`FiniteIntrinsicBernstein` is a named proposition, not a theorem or an axiom.
It records the finite-dimensional selfadjoint specialization of the intrinsic
Bernstein inequality (Tropp 2015, Theorem 7.3.1; the Hermitian two-block
specialization has prefactor `8 trace(V)/‖V‖`; author source:
https://users.cms.caltech.edu/~jtropp/books/Tro14-Introduction-Matrix-FnTML-rev.pdf).
The broader proposition is retained separately. The actual covariance
applications below use `FiniteUniformIntrinsicBernstein`: their per-increment
variance bound is derived with the same common majorant, which is the version
needed by the project and admits a Golden--Thompson proof.

The covariance application does prove all model hypotheses: actual independent
sampled centered rank-one operators, their integrability and centered means,
selfadjointness, increment bound, and genuine Loewner variance majorant.
It does not prove the external Bernstein leaf or an infinite-dimensional
approximation theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace KernelSeq

noncomputable section

variable {H Ω X ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace Ω] [MeasurableSpace X]

local instance : MeasurableSpace (H →L[ℝ] H) := borel (H →L[ℝ] H)
local instance : BorelSpace (H →L[ℝ] H) := ⟨rfl⟩

/-- Exact unproved external leaf. Finite dimension and probability are explicit
antecedents, so no theorem using this interface silently asserts Bernstein. -/
def FiniteIntrinsicBernstein (b : HilbertBasis ι ℝ H) (P : Measure Ω) : Prop :=
  IsProbabilityMeasure P → FiniteDimensional ℝ H →
  ∀ (n : ℕ) (Y : Fin n → Ω → H →L[ℝ] H) (R : ℝ) (V : H →L[ℝ] H) (t : ℝ),
    0 ≤ R →
    (∀ i, AEStronglyMeasurable (Y i) P) →
    (∀ i, Integrable (Y i) P) →
    (∀ i, Integrable (fun ω => Y i ω * Y i ω) P) →
    iIndepFun Y P →
    (∀ i, (∫ ω, Y i ω ∂P) = 0) →
    (∀ i, ∀ᵐ ω ∂P, IsSelfAdjoint (Y i ω)) →
    (∀ i, ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ R) →
    V.IsPositive →
    (∑ i, ∫ ω, Y i ω * Y i ω ∂P) ≤ V →
    0 < ‖V‖ → Real.sqrt ‖V‖ + R / 3 ≤ t →
    P {ω | t ≤ ‖∑ i, Y i ω‖} ≤
      ENNReal.ofReal (8 * (basisTrace b V / ‖V‖) *
        Real.exp (-(t ^ 2) / (2 * (‖V‖ + R * t / 3))))

omit [CompleteSpace H] in
/-- Change of variables for actual Bochner means under the sample law. -/
theorem bochner_integral_comp_measurePreserving {μ : Measure X} {P : Measure Ω}
    (x : Ω → X) (hlaw : MeasurePreserving x P μ) (F : X → H →L[ℝ] H)
    (hF : AEStronglyMeasurable F μ) :
    (∫ ω, F (x ω) ∂P) = ∫ y, F y ∂μ := by
  have h := integral_map hlaw.aemeasurable
    (show AEStronglyMeasurable F (P.map x) by simpa only [hlaw.map_eq] using hF)
  rw [hlaw.map_eq] at h
  exact h.symm

/-- The variance-majorant norm is genuinely positive when the covariance norm
is positive; a feature bound also forces a positive bound in this case. -/
theorem covariance_variance_majorant_norm_pos {μ : Measure X} [IsProbabilityMeasure μ]
    (u : X → H) (hu : MemLp u 2 μ) {L : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L)
    (hC : 0 < ‖populationCovariance (featureEmbedding μ u hu)‖)
    {n : ℕ} (hn : 0 < n) :
    0 < ‖((n : ℝ) * L) • populationCovariance (featureEmbedding μ u hu)‖ := by
  have hL : 0 < L := hC.trans_le (populationCovariance_norm_le_feature_bound u hu hbound)
  have hnL : 0 < (n : ℝ) * L := mul_pos (by exact_mod_cast hn) hL
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hnL]
  exact mul_pos hnL hC

/-- The actual covariance tail, conditional only on the stated external finite
Bernstein leaf. Every model premise of that leaf is proved here from the sample
law, full independence, L² feature, and a.e. feature bound. -/
theorem finite_covariance_sum_tail [FiniteDimensional ℝ H]
    {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (b : HilbertBasis ι ℝ H) (hTropp : FiniteUniformIntrinsicBernstein b P)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ) (hind : iIndepFun x P)
    (u : X → H) (hu : MemLp u 2 μ) {L : ℝ} (hbound : ∀ᵐ y ∂μ, ‖u y‖ ^ 2 ≤ L)
    (hC : 0 < ‖populationCovariance (featureEmbedding μ u hu)‖) (t : ℝ)
    (ht : Real.sqrt ‖((n : ℝ) * L) • populationCovariance (featureEmbedding μ u hu)‖ +
      (2 * L) / 3 ≤ t) :
    P {ω | t ≤ ‖∑ i, centeredRankOne u hu (x i ω)‖} ≤
      ENNReal.ofReal (8 *
        (basisTrace b (((n : ℝ) * L) • populationCovariance (featureEmbedding μ u hu)) /
          ‖((n : ℝ) * L) • populationCovariance (featureEmbedding μ u hu)‖) *
        Real.exp (-(t ^ 2) /
          (2 * (‖((n : ℝ) * L) • populationCovariance (featureEmbedding μ u hu)‖ + (2 * L) * t / 3)))) := by
  let C := populationCovariance (featureEmbedding μ u hu)
  let Y := fun i ω => centeredRankOne u hu (x i ω)
  have hY : ∀ i, Integrable (Y i) P := fun i =>
    (hlaw i).integrable_comp_of_integrable (integrable_centeredRankOne u hu)
  have hY2 : ∀ i, Integrable (fun ω => Y i ω * Y i ω) P := fun i =>
    (hlaw i).integrable_comp_of_integrable (integrable_centeredRankOne_square u hu hbound)
  have hmean (i : Fin n) : (∫ ω, Y i ω ∂P) = 0 := by
    rw [bochner_integral_comp_measurePreserving (x i) (hlaw i) _
      (integrable_centeredRankOne u hu).1]
    exact integral_centeredRankOne u hu
  have hindY : iIndepFun Y P := by
    apply hind.comp₀ (fun _ => centeredRankOne u hu) (fun i => (hlaw i).aemeasurable)
    intro i
    rw [(hlaw i).map_eq]
    exact (integrable_centeredRankOne u hu).1.aemeasurable
  have hnorm (i : Fin n) : ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ 2 * L :=
    (hlaw i).quasiMeasurePreserving.ae (centeredRankOne_norm_le_two u hu hbound)
  have hmoment (i : Fin n) : (∫ ω, Y i ω * Y i ω ∂P) ≤ L • C := by
    rw [bochner_integral_comp_measurePreserving (x i) (hlaw i) _
      (integrable_centeredRankOne_square u hu hbound).1]
    exact integral_centeredRankOne_square_le u hu hbound
  have hcommon (i : Fin n) : (∫ ω, Y i ω * Y i ω ∂P) ≤
      (n : ℝ)⁻¹ • (((n : ℝ) * L) • C) := by
    have heq : (n : ℝ)⁻¹ • (((n : ℝ) * L) • C) = L • C := by
      rw [smul_smul]
      congr 1
      field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
    rw [heq]
    exact hmoment i
  have hL := feature_sq_bound_nonneg u hbound
  exact hTropp inferInstance inferInstance n Y (2 * L) (((n : ℝ) * L) • C) t
    (mul_nonneg (by norm_num) hL) (fun i => (hY i).1) hY hY2 hindY hmean
    (fun i => Eventually.of_forall (fun ω => centeredRankOne_isSelfAdjoint u hu (x i ω))) hnorm
    ((populationCovariance_isPositive _).smul_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hL))
    hcommon (covariance_variance_majorant_norm_pos u hu hbound hC hn) ht

/-- The actual covariance trace is the feature second moment. Diagonal
summability follows from integrated Parseval in the specified countable basis. -/
theorem populationCovariance_basisTrace [Countable ι]
    {μ : Measure X} (b : HilbertBasis ι ℝ H) (u : X → H) (hu : MemLp u 2 μ) :
    Summable (fun i => inner ℝ (b i) (populationCovariance (featureEmbedding μ u hu) (b i))) ∧
      basisTrace b (populationCovariance (featureEmbedding μ u hu)) = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hcoord (i : ι) : inner ℝ (b i) (populationCovariance (featureEmbedding μ u hu) (b i)) =
      ∫ x, inner ℝ (b i) (u x) ^ 2 ∂μ := by
    rw [populationCovariance_eq_integral u hu,
      inner_integral_operator_apply _ (integrable_rankOne_feature u hu)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      simp only [InnerProductSpace.rankOne_apply, inner_smul_right,
        real_inner_comm (b i) (u x), pow_two])
  have hs := hasSum_integral_sq_hilbertBasis b u hu
  constructor
  · exact hs.summable.congr (fun i => (hcoord i).symm)
  · change (∑' i, inner ℝ (b i) (populationCovariance (featureEmbedding μ u hu) (b i))) = _
    simp_rw [hcoord]
    exact hs.tsum_eq

omit [CompleteSpace H] in
/-- Positive scaling cancels exactly from the intrinsic trace/norm ratio. -/
theorem basisTrace_smul_div_norm (b : HilbertBasis ι ℝ H) (C : H →L[ℝ] H)
    (hdiag : Summable (fun i => inner ℝ (b i) (C (b i)))) (a : ℝ) (ha : 0 < a)
    (hC : 0 < ‖C‖) :
    basisTrace b (a • C) / ‖a • C‖ = basisTrace b C / ‖C‖ := by
  rw [basisTrace_smul b a C hdiag, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  field_simp [ha.ne', hC.ne']

/-- The actual variance-majorant norm scales as `n L ‖C‖`; no substituted
variance-norm certificate is required. -/
theorem covariance_variance_majorant_norm {μ : Measure X} [IsProbabilityMeasure μ]
    (u : X → H) (hu : MemLp u 2 μ) {L : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ L) (n : ℕ) :
    ‖((n : ℝ) * L) • populationCovariance (featureEmbedding μ u hu)‖ =
      ((n : ℝ) * L) * ‖populationCovariance (featureEmbedding μ u hu)‖ := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (feature_sq_bound_nonneg u hbound))]

/-- The same conditional finite-dimensional tail with the intrinsic prefactor
written as the true feature second moment divided by the covariance norm.
For a whitened feature this is the `N1/rho` ratio after the separate actual
normalized-covariance identification. -/
theorem finite_covariance_sum_tail_featureTrace [FiniteDimensional ℝ H] [Countable ι]
    {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (b : HilbertBasis ι ℝ H) (hTropp : FiniteUniformIntrinsicBernstein b P)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ) (hind : iIndepFun x P)
    (u : X → H) (hu : MemLp u 2 μ) {L : ℝ} (hbound : ∀ᵐ y ∂μ, ‖u y‖ ^ 2 ≤ L)
    (hC : 0 < ‖populationCovariance (featureEmbedding μ u hu)‖) (t : ℝ)
    (ht : Real.sqrt (((n : ℝ) * L) * ‖populationCovariance (featureEmbedding μ u hu)‖) +
      (2 * L) / 3 ≤ t) :
    P {ω | t ≤ ‖∑ i, centeredRankOne u hu (x i ω)‖} ≤
      ENNReal.ofReal (8 *
        ((∫ y, ‖u y‖ ^ 2 ∂μ) / ‖populationCovariance (featureEmbedding μ u hu)‖) *
        Real.exp (-(t ^ 2) /
          (2 * (((n : ℝ) * L) * ‖populationCovariance (featureEmbedding μ u hu)‖ + (2 * L) * t / 3)))) := by
  have hnrm := covariance_variance_majorant_norm u hu hbound n
  have hb := finite_covariance_sum_tail b hTropp hn x hlaw hind u hu hbound hC t
    (by simpa only [hnrm] using ht)
  have hL : 0 < L := hC.trans_le (populationCovariance_norm_le_feature_bound u hu hbound)
  have hratio := basisTrace_smul_div_norm b _ (populationCovariance_basisTrace b u hu).1
    ((n : ℝ) * L) (mul_pos (by exact_mod_cast hn) hL) hC
  rw [hratio, (populationCovariance_basisTrace b u hu).2, hnrm] at hb
  exact hb

end

end KernelSeq
