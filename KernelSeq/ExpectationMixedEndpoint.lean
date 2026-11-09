import KernelSeq.ExpectationMixedMoments
import KernelSeq.ExpectationCovarianceMoments

/-!
# A genuine measurable L2 envelope for the actual mixed Schatten endpoint

Actual interpolation and the actual mixed operator/HS bounds give a
pointwise envelope on the covariance quarter event. Its second moment is
derived from the proved covariance and HS moments at the original gamma
scale. Measurability of the endpoint infimum is neither used nor assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

variable {ι H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Selection of any genuine exponent in the endpoint infimum. -/
theorem hsSchattenEndpoint_le_exponent (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenEndpoint b c ≤ p * hsSchattenNorm b c p := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact mul_nonneg (by linarith [q.2]) (hsSchattenNorm_nonneg b c _)
  · exact Set.mem_range_self (⟨p, hp⟩ : {p : ℝ // 2 ≤ p})

/-- Actual operator/HS interpolation, with both factor-two transition
bounds absorbed without dividing by a positive random norm. -/
theorem hsSchattenEndpoint_le_mixedMomentAmplitude (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {δ η p : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hp : 2 ≤ p)
    (hop : ‖hilbertSchmidtOperator b c‖ ≤ 2 * δ) (hhs : ‖c‖ ≤ 2 * η) :
    hsSchattenEndpoint b c ≤ 2 * (p * δ ^ (1 - 2 / p) * η ^ (2 / p)) := by
  have hp0 : 0 < p := by linarith
  have ha : 0 ≤ 1 - 2 / p := by
    have hh := (div_le_one hp0).mpr hp
    linarith
  have hb : 0 ≤ 2 / p := by positivity
  have hi := hsSchattenNorm_le_opNorm_mul_hsNorm b c hp
  have hmono := mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hop ha)
    (Real.rpow_le_rpow (norm_nonneg _) hhs hb)
    (Real.rpow_nonneg (norm_nonneg c) _) (Real.rpow_nonneg (by positivity : 0 ≤ 2 * δ) _)
  have he : (2 * δ) ^ (1 - 2 / p) * (2 * η) ^ (2 / p) =
      2 * (δ ^ (1 - 2 / p) * η ^ (2 / p)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hη]
    calc
      _ = ((2 : ℝ) ^ (1 - 2 / p) * 2 ^ (2 / p)) *
          (δ ^ (1 - 2 / p) * η ^ (2 / p)) := by ring
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          show (1 - 2 / p) + 2 / p = 1 by ring, Real.rpow_one]
  calc
    _ ≤ p * hsSchattenNorm b c p := hsSchattenEndpoint_le_exponent b c hp
    _ ≤ p * ((2 * δ) ^ (1 - 2 / p) * (2 * η) ^ (2 / p)) :=
      mul_le_mul_of_nonneg_left (hi.trans hmono) hp0.le
    _ = _ := by rw [he]; ring

section ActualSample

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The actual scalar envelope. It uses genuine measurable operator and HS
norms; its exponent depends only on the population effective dimension. -/
def actualMixedEndpointEnvelope (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) {n : ℕ} (x : Fin n → X) : ℝ :=
  let p := mixedMomentExponent (featureEffectiveDimension k hk lam /
    dimensionLog (featureEffectiveDimension k hk lam))
  2 * (p * actualCovarianceDeviation k hk lam x ^ (1 - 2 / p) *
    ‖normalizedHSCovarianceFluctuation b k hk lam x‖ ^ (2 / p))

theorem actualMixedEndpointEnvelope_nonneg (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) {n : ℕ} (x : Fin n → X) :
    0 ≤ actualMixedEndpointEnvelope b k hk lam x := by
  have hp := mixedMomentExponent_ge_two (featureEffectiveDimension k hk lam /
    dimensionLog (featureEffectiveDimension k hk lam))
  dsimp only [actualMixedEndpointEnvelope]
  exact mul_nonneg (by norm_num) (mul_nonneg
    (mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))
    (Real.rpow_nonneg (norm_nonneg _) _))

/-- On the actual quarter event, the genuine optimized Schatten endpoint
is dominated by the explicit measurable envelope. -/
theorem manuscriptMixedEndpoint_le_actualMixedEndpointEnvelope (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam)
    {n : ℕ} (x : Fin n → X) (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4) :
    hsSchattenEndpoint b (manuscriptMixedColumns b k hk lam x) ≤
      actualMixedEndpointEnvelope b k hk lam x := by
  have hop := manuscriptMixedPerturbation_norm_le
    (populationCovariance (featureEmbedding μ k hk)) (empiricalCovariance (fun i => k (x i)))
    (populationCovariance_feature_isCompact μ k hk) (empiricalCovariance_isCompact _)
    (populationCovariance_isPositive _) (empiricalCovariance_isPositive _) lam hlam hδ
  rw [← hilbertSchmidtOperator_manuscriptMixedColumns b k hk lam hlam x] at hop
  exact hsSchattenEndpoint_le_mixedMomentAmplitude b _ (norm_nonneg _) (norm_nonneg _)
    (mixedMomentExponent_ge_two _) hop (manuscriptMixedColumns_norm_le b k hk lam hlam x hδ)

variable [TopologicalSpace.SeparableSpace H]

omit [IsProbabilityMeasure P] in
/-- True L2 membership at every index, including zero effective dimension.
No strong measurability or integrability of an infimum is needed. -/
theorem actualMixedEndpointEnvelope_memLp (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    MemLp (fun ω => actualMixedEndpointEnvelope b k hk lam (fun j => x j ω)) 2 P := by
  have hη := (memLp_normalizedHSCovarianceFluctuation b hn x hlaw k hk lam hL).norm
  by_cases hN : featureEffectiveDimension k hk lam = 0
  · have he : (fun ω => actualMixedEndpointEnvelope b k hk lam (fun j => x j ω)) =
        (fun ω => 4 * ‖normalizedHSCovarianceFluctuation b k hk lam (fun j => x j ω)‖) := by
      funext ω
      simp only [actualMixedEndpointEnvelope, mixedMomentExponent, hN, zero_div,
        Real.sqrt_zero, add_zero, Real.log_exp]
      norm_num
      ring
    rw [he]
    exact hη.const_mul 4
  have hNpos : 0 < featureEffectiveDimension k hk lam := lt_of_le_of_ne
    (featureEffectiveDimension_nonneg k hk lam hlam) (Ne.symm hN)
  have hell : 0 < dimensionLog (featureEffectiveDimension k hk lam) :=
    lt_of_lt_of_le zero_lt_one (one_le_dimensionLog hNpos.le)
  exact (mixedMomentAmplitude_memLp
    (memLp_actualCovarianceDeviation b hn x hlaw k hk lam hL) hη
    (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun _ => norm_nonneg _)
    (mixedMomentExponent_gt_two (div_pos hNpos hell))).const_mul 2

/-- A numerical constant independent of regularization, sample size,
retention, the target and the effective dimension. -/
def mixedEndpointMomentConstant : ℝ := 16 * (768 * Real.exp 1) * Real.exp 2

theorem mixedEndpointMomentConstant_nonneg : 0 ≤ mixedEndpointMomentConstant := by
  dsimp only [mixedEndpointMomentConstant]
  positivity

private theorem integral_actualMixedEndpointEnvelope_sq_le_of_covariance_moment
    (b : HilbertBasis ι ℝ H) {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (hind : iIndepFun x P)
    (k : X → H) (hk : MemLp k 2 μ) {lam L : ℝ} (hlam : 0 < lam)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hN : 0 < featureEffectiveDimension k hk lam)
    (hδmoment : (∫ ω, actualCovarianceDeviation k hk lam (fun j => x j ω) ^ 2 ∂P) ≤
      (768 * Real.exp 1) * (L * dimensionLog (featureEffectiveDimension k hk lam) / (n : ℝ))) :
    (∫ ω, actualMixedEndpointEnvelope b k hk lam (fun j => x j ω) ^ 2 ∂P) ≤
      mixedEndpointMomentConstant * originalBiasGamma L (n : ℝ)
        (featureEffectiveDimension k hk lam) ^ 2 := by
  let δ := fun ω => actualCovarianceDeviation k hk lam (fun j => x j ω)
  let η := fun ω => ‖normalizedHSCovarianceFluctuation b k hk lam (fun j => x j ω)‖
  let p := mixedMomentExponent (featureEffectiveDimension k hk lam /
    dimensionLog (featureEffectiveDimension k hk lam))
  have hL0 : 0 ≤ L := feature_sq_bound_nonneg (bernsteinFeature k hk lam) hL
  have hC : 1 ≤ 768 * Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hhs := integral_normalizedHSCovarianceFluctuation_sq_le b hn x hlaw
    (fun i j hij => hind.indepFun hij) k hk lam hlam hL
  have hηmoment : (∫ ω, η ω ^ 2 ∂P) ≤
      (768 * Real.exp 1) * (L * featureEffectiveDimension k hk lam / (n : ℝ)) := by
    calc
      _ ≤ L / (n : ℝ) * featureEffectiveDimension k hk lam := hhs
      _ = L * featureEffectiveDimension k hk lam / (n : ℝ) := by ring
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hC
  have hm := integral_mixedMomentAmplitude_sq_le_originalBiasGamma
    (memLp_actualCovarianceDeviation b hn x hlaw k hk lam hL)
    (memLp_normalizedHSCovarianceFluctuation b hn x hlaw k hk lam hL).norm
    (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun _ => norm_nonneg _)
    (zero_le_one.trans hC) hL0 (Nat.cast_pos.mpr hn) hN hδmoment hηmoment
  have he : (∫ ω, actualMixedEndpointEnvelope b k hk lam (fun j => x j ω) ^ 2 ∂P) =
      4 * (∫ ω, mixedMomentAmplitude p δ η ω ^ 2 ∂P) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp only [actualMixedEndpointEnvelope, mixedMomentAmplitude, p, δ, η]
      ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by
    dsimp only [mixedEndpointMomentConstant]
    ring)

/-- The actual endpoint envelope has the original gamma² second moment,
eventually under the original variance compatibility. Both input moments
are proved from the actual independent feature samples inside the proof. -/
theorem integral_actualMixedEndpointEnvelope_sq_le_original_scale_eventually
    {J : Type*} {l : Filter J} (b : HilbertBasis ι ℝ H)
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (x : (i : J) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    (φ : J → ℝ → ℝ) {M ρ A : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L : J → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, (∫ ω, actualMixedEndpointEnvelope b k hk (lam i) (fun j => x i j ω) ^ 2 ∂P) ≤
      mixedEndpointMomentConstant * originalBiasGamma (L i) (n i : ℝ)
        (featureEffectiveDimension k hk (lam i)) ^ 2 := by
  have hδmoment := integral_actualCovarianceDeviation_sq_le_original_scale_eventually
    b n hn x hlaw hind k hk lam hlam φ hM hf h L hL hQ hcompat
  filter_upwards [hQ, hδmoment] with i hQi hδi
  have hN : 0 < featureEffectiveDimension k hk (lam i) := by
    have hp := hQi.trans_le
      (featureFilterDimension_le_effectiveDimension k hk (φ i) (hlam i) hM (hf i) (h i))
    by_contra hnot
    exact (not_le_of_gt hp) (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg A) (not_lt.mp hnot))
  exact integral_actualMixedEndpointEnvelope_sq_le_of_covariance_moment b (hn i) (x i)
    (hlaw i) (hind i) k hk (hlam i) (hL i) hN hδi

end ActualSample
end
end KernelSeq
