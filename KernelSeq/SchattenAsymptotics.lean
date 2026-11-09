import KernelSeq.LogRate
import KernelSeq.SchattenInterpolation
import KernelSeq.NormalizedBernstein
import KernelSeq.ConcentrationAsymptotics
import KernelSeq.MixedPerturbation

/-!
# Probability bounds for actual logarithmic Schatten endpoints

The endpoint is formed from the actual singular-value sums of actual HS
columns. Scalar tight-tail conditions are propagated through the logarithmic
rate by outer-measure event inclusions; convergence of that rate is not an
input. The actual covariance applications keep the finite-dimensional
Bernstein premise visible. No HMS multiplier estimate is used here.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace KernelSeq

/-- Constant absorption includes a zero reference scale. If `a=0`, the
pointwise operator bound forces `δ=0`; no division by a positive scale is needed. -/
theorem logarithmicRate_absorb_constants_nonneg {δ η a b C D : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδa : δ ≤ C * a) (hηb : η ≤ D * b) :
    logarithmicRate δ η ≤ max 1 (max C D) * logarithmicRate a b := by
  by_cases ha0 : a = 0
  · have hδ0 : δ = 0 := le_antisymm (by simpa only [ha0, mul_zero] using hδa) hδ
    simp only [ha0, hδ0, logarithmicRate_zero, mul_zero, le_refl]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    simpa only [logarithmicRate_of_pos hap, mul_assoc] using
      logarithmicRate_absorb_constants hδ hη hap hb hδa hηb

/-- Explicit upper-tail tightness at deterministic scales suffices for the
weighted logarithmic rate to vanish. This is a tail premise, not an assumed
`oP` conclusion. Both reference scales may equal zero, and no independence or
measurability of the random coefficients is required. -/
theorem tendstoInMeasure_weighted_logarithmicRate_of_tight_tails
    {J Ω : Type*} [MeasurableSpace Ω] {l : Filter J} (P : Measure Ω)
    (δ η : J → Ω → ℝ) (a b w : J → ℝ)
    (hδ : ∀ i ω, 0 ≤ δ i ω) (hη : ∀ i ω, 0 ≤ η i ω)
    (hgood : ∀ᶠ i in l, 0 ≤ a i ∧ 0 ≤ b i ∧ 0 ≤ w i)
    (hδtail : ∀ q : ℝ, 0 < q → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ i in l, P {ω | C * a i < δ i ω} ≤ ENNReal.ofReal q)
    (hηtail : ∀ q : ℝ, 0 < q → ∃ D : ℝ, 0 < D ∧
      ∀ᶠ i in l, P {ω | D * b i < η i ω} ≤ ENNReal.ofReal q)
    (hscale : Tendsto (fun i => w i * logarithmicRate (a i) (b i)) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω => w i * logarithmicRate (δ i ω) (η i ω)) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_zero, Real.norm_eq_abs]
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ζ hζ
  obtain ⟨r, hr, hrζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hζ
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨C, _, hC⟩ := hδtail ((r : ℝ) / 3) (by positivity)
  obtain ⟨D, _, hD⟩ := hηtail ((r : ℝ) / 3) (by positivity)
  let K := max 1 (max C D)
  have hlim : Tendsto (fun i => K * (w i * logarithmicRate (a i) (b i))) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hscale
  filter_upwards [hgood, hC, hD, hlim.eventually (eventually_lt_nhds hε)] with i hi hCi hDi hKi
  have hsub : {ω | ε ≤ |w i * logarithmicRate (δ i ω) (η i ω)|} ⊆
      {ω | C * a i < δ i ω} ∪ {ω | D * b i < η i ω} := by
    intro ω hω
    change ε ≤ |w i * logarithmicRate (δ i ω) (η i ω)| at hω
    by_contra hnot
    have hδa : δ i ω ≤ C * a i := le_of_not_gt (fun h => hnot (Or.inl h))
    have hηb : η i ω ≤ D * b i := le_of_not_gt (fun h => hnot (Or.inr h))
    have hb := mul_le_mul_of_nonneg_left
      (logarithmicRate_absorb_constants_nonneg (hδ i ω) (hη i ω) hi.1 hi.2.1 hδa hηb) hi.2.2
    rw [abs_of_nonneg (mul_nonneg hi.2.2 (logarithmicRate_nonneg (hδ i ω) (hη i ω)))] at hω
    have hk : w i * logarithmicRate (δ i ω) (η i ω) < ε := by
      calc
        _ ≤ w i * (K * logarithmicRate (a i) (b i)) := hb
        _ = K * (w i * logarithmicRate (a i) (b i)) := by ring
        _ < ε := hKi
    exact not_lt_of_ge hω hk
  calc
    P {ω | ε ≤ |w i * logarithmicRate (δ i ω) (η i ω)|} ≤
        P {ω | C * a i < δ i ω} + P {ω | D * b i < η i ω} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal ((r : ℝ) / 3) + ENNReal.ofReal ((r : ℝ) / 3) := add_le_add hCi hDi
    _ ≤ ζ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact (ENNReal.ofReal_le_ofReal (by linarith : (r : ℝ) / 3 + r / 3 ≤ r)).trans
        (by simpa only [ENNReal.ofReal_coe_nnreal] using hrζ.le)

variable {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The optimized endpoint formed from the actual finite singular-value power
sums, with no endpoint-rate premise. -/
noncomputable def hsSchattenEndpoint (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) : ℝ :=
  sInf (Set.range (fun p : {p : ℝ // 2 ≤ p} => p.1 * hsSchattenNorm b c p.1))

theorem hsSchattenEndpoint_nonneg (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) : 0 ≤ hsSchattenEndpoint b c := by
  apply le_csInf
  · exact ⟨_, Set.mem_range_self (⟨2, le_rfl⟩ : {p : ℝ // 2 ≤ p})⟩
  · rintro _ ⟨p, rfl⟩
    exact mul_nonneg (by linarith [p.2]) (Real.rpow_nonneg (tsum_nonneg
      (fun i : HSSingularIndex b c => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _)) _)

/-- The deterministic endpoint inequality in the same zero convention as the
probability rate. A zero operator forces its actual HS columns to vanish. -/
theorem hsSchattenEndpoint_le_logarithmicRate (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    hsSchattenEndpoint b c ≤ 2 * Real.exp 1 * logarithmicRate ‖hilbertSchmidtOperator b c‖ ‖c‖ := by
  have hb := schatten_logarithmic_endpoint_inf b c
  by_cases hzero : ‖hilbertSchmidtOperator b c‖ = 0
  · simpa only [hsSchattenEndpoint, hzero, mul_zero, zero_mul, logarithmicRate_zero] using hb
  · have hp : 0 < ‖hilbertSchmidtOperator b c‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    simpa only [hsSchattenEndpoint, logarithmicRate_of_pos hp, mul_assoc] using hb

/-- The reference logarithmic rate is exactly the manuscript's `γ`, including
zero leverage. No positive lower bound on leverage or effective dimension is
used to cancel the common square-root factor. -/
theorem logarithmicRate_covariance_scales {L n N : ℝ}
    (hL : 0 ≤ L) (hn : 0 < n) (hN : 0 ≤ N) :
    logarithmicRate (Real.sqrt (L * dimensionLog N / n)) (Real.sqrt (L * N / n)) =
      Real.sqrt (L * dimensionLog N / n) *
        Real.log (Real.exp 1 + Real.sqrt (N / dimensionLog N)) := by
  have he : 0 < dimensionLog N := by linarith [one_le_dimensionLog hN]
  by_cases hz : Real.sqrt (L * dimensionLog N / n) = 0
  · simp only [hz, logarithmicRate_zero, zero_mul]
  · have hLp : 0 < L := by
      have hLne : L ≠ 0 := fun h => hz (by rw [h, zero_mul, zero_div, Real.sqrt_zero])
      exact lt_of_le_of_ne hL (Ne.symm hLne)
    have hratio : Real.sqrt (L * N / n) / Real.sqrt (L * dimensionLog N / n) =
        Real.sqrt (N / dimensionLog N) := by
      rw [← Real.sqrt_div (div_nonneg (mul_nonneg hL hN) hn.le)]
      congr 1
      field_simp [hLp.ne', hn.ne', he.ne']
    rw [logarithmicRate_of_pos (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)), hratio]

/-- Compatibility gives a fixed-confidence threshold bounded by a constant
times the original operator-norm reference scale. The retention may tend to
zero, and the proof remains valid at zero leverage. -/
theorem variance_compatibility_intrinsicThreshold_tight_bound
    {J : Type*} {l : Filter J} (L n N Q r : J → ℝ) (A : ℝ)
    (hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < n i ∧ 0 ≤ N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ Q i ≤ A ^ 2 * r i * N i)
    (hcompat : Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0))
    (z : ℝ) (hz : 0 ≤ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in l,
      normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z ≤
        C * Real.sqrt (L i * dimensionLog (N i) / n i) := by
  let v := fun i => L i * dimensionLog (N i) / n i
  have hvgood : ∀ᶠ i in l, 0 ≤ v i ∧ 0 ≤ N i ∧ 0 < Q i ∧ 0 < r i ∧ r i ≤ 1 ∧
      Q i ≤ A ^ 2 * r i * N i := by
    filter_upwards [hgood] with i hi
    exact ⟨div_nonneg (mul_nonneg hi.1 (by linarith [one_le_dimensionLog hi.2.2.1])) hi.2.1.le,
      hi.2.2⟩
  obtain ⟨hv, _, hint⟩ := variance_compatibility_scale_limits v N Q r A hvgood hcompat
  have hsqrt : Tendsto (fun i => Real.sqrt (v i)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hv
  have hdiv : Tendsto (fun i => Real.sqrt (v i) / dimensionLog (N i)) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrt
    · filter_upwards [hgood] with i hi
      exact div_nonneg (Real.sqrt_nonneg _) (by linarith [one_le_dimensionLog hi.2.2.1])
    · filter_upwards [hgood] with i hi
      exact (div_le_iff₀ (by linarith [one_le_dimensionLog hi.2.2.1] : 0 < dimensionLog (N i))).mpr
        (le_mul_of_one_le_right (Real.sqrt_nonneg _) (one_le_dimensionLog hi.2.2.1))
  have hF : Tendsto (fun i => Real.sqrt (v i) * intrinsicDimensionLog (N i) (r i) / dimensionLog (N i) +
      z * Real.sqrt (v i) / dimensionLog (N i)) l (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero, zero_add] using hint.add (tendsto_const_nhds.mul hdiv)
  refine ⟨2 * Real.sqrt (2 + z) + 4, by positivity, ?_⟩
  filter_upwards [hgood, hF.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with i hi hFi
  have hT := normalizedIntrinsicThreshold_le hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2.1 hz
  have hm := mul_le_mul_of_nonneg_left hFi.le (by positivity : 0 ≤ 4 * Real.sqrt (v i))
  dsimp [v] at hm
  nlinarith

/-- A square-integrable vector with second moment at most `q` has a uniform
strict tail at `D sqrt(q)`, including `q=0`. The zero-moment branch proves the
actual vector vanishes a.e.; it is not handled by dividing by zero. -/
theorem measure_norm_gt_mul_sqrt_le {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] (P : Measure Ω) (f : Ω → F) (hf : MemLp f 2 P)
    {q D : ℝ} (hq : 0 ≤ q) (hD : 0 < D) (hmean : (∫ ω, ‖f ω‖ ^ 2 ∂P) ≤ q) :
    P {ω | D * Real.sqrt q < ‖f ω‖} ≤ ENNReal.ofReal (1 / D ^ 2) := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  by_cases hq0 : q = 0
  · have hint : (∫ ω, ‖f ω‖ ^ 2 ∂P) = 0 := le_antisymm (by simpa only [hq0] using hmean)
      (integral_nonneg fun _ => sq_nonneg _)
    have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg ‖f ω‖) hi).mp hint
    have hevent : {ω | D * Real.sqrt q < ‖f ω‖} =ᵐ[P] (∅ : Set Ω) := by
      filter_upwards [hz] with ω hω
      apply propext
      have hn : ‖f ω‖ = 0 := sq_eq_zero_iff.mp hω
      change (D * Real.sqrt q < ‖f ω‖) ↔ False
      simp only [hq0, Real.sqrt_zero, mul_zero, hn, lt_self_iff_false]
    rw [measure_congr hevent, measure_empty]
    exact zero_le
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have ht : 0 < D * Real.sqrt q := mul_pos hD (Real.sqrt_pos.mpr hqp)
    have hm := (hi.div_const ((D * Real.sqrt q) ^ 2)).measure_le_integral
      (Eventually.of_forall (fun ω => div_nonneg (sq_nonneg ‖f ω‖) (sq_nonneg _)))
      (s := {ω | D * Real.sqrt q < ‖f ω‖}) (fun ω hω => by
        rw [le_div_iff₀ (sq_pos_of_pos ht)]
        change D * Real.sqrt q < ‖f ω‖ at hω
        nlinarith [norm_nonneg (f ω)])
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    calc
      _ ≤ q / (D * Real.sqrt q) ^ 2 := div_le_div_of_nonneg_right hmean (sq_nonneg _)
      _ = 1 / D ^ 2 := by rw [mul_pow, Real.sq_sqrt hq]; field_simp

section ActualSample

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual manuscript-oriented mixed perturbation satisfies the
logarithmic endpoint estimate on the actual covariance quarter event. -/
theorem manuscriptMixedEndpoint_le_logarithmicRate (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4) :
    hsSchattenEndpoint b (manuscriptMixedColumns b k hk lam x) ≤
      4 * Real.exp 1 * logarithmicRate (actualCovarianceDeviation k hk lam x)
        ‖normalizedHSCovarianceFluctuation b k hk lam x‖ := by
  have hop := manuscriptMixedPerturbation_norm_le
    (populationCovariance (featureEmbedding μ k hk)) (empiricalCovariance (fun i => k (x i)))
    (populationCovariance_feature_isCompact μ k hk) (empiricalCovariance_isCompact _)
    (populationCovariance_isPositive _) (empiricalCovariance_isPositive _) lam hlam hδ
  rw [← hilbertSchmidtOperator_manuscriptMixedColumns b k hk lam hlam x] at hop
  have hhs := manuscriptMixedColumns_norm_le b k hk lam hlam x hδ
  have habs := logarithmicRate_absorb_constants_nonneg
    (norm_nonneg (hilbertSchmidtOperator b (manuscriptMixedColumns b k hk lam x)))
    (norm_nonneg (manuscriptMixedColumns b k hk lam x))
    (norm_nonneg (featureRegularizedInvSqrt μ k hk lam *
      (empiricalCovariance (fun i => k (x i)) - populationCovariance (featureEmbedding μ k hk)) *
        featureRegularizedInvSqrt μ k hk lam))
    (norm_nonneg (normalizedHSCovarianceFluctuation b k hk lam x)) hop hhs
  norm_num only [max_self, show max (1 : ℝ) 2 = 2 by norm_num] at habs
  calc
    _ ≤ 2 * Real.exp 1 * logarithmicRate
        ‖hilbertSchmidtOperator b (manuscriptMixedColumns b k hk lam x)‖
        ‖manuscriptMixedColumns b k hk lam x‖ := hsSchattenEndpoint_le_logarithmicRate b _
    _ ≤ 2 * Real.exp 1 * (2 * logarithmicRate (actualCovarianceDeviation k hk lam x)
        ‖normalizedHSCovarianceFluctuation b k hk lam x‖) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ = _ := by ring

variable [IsProbabilityMeasure P] [TopologicalSpace.SeparableSpace H]

/-- A genuine finite-confidence endpoint bound for the actual sampled mixed
perturbation. Its two failure terms come from the actual normalized Bernstein
tail and the proved HS second moment. The only external theorem is the visible
finite-dimensional Bernstein premise; no covariance-rate premise is assumed.
The HS reference scale is allowed to be zero. -/
theorem measure_manuscriptMixedEndpoint_exceedance_le (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam)
    (hTropp : FiniteSpectralBernstein
      (featureCovarianceBasis (bernsteinFeature k hk lam) (bernsteinFeature_memLp k hk lam)) P)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ) (hind : iIndepFun x P)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hr : 0 < featureCovarianceRetention k hk lam) (z D : ℝ) (hz : 0 ≤ z) (hD : 0 < D) :
    P {ω | actualCovarianceDeviation k hk lam (fun i => x i ω) ≤ 1 / 4 ∧
      4 * Real.exp 1 * logarithmicRate
        (normalizedIntrinsicThreshold L (n : ℝ) (featureEffectiveDimension k hk lam)
          (featureCovarianceRetention k hk lam) z)
        (D * Real.sqrt (L / (n : ℝ) * featureEffectiveDimension k hk lam)) <
      hsSchattenEndpoint b (manuscriptMixedColumns b k hk lam (fun i => x i ω))} ≤
      ENNReal.ofReal (8 * Real.exp (-z)) + ENNReal.ofReal (1 / D ^ 2) := by
  let δ := fun ω => actualCovarianceDeviation k hk lam (fun i => x i ω)
  let η := fun ω => ‖normalizedHSCovarianceFluctuation b k hk lam (fun i => x i ω)‖
  let q := L / (n : ℝ) * featureEffectiveDimension k hk lam
  let T := normalizedIntrinsicThreshold L (n : ℝ) (featureEffectiveDimension k hk lam)
    (featureCovarianceRetention k hk lam) z
  have hLnonneg : 0 ≤ L := feature_sq_bound_nonneg (bernsteinFeature k hk lam) hL
  have hN : 0 ≤ featureEffectiveDimension k hk lam := featureEffectiveDimension_nonneg k hk lam hlam
  have hT : 0 ≤ T := normalizedIntrinsicThreshold_nonneg hLnonneg (Nat.cast_pos.mpr hn) hN hr hz
  have hq : 0 ≤ q := mul_nonneg (div_nonneg hLnonneg (Nat.cast_nonneg _)) hN
  have htδ : P {ω | T < δ ω} ≤ ENNReal.ofReal (8 * Real.exp (-z)) := by
    simpa only [T, δ, normalizedIntrinsicThreshold, intrinsicDimensionLog, dimensionLog] using
      normalized_covariance_bernstein_tail k hk lam hlam hTropp hn x hlaw hind hL hr z hz
  have htη : P {ω | D * Real.sqrt q < η ω} ≤ ENNReal.ofReal (1 / D ^ 2) := by
    exact measure_norm_gt_mul_sqrt_le P _
      (memLp_normalizedHSCovarianceFluctuation b hn x hlaw k hk lam hL) hq hD
      (integral_normalizedHSCovarianceFluctuation_sq_le b hn x hlaw
        (fun _ _ hij => hind.indepFun hij) k hk lam hlam hL)
  have hsub : {ω | δ ω ≤ 1 / 4 ∧
      4 * Real.exp 1 * logarithmicRate T (D * Real.sqrt q) <
        hsSchattenEndpoint b (manuscriptMixedColumns b k hk lam (fun i => x i ω))} ⊆
      {ω | T < δ ω} ∪ {ω | D * Real.sqrt q < η ω} := by
    intro ω hω
    by_contra hnot
    have hδT : δ ω ≤ T := le_of_not_gt (fun h => hnot (Or.inl h))
    have hηD : η ω ≤ D * Real.sqrt q := le_of_not_gt (fun h => hnot (Or.inr h))
    have hlog := (logarithmicRate_mono_left (norm_nonneg _) hδT (norm_nonneg _)).trans
      (logarithmicRate_mono_right hT (norm_nonneg _) hηD)
    exact not_lt_of_ge ((manuscriptMixedEndpoint_le_logarithmicRate b k hk lam hlam _ hω.1).trans
      (mul_le_mul_of_nonneg_left hlog (by positivity))) hω.2
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add htδ htη))

/-- The source logarithmic Schatten endpoint has the normalized consequence
predicted by its deterministic `γ` scale, for the actual feature/sample model.
Every random bound is supplied by the actual mixed perturbation, actual HS
second moment, and actual intrinsic Bernstein tail. The external finite
Bernstein theorem remains an explicit premise. Neither an HMS estimate nor
a stochastic endpoint/normalized-covariance rate is assumed.

The deterministic weight is arbitrary and may diverge. Retention can approach
zero, and all reference-scale lemmas retain their zero-leverage convention.
-/
theorem actual_weighted_schatten_endpoint_of_compatibility
    {J : Type*} {l : Filter J} (b : HilbertBasis ι ℝ H)
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (x : (i : J) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : J → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L w : J → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hw : ∀ᶠ i in l, 0 ≤ w i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) *
        Real.sqrt (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0))
    (hγ : Tendsto (fun i => w i * Real.sqrt (L i * dimensionLog
      (featureEffectiveDimension k hk (lam i)) / (n i : ℝ)) *
        Real.log (Real.exp 1 + Real.sqrt (featureEffectiveDimension k hk (lam i) /
          dimensionLog (featureEffectiveDimension k hk (lam i))))) l (𝓝 0))
    (hTropp : ∀ i, FiniteSpectralBernstein
      (featureCovarianceBasis (bernsteinFeature k hk (lam i))
        (bernsteinFeature_memLp k hk (lam i))) P) :
    TendstoInMeasure P (fun i ω => w i * hsSchattenEndpoint b
      (manuscriptMixedColumns b k hk (lam i) (fun j => x i j ω))) l (fun _ => 0) := by
  let N := fun i => featureEffectiveDimension k hk (lam i)
  let Q := fun i => featureFilterDimension k hk (φ i)
  let r := fun i => featureCovarianceRetention k hk (lam i)
  let δ := fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)
  let η := fun i ω => ‖normalizedHSCovarianceFluctuation b k hk (lam i) (fun j => x i j ω)‖
  let a := fun i => Real.sqrt (L i * dimensionLog (N i) / (n i : ℝ))
  let d := fun i => Real.sqrt (L i / (n i : ℝ) * N i)
  let G := fun i => {ω | δ i ω ≤ 1 / 4}
  have hLnonneg : ∀ i, 0 ≤ L i := fun i =>
    feature_sq_bound_nonneg (bernsteinFeature k hk (lam i)) (hL i)
  have hN : ∀ i, 0 ≤ N i := fun i => featureEffectiveDimension_nonneg k hk (lam i) (hlam i)
  have hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < (n i : ℝ) ∧ 0 ≤ N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ Q i ≤ A ^ 2 * r i * N i := by
    filter_upwards [hQ] with i hQi
    exact ⟨hLnonneg i, Nat.cast_pos.mpr (hn i), hN i, hQi,
      featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hQi,
      featureCovarianceRetention_le_one k hk (lam i) (hlam i),
      featureFilterDimension_le_retention k hk (φ i) (hlam i) hM (hf i) (h i)⟩
  have htail : ∀ z : ℝ, 0 ≤ z → ∀ᶠ i in l,
      P {ω | normalizedIntrinsicThreshold (L i) (n i : ℝ) (N i) (r i) z < |δ i ω|} ≤
        ENNReal.ofReal (8 * Real.exp (-z)) := by
    intro z hz
    filter_upwards [hgood] with i hi
    simpa only [normalizedIntrinsicThreshold, intrinsicDimensionLog, dimensionLog,
      δ, N, r, actualCovarianceDeviation, covarianceRelativeDeviation, abs_norm] using
      normalized_covariance_bernstein_tail k hk (lam i) (hlam i) (hTropp i) (hn i)
        (x i) (hlaw i) (hind i) (hL i) hi.2.2.2.2.1 z hz
  have hδ0 := (variance_compatibility_covariance_limits_of_threshold_tails P δ L
    (fun i => (n i : ℝ)) N Q r A hgood hcompat htail).1
  have hδtight : ∀ q : ℝ, 0 < q → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ i in l, P {ω | C * a i < δ i ω} ≤ ENNReal.ofReal q := by
    intro q hq
    have hexp : Tendsto (fun z : ℝ => 8 * Real.exp (-z)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
    obtain ⟨z, hz, hzq⟩ :=
      ((eventually_ge_atTop (0 : ℝ)).and (hexp.eventually (eventually_lt_nhds hq))).exists
    obtain ⟨C, hC, hTb⟩ := variance_compatibility_intrinsicThreshold_tight_bound L
      (fun i => (n i : ℝ)) N Q r A hgood hcompat z hz
    refine ⟨C, hC, ?_⟩
    filter_upwards [hTb, htail z hz] with i hi hti
    refine (measure_mono (fun ω hω => ?_)).trans
      (hti.trans (ENNReal.ofReal_le_ofReal hzq.le))
    change C * a i < δ i ω at hω
    exact hi.trans_lt hω |>.trans_le (le_abs_self _)
  have hηtight : ∀ q : ℝ, 0 < q → ∃ D : ℝ, 0 < D ∧
      ∀ᶠ i in l, P {ω | D * d i < η i ω} ≤ ENNReal.ofReal q := by
    intro q hq
    let D := 1 + 1 / q
    have hD : 0 < D := by dsimp [D]; positivity
    have hD1 : 1 ≤ D := by dsimp [D]; linarith [one_div_nonneg.mpr hq.le]
    have hqD : q * D = q + 1 := by dsimp [D]; field_simp
    have hsmall : 1 / D ^ 2 ≤ q := by
      apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hD1 (by positivity : 0 ≤ q * D)]
    refine ⟨D, hD, Eventually.of_forall fun i => ?_⟩
    exact (measure_norm_gt_mul_sqrt_le P _
      (memLp_normalizedHSCovarianceFluctuation b (hn i) (x i) (hlaw i) k hk (lam i) (hL i))
      (mul_nonneg (div_nonneg (hLnonneg i) (Nat.cast_nonneg _)) (hN i)) hD
      (integral_normalizedHSCovarianceFluctuation_sq_le b (hn i) (x i) (hlaw i)
        (fun _ _ hij => (hind i).indepFun hij) k hk (lam i) (hlam i) (hL i))).trans
      (ENNReal.ofReal_le_ofReal hsmall)
  have hscale : Tendsto (fun i => w i * logarithmicRate (a i) (d i)) l (𝓝 0) := by
    apply hγ.congr'
    filter_upwards [hgood] with i hi
    have hid : logarithmicRate (a i) (d i) = a i *
        Real.log (Real.exp 1 + Real.sqrt (N i / dimensionLog (N i))) := by
      change logarithmicRate (Real.sqrt (L i * dimensionLog (N i) / (n i : ℝ)))
        (Real.sqrt (L i / (n i : ℝ) * N i)) = _
      rw [show L i / (n i : ℝ) * N i = L i * N i / (n i : ℝ) by ring]
      exact logarithmicRate_covariance_scales hi.1 hi.2.1 hi.2.2.1
    rw [hid]
    ring
  have hlog := tendstoInMeasure_weighted_logarithmicRate_of_tight_tails P δ η a d w
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    (by filter_upwards [hw] with i hi; exact ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, hi⟩)
    hδtight hηtight hscale
  have hbad : Tendsto (fun i => P (G i)ᶜ) l (𝓝 0) := by
    have ht : Tendsto (fun i => P {ω | 1 / 4 ≤ |δ i ω|}) l (𝓝 0) := by
      simpa only [sub_zero, Real.norm_eq_abs] using
        (tendstoInMeasure_iff_norm.mp hδ0) (1 / 4) (by norm_num)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
    intro i
    apply measure_mono
    intro ω hω
    change ¬ δ i ω ≤ 1 / 4 at hω
    exact (lt_of_not_ge hω).le.trans (le_abs_self _)
  apply tendstoInMeasure_zero_of_good_events P _
    (fun i ω => (4 * Real.exp 1) * (w i * logarithmicRate (δ i ω) (η i ω))) G hbad
    (tendstoInMeasure_const_mul_zero hlog (4 * Real.exp 1))
  filter_upwards [hw] with i hi ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hi (hsSchattenEndpoint_nonneg b _))]
  have hm := mul_le_mul_of_nonneg_left
    (manuscriptMixedEndpoint_le_logarithmicRate b k hk (lam i) (hlam i) _ hω) hi
  calc
    _ ≤ w i * (4 * Real.exp 1 * logarithmicRate (δ i ω) (η i ω)) := hm
    _ = _ := by ring

end ActualSample

end KernelSeq
