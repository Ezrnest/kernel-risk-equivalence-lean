import KernelSeq.BernsteinTailScale

/-!
# Variance compatibility implies vanishing intrinsic Bernstein thresholds

The retention is allowed to approach zero, and the leverage bound may equal
zero. The deterministic estimates never divide by the leverage or its square
root. The probabilistic conclusion below uses visible exponential tails at
these actual thresholds, not an assumed covariance convergence rate.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace KernelSeq

/-- The exact normalized Bernstein threshold for covariance increments. -/
noncomputable def normalizedIntrinsicThreshold (L n N r z : ℝ) : ℝ :=
  bernsteinThreshold (n * L * r) (2 * L) (intrinsicDimensionLog N r + z) / n

/-- Its nonnegativity includes the zero-leverage case. -/
theorem normalizedIntrinsicThreshold_nonneg {L n N r z : ℝ}
    (hL : 0 ≤ L) (hn : 0 < n) (hN : 0 ≤ N) (hr : 0 < r) (hz : 0 ≤ z) :
    0 ≤ normalizedIntrinsicThreshold L n N r z := by
  have hi : 1 ≤ intrinsicDimensionLog N r := one_le_dimensionLog (div_nonneg hN hr.le)
  exact div_nonneg (bernsteinThreshold_nonneg (by positivity : 0 ≤ 2 * L) (by linarith)) hn.le

/-- The intrinsic square-root logarithm is controlled without a retention
lower bound. The linear term is factored using `sqrt(v)²=v`, including `v=0`. -/
theorem normalizedIntrinsicThreshold_le {L n N r z : ℝ}
    (hL : 0 ≤ L) (hn : 0 < n) (hN : 0 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) (hz : 0 ≤ z) :
    normalizedIntrinsicThreshold L n N r z ≤
      2 * Real.sqrt (2 + z) * Real.sqrt (L * dimensionLog N / n) +
      4 * Real.sqrt (L * dimensionLog N / n) *
        (Real.sqrt (L * dimensionLog N / n) * intrinsicDimensionLog N r / dimensionLog N +
          z * Real.sqrt (L * dimensionLog N / n) / dimensionLog N) := by
  let v := L * dimensionLog N / n
  have he : 1 ≤ dimensionLog N := one_le_dimensionLog hN
  have hep : 0 < dimensionLog N := by linarith
  have hi : 1 ≤ intrinsicDimensionLog N r := one_le_dimensionLog (div_nonneg hN hr.le)
  have hs : 0 ≤ intrinsicDimensionLog N r + z := by linarith
  have hv : 0 ≤ v := div_nonneg (mul_nonneg hL hep.le) hn.le
  have hrl := retention_mul_intrinsicDimensionLog_le hN hr hr1
  have hrz := mul_le_mul_of_nonneg_right hr1 hz
  have hze := le_mul_of_one_le_right hz he
  have hrs : r * (intrinsicDimensionLog N r + z) ≤ (2 + z) * dimensionLog N := by
    nlinarith
  have hroot : Real.sqrt (n * L * r * (intrinsicDimensionLog N r + z)) / n ≤
      Real.sqrt (2 + z) * Real.sqrt v := by
    apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) hn.le)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    calc
      _ = (L / n) * (r * (intrinsicDimensionLog N r + z)) := by
        rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ n * L * r * (intrinsicDimensionLog N r + z))]
        field_simp [hn.ne']
      _ ≤ (L / n) * ((2 + z) * dimensionLog N) :=
        mul_le_mul_of_nonneg_left hrs (div_nonneg hL hn.le)
      _ = (Real.sqrt (2 + z) * Real.sqrt v) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 2 + z), Real.sq_sqrt hv]
        dsimp [v]
        ring
  have hlin :
      4 * Real.sqrt v * (Real.sqrt v * intrinsicDimensionLog N r / dimensionLog N +
        z * Real.sqrt v / dimensionLog N) = 4 * L * (intrinsicDimensionLog N r + z) / n := by
    calc
      _ = 4 * (Real.sqrt v) ^ 2 * (intrinsicDimensionLog N r + z) / dimensionLog N := by ring
      _ = 4 * v * (intrinsicDimensionLog N r + z) / dimensionLog N := by rw [Real.sq_sqrt hv]
      _ = _ := by dsimp [v]; field_simp [hep.ne']
  unfold normalizedIntrinsicThreshold bernsteinThreshold
  calc
    _ = 2 * (Real.sqrt (n * L * r * (intrinsicDimensionLog N r + z)) / n) +
        4 * L * (intrinsicDimensionLog N r + z) / n := by ring
    _ ≤ 2 * (Real.sqrt (2 + z) * Real.sqrt v) +
        4 * L * (intrinsicDimensionLog N r + z) / n :=
      add_le_add (mul_le_mul_of_nonneg_left hroot (by norm_num)) le_rfl
    _ = _ := by rw [← hlin]; ring

/-- The original variance-compatibility condition forces every fixed-confidence
Bernstein threshold and its `N/Q` multiple to vanish. No positive uniform
lower bound on retention, dimension, or leverage is required. -/
theorem variance_compatibility_bernstein_threshold_limits {J : Type*} {l : Filter J}
    (L n N Q r : J → ℝ) (A : ℝ)
    (hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < n i ∧ 0 ≤ N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ Q i ≤ A ^ 2 * r i * N i)
    (hcompat : Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0)) :
    ∀ z : ℝ, 0 ≤ z →
      Tendsto (fun i => normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z) l (𝓝 0) ∧
      Tendsto (fun i => N i / Q i * normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z) l (𝓝 0) := by
  let v := fun i => L i * dimensionLog (N i) / n i
  have hvgood : ∀ᶠ i in l, 0 ≤ v i ∧ 0 ≤ N i ∧ 0 < Q i ∧ 0 < r i ∧ r i ≤ 1 ∧
      Q i ≤ A ^ 2 * r i * N i := by
    filter_upwards [hgood] with i hi
    rcases hi with ⟨hL, hn, hN, hQ, hr, hr1, hcomp⟩
    have he := one_le_dimensionLog hN
    exact ⟨div_nonneg (mul_nonneg hL (by linarith)) hn.le, hN, hQ, hr, hr1, hcomp⟩
  obtain ⟨hv, _, hint⟩ := variance_compatibility_scale_limits v N Q r A hvgood hcompat
  have hsqrt : Tendsto (fun i => Real.sqrt (v i)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hv
  have hdiv : Tendsto (fun i => Real.sqrt (v i) / dimensionLog (N i)) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrt
    · filter_upwards [hgood] with i hi
      exact div_nonneg (Real.sqrt_nonneg _) (by linarith [one_le_dimensionLog hi.2.2.1])
    · filter_upwards [hgood] with i hi
      have he := one_le_dimensionLog hi.2.2.1
      apply (div_le_iff₀ (by linarith : 0 < dimensionLog (N i))).mpr
      exact le_mul_of_one_le_right (Real.sqrt_nonneg _) he
  intro z hz
  let F := fun i => Real.sqrt (v i) * intrinsicDimensionLog (N i) (r i) / dimensionLog (N i) +
    z * Real.sqrt (v i) / dimensionLog (N i)
  have hF : Tendsto F l (𝓝 0) := by
    simpa only [F, mul_div_assoc, zero_add, mul_zero] using hint.add (tendsto_const_nhds.mul hdiv)
  have hu : Tendsto (fun i => 2 * Real.sqrt (2 + z) * Real.sqrt (v i) +
      4 * Real.sqrt (v i) * F i) l (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_const_nhds.mul hsqrt).add ((tendsto_const_nhds.mul hsqrt).mul hF)
  have hwu : Tendsto (fun i => 2 * Real.sqrt (2 + z) * (N i / Q i * Real.sqrt (v i)) +
      4 * (N i / Q i * Real.sqrt (v i)) * F i) l (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_const_nhds.mul hcompat).add ((tendsto_const_nhds.mul hcompat).mul hF)
  have hTnonneg : ∀ᶠ i in l, 0 ≤ normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z := by
    filter_upwards [hgood] with i hi
    exact normalizedIntrinsicThreshold_nonneg hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.2.1 hz
  have hTb : ∀ᶠ i in l, normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z ≤
      2 * Real.sqrt (2 + z) * Real.sqrt (v i) + 4 * Real.sqrt (v i) * F i := by
    filter_upwards [hgood] with i hi
    exact normalizedIntrinsicThreshold_le hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2.1 hz
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu hTnonneg hTb
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwu
    · filter_upwards [hgood, hTnonneg] with i hi hTi
      exact mul_nonneg (div_nonneg hi.2.2.1 hi.2.2.2.1.le) hTi
    · filter_upwards [hgood, hTb] with i hi hTi
      have hm := mul_le_mul_of_nonneg_left hTi (div_nonneg hi.2.2.1 hi.2.2.2.1.le)
      convert hm using 1
      ring

/-- The same original compatibility also supplies the actual HS second-moment
scale used by variance transfer; this is a consequence, not a new scale input. -/
theorem variance_compatibility_hs_moment_scale_limit {J : Type*} {l : Filter J}
    (L n N Q r : J → ℝ) (A : ℝ)
    (hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < n i ∧ 0 ≤ N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ Q i ≤ A ^ 2 * r i * N i)
    (hcompat : Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0)) :
    Tendsto (fun i => L i * N i / (n i * Q i)) l (𝓝 0) := by
  let v := fun i => L i * dimensionLog (N i) / n i
  have hupper : Tendsto (fun i => A ^ 2 * (N i / Q i * Real.sqrt (v i))) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hcompat
  have hsqrt : Tendsto (fun i => Real.sqrt (v i)) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
    filter_upwards [hgood] with i hi
    rcases hi with ⟨_, _, _, hQ, hr, hr1, hcomp⟩
    exact (variance_compatibility_sqrt_bounds hQ hr hr1 hcomp).1
  have hp : Tendsto (fun i => (N i / Q i * Real.sqrt (v i)) * Real.sqrt (v i)) l (𝓝 0) := by
    simpa only [mul_zero] using hcompat.mul hsqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
  · filter_upwards [hgood] with i hi
    exact div_nonneg (mul_nonneg hi.1 hi.2.2.1) (mul_nonneg hi.2.1.le hi.2.2.2.1.le)
  · filter_upwards [hgood] with i hi
    rcases hi with ⟨hL, hn, hN, hQ, _, _, _⟩
    have he := one_le_dimensionLog hN
    have hv : 0 ≤ v i := div_nonneg (mul_nonneg hL (by linarith)) hn.le
    have hm : 0 ≤ L i * N i / (n i * Q i) := div_nonneg (mul_nonneg hL hN) (by positivity)
    refine (le_mul_of_one_le_right hm he).trans_eq ?_
    rw [mul_assoc, ← pow_two, Real.sq_sqrt hv]
    dsimp [v]
    field_simp [hn.ne', hQ.ne']

/-- Visible exponential Bernstein tails at the true thresholds imply the two
covariance error limits needed for variance transfer. This assumes a tail
inequality, not either limiting rate. Its actual operator proof is separate. -/
theorem variance_compatibility_covariance_limits_of_threshold_tails
    {J Ω : Type*} [MeasurableSpace Ω] {l : Filter J} (P : Measure Ω)
    (δ : J → Ω → ℝ) (L n N Q r : J → ℝ) (A : ℝ)
    (hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < n i ∧ 0 ≤ N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ Q i ≤ A ^ 2 * r i * N i)
    (hcompat : Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0))
    (htail : ∀ z : ℝ, 0 ≤ z → ∀ᶠ i in l,
      P {ω | normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z < |δ i ω|} ≤
        ENNReal.ofReal (8 * Real.exp (-z))) :
    TendstoInMeasure P δ l (fun _ => 0) ∧
      TendstoInMeasure P (fun i ω => δ i ω * N i / Q i) l (fun _ => 0) := by
  have hlimits := variance_compatibility_bernstein_threshold_limits L n N Q r A hgood hcompat
  constructor
  · apply tendstoInMeasure_zero_of_exponential_thresholds P δ
      (fun z i => normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z)
      (fun z hz => (hlimits z hz).1)
    intro z hz
    simpa only [Real.norm_eq_abs] using htail z hz
  · apply tendstoInMeasure_zero_of_exponential_thresholds P (fun i ω => δ i ω * N i / Q i)
      (fun z i => N i / Q i * normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z)
      (fun z hz => (hlimits z hz).2)
    intro z hz
    filter_upwards [hgood, htail z hz] with i hi hti
    rcases hi with ⟨_, _, hN, hQ, _, _, hcomp⟩
    have hNpos : 0 < N i := by
      by_contra hnot
      have hzN : N i = 0 := le_antisymm (not_lt.mp hnot) hN
      rw [hzN, mul_zero] at hcomp
      linarith
    have hfac : 0 < N i / Q i := div_pos hNpos hQ
    refine (measure_mono ?_).trans hti
    intro ω hω
    change N i / Q i * normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z <
      ‖δ i ω * N i / Q i‖ at hω
    have hid : ‖δ i ω * N i / Q i‖ = (N i / Q i) * |δ i ω| := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hN, abs_of_pos hQ]
      ring
    rw [hid] at hω
    exact (mul_lt_mul_iff_of_pos_left hfac).mp hω

end KernelSeq
