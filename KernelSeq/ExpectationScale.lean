import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The original logarithmic scale controls exponential bad-event envelopes

The only limiting scale is r log(e + H) → 0, with r = L/n and H = n/(λQ).
The reciprocal divergence needed for the exponential estimate is derived,
rather than assumed. These are genuine scalar limits and deterministic
envelope inequalities, not tail or risk-comparison certificates.
-/

open Filter Topology

namespace KernelSeq
noncomputable section

variable {J : Type*} {l : Filter J}

/-- The logarithmic expectation scale itself forces L/n to vanish. -/
theorem expectation_log_scale_tendsto_zero (r H : J → ℝ)
    (hr : ∀ᶠ i in l, 0 ≤ r i) (hH : ∀ᶠ i in l, 0 ≤ H i)
    (hscale : Tendsto (fun i => r i * Real.log (Real.exp 1 + H i)) l (𝓝 0)) :
    Tendsto r l (𝓝 0) := by
  apply squeeze_zero' hr _ hscale
  filter_upwards [hr, hH] with i hri hHi
  have hlog : 1 ≤ Real.log (Real.exp 1 + H i) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (le_add_of_nonneg_right hHi)
  nlinarith

/-- Every fixed nonnegative polynomial power is negligible against the
true exponential tail under the original logarithmic expectation scale. -/
theorem expectation_log_scale_rpow_mul_exp_tendsto_zero (r H : J → ℝ)
    (hr : ∀ᶠ i in l, 0 < r i) (hH : ∀ᶠ i in l, 0 ≤ H i)
    (hscale : Tendsto (fun i => r i * Real.log (Real.exp 1 + H i)) l (𝓝 0))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    Tendsto (fun i => (1 + H i) ^ a * Real.exp (-c / r i)) l (𝓝 0) := by
  have hr0 := expectation_log_scale_tendsto_zero r H (hr.mono fun _ hi => hi.le) hH hscale
  have hrGT : Tendsto r l (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hr0, hr⟩
  have htop := hrGT.inv_tendsto_nhdsGT_zero
  have htop' : Tendsto (fun i => (c / 2) * (r i)⁻¹) l atTop :=
    htop.const_mul_atTop (by positivity)
  have htail : Tendsto (fun i => Real.exp (-((c / 2) * (r i)⁻¹))) l (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp htop'
  have hasmall : ∀ᶠ i in l, a * (r i * Real.log (Real.exp 1 + H i)) < c / 2 := by
    have ht := hscale.const_mul a
    simp only [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < c / 2))
  apply squeeze_zero' _ _ htail
  · filter_upwards [hH] with i hHi
    exact mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + H i) a) (Real.exp_pos _).le
  · filter_upwards [hr, hH, hasmall] with i hri hHi hsmall
    have hbase : 0 < 1 + H i := by linarith
    have hlogle : Real.log (1 + H i) ≤ Real.log (Real.exp 1 + H i) :=
      Real.log_le_log hbase (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have hlogbound : a * Real.log (1 + H i) * r i ≤ c / 2 := by
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogle ha) hri.le
      nlinarith
    rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    apply (mul_le_mul_iff_right₀ hri).mp
    field_simp [hri.ne']
    nlinarith

/-- The original sample/leverage notation has exactly the preceding
scalar rate; no extra reciprocal-divergence premise is introduced. -/
theorem expectation_scale_polynomial_tail (L n H : J → ℝ)
    (hL : ∀ᶠ i in l, 0 < L i) (hn : ∀ᶠ i in l, 0 < n i)
    (hH : ∀ᶠ i in l, 0 ≤ H i)
    (hscale : Tendsto (fun i => L i / n i * Real.log (Real.exp 1 + H i)) l (𝓝 0))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    Tendsto (fun i => (1 + H i) ^ a * Real.exp (-c * n i / L i)) l (𝓝 0) := by
  have h := expectation_log_scale_rpow_mul_exp_tendsto_zero (fun i => L i / n i) H
    (by filter_upwards [hL, hn] with i hiL hin; positivity) hH hscale ha hc
  apply h.congr'
  filter_upwards [hL, hn] with i hiL hin
  congr 2
  field_simp

/-- A fixed real exponent, including a negative one, is harmless. -/
theorem expectation_scale_real_power_tail (L n H : J → ℝ)
    (hL : ∀ᶠ i in l, 0 < L i) (hn : ∀ᶠ i in l, 0 < n i)
    (hH : ∀ᶠ i in l, 0 ≤ H i)
    (hscale : Tendsto (fun i => L i / n i * Real.log (Real.exp 1 + H i)) l (𝓝 0))
    (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i => (1 + H i) ^ a * Real.exp (-c * n i / L i)) l (𝓝 0) := by
  apply squeeze_zero' _ _ (expectation_scale_polynomial_tail L n H hL hn hH hscale
    (show 0 ≤ max a 0 from le_max_right _ _) hc)
  · filter_upwards [hH] with i hi
    positivity
  · filter_upwards [hH] with i hi
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1 + H i) (le_max_left _ _))
      (Real.exp_pos _).le

/-- A fixed multiple of leverage bounds the filter dimension divided by
sample size under L/n→0. -/
theorem filterDimension_div_sample_tendsto_zero_of_le (Q L n : J → ℝ) {C : ℝ}
    (_hC : 0 ≤ C) (hQ : ∀ᶠ i in l, 0 ≤ Q i) (hn : ∀ᶠ i in l, 0 < n i)
    (hQL : ∀ᶠ i in l, Q i ≤ C * L i)
    (hLn : Tendsto (fun i => L i / n i) l (𝓝 0)) :
    Tendsto (fun i => Q i / n i) l (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa only [mul_zero] using hLn.const_mul C)
  · filter_upwards [hQ, hn] with i hiQ hin
    exact div_nonneg hiQ hin.le
  · filter_upwards [hQL, hn] with i hiQL hin
    exact (div_le_div_of_nonneg_right hiQL hin.le).trans_eq (by ring)

/-- Thus Q≤n eventually; this is derived rather than added as a new rate. -/
theorem eventually_filterDimension_le_sample_of_le (Q L n : J → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hQ : ∀ᶠ i in l, 0 ≤ Q i) (hn : ∀ᶠ i in l, 0 < n i)
    (hQL : ∀ᶠ i in l, Q i ≤ C * L i)
    (hLn : Tendsto (fun i => L i / n i) l (𝓝 0)) :
    ∀ᶠ i in l, Q i ≤ n i := by
  have ht := filterDimension_div_sample_tendsto_zero_of_le Q L n hC hQ hn hQL hLn
  have he := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [he, hn] with i hi hin
  exact ((div_lt_one hin).mp hi).le

/-- The actual polynomial reciprocal factor is bounded by H whenever
Q≤n. No regularization bound is needed for this inequality. -/
theorem regularization_inv_le_expectation_H {n lam Q : ℝ}
    (_hn : 0 < n) (hlam : 0 < lam) (hQ : 0 < Q) (hQn : Q ≤ n) :
    lam⁻¹ ≤ n / (lam * Q) := by
  rw [← one_div]
  apply (div_le_div_iff₀ hlam (mul_pos hlam hQ)).mpr
  nlinarith

/-- The fixed-target global risk envelope is a quadratic polynomial in H
when λ≤1 and Q≤n. The former follows from the prescribed λ→0 sequence. -/
theorem expectation_global_envelope_le_polynomial {n lam Q : ℝ}
    (hn : 0 < n) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hQ : 0 < Q) (hQn : Q ≤ n) :
    1 + n / Q + n / (lam ^ 2 * Q) ≤ (1 + n / (lam * Q)) ^ (2 : ℕ) := by
  have hfirst : n / Q ≤ n / (lam * Q) :=
    div_le_div_of_nonneg_left hn.le (mul_pos hlam hQ) (by nlinarith)
  have hsecond : n / (lam ^ 2 * Q) ≤ (n / (lam * Q)) ^ (2 : ℕ) := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hlam) hQ)).mpr
    have hm := mul_le_mul_of_nonneg_left hQn hn.le
    field_simp [hlam.ne', hQ.ne']
    nlinarith
  have hH : 0 ≤ n / (lam * Q) := by positivity
  nlinarith

/-- The original additional expectation condition kills the complete
fixed-target global bad-risk envelope. Only λ→0 from the prescribed
sequence is used to control λ; no new rate on λ is imposed. -/
theorem expectation_scale_global_envelope_tail (L n lam Q : J → ℝ)
    (hL : ∀ᶠ i in l, 0 < L i) (hn : ∀ᶠ i in l, 0 < n i)
    (hlam : ∀ᶠ i in l, 0 < lam i) (hQ : ∀ᶠ i in l, 0 < Q i)
    (hQn : ∀ᶠ i in l, Q i ≤ n i) (hlam0 : Tendsto lam l (𝓝 0))
    (hscale : Tendsto (fun i => L i / n i *
      Real.log (Real.exp 1 + n i / (lam i * Q i))) l (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i => (1 + n i / Q i + n i / (lam i ^ 2 * Q i)) *
      Real.exp (-c * n i / L i)) l (𝓝 0) := by
  have hH : ∀ᶠ i in l, 0 ≤ n i / (lam i * Q i) := by
    filter_upwards [hn, hlam, hQ] with i hin hil hiQ
    positivity
  have ht := expectation_scale_polynomial_tail L n (fun i => n i / (lam i * Q i))
    hL hn hH hscale (show 0 ≤ (2 : ℝ) by norm_num) hc
  simp only [Real.rpow_two] at ht
  have hl1 := hlam0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  apply squeeze_zero' _ _ ht
  · filter_upwards [hn, hlam, hQ] with i hin hil hiQ
    positivity
  · filter_upwards [hn, hlam, hQ, hQn, hl1] with i hin hil hiQ hiQn hil1
    exact mul_le_mul_of_nonneg_right
      (expectation_global_envelope_le_polynomial hin hil hil1.le hiQ hiQn) (Real.exp_pos _).le

/-- A true bound on λ²Q controls n/Q without any bound on λ. -/
theorem sample_div_filterDimension_le_expectation_H_sq {n lam Q B : ℝ}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hsquare : lam ^ 2 * Q ≤ B) :
    n / Q ≤ B * (n / (lam * Q)) ^ (2 : ℕ) := by
  have hn0 : 0 < n := by linarith
  have hBn : lam ^ 2 * Q ≤ B * n :=
    hsquare.trans (by nlinarith [mul_nonneg hB (show 0 ≤ n - 1 by linarith)])
  have hm := mul_le_mul_of_nonneg_left hBn hn0.le
  apply (mul_le_mul_iff_right₀ (mul_pos (sq_pos_of_pos hlam) (sq_pos_of_pos hQ))).mp
  field_simp [hlam.ne', hQ.ne']
  nlinarith

/-- The complete fixed-target global envelope is controlled by H² from
the actual λ²Q bound, with no extra regularization limit or boundedness. -/
theorem expectation_global_envelope_le_of_square_bound {n lam Q B : ℝ}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hQ : 0 < Q) (hQn : Q ≤ n)
    (hB : 0 ≤ B) (hsquare : lam ^ 2 * Q ≤ B) :
    1 + n / Q + n / (lam ^ 2 * Q) ≤ (B + 2) * (1 + n / (lam * Q)) ^ (2 : ℕ) := by
  have hn0 : 0 < n := by linarith
  have hfirst := sample_div_filterDimension_le_expectation_H_sq hn hlam hQ hB hsquare
  have hsecond : n / (lam ^ 2 * Q) ≤ (n / (lam * Q)) ^ (2 : ℕ) := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hlam) hQ)).mpr
    have hm := mul_le_mul_of_nonneg_left hQn hn0.le
    field_simp [hlam.ne', hQ.ne']
    nlinarith
  have hH : 0 ≤ n / (lam * Q) := by positivity
  calc
    _ ≤ 1 + B * (n / (lam * Q)) ^ 2 + (n / (lam * Q)) ^ 2 := by linarith
    _ ≤ (B + 2) * (1 + (n / (lam * Q)) ^ 2) := by
      nlinarith [sq_nonneg (n / (lam * Q))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith : 0 ≤ B + 2)

/-- The exact additional expectation scale kills the fixed-target global
envelope using the proved population dimension bound λ²Q≤B. -/
theorem expectation_scale_global_envelope_tail_of_square_bound (L n lam Q : J → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hL : ∀ᶠ i in l, 0 < L i)
    (hn : ∀ᶠ i in l, 1 ≤ n i) (hlam : ∀ᶠ i in l, 0 < lam i)
    (hQ : ∀ᶠ i in l, 0 < Q i) (hQn : ∀ᶠ i in l, Q i ≤ n i)
    (hsquare : ∀ᶠ i in l, lam i ^ 2 * Q i ≤ B)
    (hscale : Tendsto (fun i => L i / n i *
      Real.log (Real.exp 1 + n i / (lam i * Q i))) l (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i => (1 + n i / Q i + n i / (lam i ^ 2 * Q i)) *
      Real.exp (-c * n i / L i)) l (𝓝 0) := by
  have hn0 : ∀ᶠ i in l, 0 < n i := hn.mono fun _ hi => by linarith
  have hH : ∀ᶠ i in l, 0 ≤ n i / (lam i * Q i) := by
    filter_upwards [hn0, hlam, hQ] with i hin hil hiQ
    positivity
  have ht := (expectation_scale_polynomial_tail L n (fun i => n i / (lam i * Q i))
    hL hn0 hH hscale (show 0 ≤ (2 : ℝ) by norm_num) hc).const_mul (B + 2)
  simp only [Real.rpow_two, mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [hn0, hlam, hQ] with i hin hil hiQ
    positivity
  · filter_upwards [hn, hlam, hQ, hQn, hsquare] with i hin hil hiQ hiQn hisq
    exact (mul_le_mul_of_nonneg_right
      (expectation_global_envelope_le_of_square_bound hin hil hiQ hiQn hB hisq)
      (Real.exp_pos _).le).trans_eq (by ring)

/-- The polynomial reciprocal form appearing in the manuscript is also
killed by the original logarithmic scale, without a bound on λ itself. -/
theorem expectation_scale_reciprocal_envelope_tail (L n lam Q : J → ℝ)
    (hL : ∀ᶠ i in l, 0 < L i) (hn : ∀ᶠ i in l, 0 < n i)
    (hlam : ∀ᶠ i in l, 0 < lam i) (hQ : ∀ᶠ i in l, 0 < Q i)
    (hQn : ∀ᶠ i in l, Q i ≤ n i)
    (hscale : Tendsto (fun i => L i / n i *
      Real.log (Real.exp 1 + n i / (lam i * Q i))) l (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i => (1 + n i / (lam i * Q i) + (lam i)⁻¹) *
      Real.exp (-c * n i / L i)) l (𝓝 0) := by
  have hH : ∀ᶠ i in l, 0 ≤ n i / (lam i * Q i) := by
    filter_upwards [hn, hlam, hQ] with i hin hil hiQ
    positivity
  have ht := (expectation_scale_polynomial_tail L n (fun i => n i / (lam i * Q i))
    hL hn hH hscale (show 0 ≤ (1 : ℝ) by norm_num) hc).const_mul 2
  simp only [Real.rpow_one, mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [hn, hlam, hQ] with i hin hil hiQ
    positivity
  · filter_upwards [hn, hlam, hQ, hQn] with i hin hil hiQ hiQn
    have hlin : 1 + n i / (lam i * Q i) + (lam i)⁻¹ ≤ 2 * (1 + n i / (lam i * Q i)) := by
      have hi := regularization_inv_le_expectation_H hin hil hiQ hiQn
      linarith
    exact (mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le).trans_eq (by ring)

end
end KernelSeq
