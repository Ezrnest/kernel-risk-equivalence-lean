import KernelSeq.GradientFlowFilter
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Stable gradient descent, including real iteration times

The iteration time is the actual `(eta * lam)⁻¹`. The positive real branch is
used on the original stable spectral interval; no integrality assumption is
imposed. `eta * lam ≤ 1` is the manuscript's sufficiently small regularization
regime. Constants depend only on the fixed stability margin.
-/

namespace KernelSeq.ResidualFilter

open MeasureTheory Set
noncomputable section

def gradientDescentIterations (eta lam : ℝ) : ℝ := (eta * lam)⁻¹

def stableGradientDescent (eta lam t : ℝ) : ℝ :=
  if t = 0 then lam⁻¹ else
    (1 - (1 - eta * t) ^ gradientDescentIterations eta lam) / t

theorem gradientDescentIterations_pos {eta lam : ℝ} (heta : 0 < eta) (hlam : 0 < lam) :
    0 < gradientDescentIterations eta lam := by unfold gradientDescentIterations; positivity

theorem gradientDescentIterations_ge_one {eta lam : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hsmall : eta * lam ≤ 1) :
    1 ≤ gradientDescentIterations eta lam := by
  unfold gradientDescentIterations
  exact (one_le_inv₀ (mul_pos heta hlam)).2 hsmall

theorem gradientDescentIterations_mul_step {eta lam : ℝ} (heta : 0 < eta) (hlam : 0 < lam) :
    gradientDescentIterations eta lam * eta = lam⁻¹ := by
  unfold gradientDescentIterations
  field_simp

theorem stableGradientDescent_zero (eta lam : ℝ) : stableGradientDescent eta lam 0 = lam⁻¹ := by
  simp [stableGradientDescent]

theorem stableGradientDescent_shrinkage (eta lam t : ℝ) :
    shrinkage (stableGradientDescent eta lam) t =
      1 - (1 - eta * t) ^ gradientDescentIterations eta lam := by
  by_cases ht : t = 0
  · subst t
    simp [shrinkage]
  · unfold shrinkage stableGradientDescent
    rw [if_neg ht]
    field_simp

theorem stableGradientDescent_residual (eta lam t : ℝ) :
    residual (stableGradientDescent eta lam) t =
      (1 - eta * t) ^ gradientDescentIterations eta lam := by
  rw [residual, stableGradientDescent_shrinkage]
  ring

private theorem stable_base_pos {eta M margin t : ℝ} (heta : 0 < eta)
    (hmargin : margin < 1) (hstable : eta * M ≤ margin) (ht : t ∈ Icc (0 : ℝ) M) :
    0 < 1 - eta * t := by
  have h := mul_le_mul_of_nonneg_left ht.2 heta.le
  linarith

theorem stableGradientDescent_spectralFilter {eta lam M margin : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hmargin : margin < 1) (hstable : eta * M ≤ margin) :
    SpectralFilter M (stableGradientDescent eta lam) := by
  have hc : Continuous (fun t : Icc (0 : ℝ) M =>
      (1 - eta * (t : ℝ)) ^ gradientDescentIterations eta lam) := by
    apply (continuous_const.sub (continuous_const.mul continuous_subtype_val)).rpow_const
    intro t
    exact Or.inl (ne_of_gt (stable_base_pos heta hmargin hstable t.property))
  have hm := gradientDescentIterations_pos heta hlam
  constructor
  · apply Measurable.ite ((measurableSet_singleton (0 : ℝ)).preimage measurable_subtype_coe)
      measurable_const
    exact (continuous_const.sub hc).measurable.div measurable_subtype_coe
  · intro t ht
    by_cases ht0 : t = 0
    · simp [stableGradientDescent, ht0, hlam.le]
    · rw [stableGradientDescent, if_neg ht0]
      exact div_nonneg (sub_nonneg.mpr (Real.rpow_le_one
        (stable_base_pos heta hmargin hstable ht).le
        (by nlinarith [ht.1]) hm.le)) ht.1
  · intro t ht
    rw [stableGradientDescent_shrinkage]
    have hb := stable_base_pos heta hmargin hstable ht
    have hp0 := Real.rpow_nonneg hb.le (gradientDescentIterations eta lam)
    have hp1 := Real.rpow_le_one hb.le (by nlinarith [ht.1]) hm.le
    constructor <;> linarith

theorem stableGradientDescent_inverse_size {eta lam M margin t : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hsmall : eta * lam ≤ 1)
    (hmargin : margin < 1) (hstable : eta * M ≤ margin) (ht : t ∈ Icc (0 : ℝ) M) :
    (t + lam) * stableGradientDescent eta lam t ≤ 2 := by
  have hb := stable_base_pos heta hmargin hstable ht
  have hm := gradientDescentIterations_ge_one heta hlam hsmall
  have hme := gradientDescentIterations_mul_step heta hlam
  by_cases ht0 : t = 0
  · subst t
    simp [stableGradientDescent, hlam.ne']
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [stableGradientDescent, if_neg ht0]
    by_cases htl : t ≤ lam
    · have hber := one_add_mul_self_le_rpow_one_add (s := -(eta * t)) (by linarith) hm
      have hlin : 1 - (1 - eta * t) ^ gradientDescentIterations eta lam ≤ t / lam := by
        have hid : gradientDescentIterations eta lam * (-(eta * t)) = -(t / lam) := by
          rw [show gradientDescentIterations eta lam * (-(eta * t)) =
            -(gradientDescentIterations eta lam * eta * t) by ring, hme]
          ring
        rw [hid, show 1 + -(eta * t) = 1 - eta * t by ring] at hber
        linarith
      have hg : (1 - (1 - eta * t) ^ gradientDescentIterations eta lam) / t ≤ 1 / lam := by
        apply (div_le_iff₀ htp).2
        simpa only [div_eq_mul_inv, one_div, mul_one, mul_comm] using hlin
      calc
        _ ≤ (t + lam) * (1 / lam) := mul_le_mul_of_nonneg_left hg (by linarith [ht.1])
        _ ≤ 2 := by rw [mul_one_div]; apply (div_le_iff₀ hlam).2; linarith
    · have hg : (1 - (1 - eta * t) ^ gradientDescentIterations eta lam) / t ≤ 1 / t :=
        div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg hb.le (gradientDescentIterations eta lam)]) ht.1
      calc
        _ ≤ (t + lam) * (1 / t) := mul_le_mul_of_nonneg_left hg (by linarith [ht.1])
        _ ≤ 2 := by rw [mul_one_div]; apply (div_le_iff₀ htp).2; linarith

theorem stableGradientDescent_residual_le_exp {eta lam M margin t : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hmargin : margin < 1)
    (hstable : eta * M ≤ margin) (ht : t ∈ Icc (0 : ℝ) M) :
    residual (stableGradientDescent eta lam) t ≤ Real.exp (-t / lam) := by
  have hb := stable_base_pos heta hmargin hstable ht
  have hm := gradientDescentIterations_pos heta hlam
  have hlog := Real.log_le_sub_one_of_pos hb
  have he : Real.log (1 - eta * t) * gradientDescentIterations eta lam ≤ -t / lam := by
    have h := mul_le_mul_of_nonneg_right hlog hm.le
    have hid : ((1 - eta * t) - 1) * gradientDescentIterations eta lam = -t / lam := by
      have hme := gradientDescentIterations_mul_step heta hlam
      calc
        _ = -(gradientDescentIterations eta lam * eta * t) := by ring
        _ = _ := by rw [hme]; ring
    exact h.trans_eq hid
  rw [stableGradientDescent_residual, Real.rpow_def_of_pos hb]
  exact Real.exp_le_exp.mpr he

theorem stableGradientDescent_residual_contDiffOn {eta lam M margin : ℝ}
    (heta : 0 < eta) (hM : 0 ≤ M) (hmargin : margin < 1) (hstable : eta * M ≤ margin) :
    ContDiffOn ℝ 1 (residual (stableGradientDescent eta lam)) (uIcc 0 M) := by
  have heq : residual (stableGradientDescent eta lam) =
      fun t => (1 - eta * t) ^ gradientDescentIterations eta lam :=
    funext (stableGradientDescent_residual eta lam)
  rw [heq]
  apply ContDiffOn.rpow_const_of_ne
  · exact contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id)
  · intro t ht
    exact ne_of_gt (stable_base_pos heta hmargin hstable (uIcc_of_le hM ▸ ht))

theorem stableGradientDescent_residual_deriv {eta lam M margin t : ℝ}
    (heta : 0 < eta) (hmargin : margin < 1) (hstable : eta * M ≤ margin)
    (ht : t ∈ Icc (0 : ℝ) M) :
    deriv (residual (stableGradientDescent eta lam)) t =
      -eta * gradientDescentIterations eta lam *
        (1 - eta * t) ^ (gradientDescentIterations eta lam - 1) := by
  have heq : residual (stableGradientDescent eta lam) =
      fun t => (1 - eta * t) ^ gradientDescentIterations eta lam :=
    funext (stableGradientDescent_residual eta lam)
  rw [heq]
  have hd := (((hasDerivAt_id t).const_mul eta).const_sub 1).rpow_const
    (p := gradientDescentIterations eta lam)
    (Or.inl (ne_of_gt (stable_base_pos heta hmargin hstable ht)))
  simpa only [id_eq, mul_one, neg_mul] using hd.deriv

theorem stableGradientDescent_abs_deriv_eq {eta lam M margin t : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hmargin : margin < 1)
    (hstable : eta * M ≤ margin) (ht : t ∈ Icc (0 : ℝ) M) :
    |deriv (residual (stableGradientDescent eta lam)) t| =
      residual (stableGradientDescent eta lam) t / (lam * (1 - eta * t)) := by
  have hb := stable_base_pos heta hmargin hstable ht
  have hm := gradientDescentIterations_pos heta hlam
  have hme := gradientDescentIterations_mul_step heta hlam
  rw [stableGradientDescent_residual_deriv heta hmargin hstable ht, Real.rpow_sub_one hb.ne']
  rw [show -eta * gradientDescentIterations eta lam *
      ((1 - eta * t) ^ gradientDescentIterations eta lam / (1 - eta * t)) =
      -(eta * gradientDescentIterations eta lam *
        ((1 - eta * t) ^ gradientDescentIterations eta lam / (1 - eta * t))) by ring,
    abs_neg, abs_of_nonneg (by positivity)]
  rw [stableGradientDescent_residual,
    show eta * gradientDescentIterations eta lam = lam⁻¹ by simpa [mul_comm] using hme]
  field_simp

theorem stableGradientDescent_abs_deriv_le_exp {eta lam M margin t : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hmargin : margin < 1)
    (hstable : eta * M ≤ margin) (ht : t ∈ Icc (0 : ℝ) M) :
    |deriv (residual (stableGradientDescent eta lam)) t| ≤
      (1 - margin)⁻¹ * Real.exp (-t / lam) / lam := by
  have hb := stable_base_pos heta hmargin hstable ht
  have hd : 0 < 1 - margin := by linarith
  have hbase : 1 - margin ≤ 1 - eta * t := by
    have h := mul_le_mul_of_nonneg_left ht.2 heta.le
    linarith
  rw [stableGradientDescent_abs_deriv_eq heta hlam hmargin hstable ht]
  calc
    _ ≤ Real.exp (-t / lam) / (lam * (1 - eta * t)) :=
      div_le_div_of_nonneg_right (stableGradientDescent_residual_le_exp heta hlam hmargin hstable ht)
        (mul_pos hlam hb).le
    _ ≤ Real.exp (-t / lam) / (lam * (1 - margin)) := by
      apply (div_le_div_iff₀ (mul_pos hlam hb) (mul_pos hlam hd)).2
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hlam.le) (Real.exp_pos _).le
    _ = _ := by field_simp

def stableGradientDescentSmoothConstant (margin : ℝ) : ℝ := 4 / (1 - margin)

theorem stableGradientDescent_combined_bound {eta lam M margin t : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hmargin : margin < 1)
    (hstable : eta * M ≤ margin) (ht : t ∈ Icc (0 : ℝ) M) :
    |residual (stableGradientDescent eta lam) t| +
      (t + lam) * |deriv (residual (stableGradientDescent eta lam)) t| ≤
        stableGradientDescentSmoothConstant margin * (lam / (t + lam)) ^ (1 : ℝ) := by
  have hmargin0 : 0 ≤ margin :=
    (mul_nonneg heta.le (ht.1.trans ht.2)).trans hstable
  have hd : 0 < 1 - margin := by linarith
  have hc : 1 ≤ (1 - margin)⁻¹ := (one_le_inv₀ hd).2 (by linarith)
  have hc0 : 0 ≤ (1 - margin)⁻¹ := inv_nonneg.mpr hd.le
  have hb := stable_base_pos heta hmargin hstable ht
  have hr0 : 0 ≤ residual (stableGradientDescent eta lam) t := by
    rw [stableGradientDescent_residual]
    exact Real.rpow_nonneg hb.le _
  rw [abs_of_nonneg hr0, Real.rpow_one]
  have hpsi := stableGradientDescent_residual_le_exp heta hlam hmargin hstable ht
  have hpsi' := hpsi.trans (le_mul_of_one_le_left (Real.exp_pos _).le hc)
  have hder := stableGradientDescent_abs_deriv_le_exp heta hlam hmargin hstable ht
  have hgf := gradientFlow_combined_bound hlam ht.1
  rw [gradientFlow_residual, gradientFlow_residual_deriv, Real.rpow_one,
    abs_of_pos (Real.exp_pos _), abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos hlam] at hgf
  calc
    _ ≤ (1 - margin)⁻¹ * Real.exp (-t / lam) +
        (t + lam) * ((1 - margin)⁻¹ * Real.exp (-t / lam) / lam) :=
      add_le_add hpsi' (mul_le_mul_of_nonneg_left hder (by linarith [ht.1]))
    _ = (1 - margin)⁻¹ *
        (Real.exp (-t / lam) + (t + lam) * (Real.exp (-t / lam) / lam)) := by ring
    _ ≤ (1 - margin)⁻¹ * (4 * (lam / (t + lam))) := mul_le_mul_of_nonneg_left hgf hc0
    _ = _ := by unfold stableGradientDescentSmoothConstant; ring

/-- Stable gradient descent at the actual real iteration time satisfies the
original contract, with a constant depending only on the stability margin. -/
theorem stableGradientDescent_contract {eta lam M margin : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hM : 0 ≤ M) (hsmall : eta * lam ≤ 1)
    (hmargin : margin < 1) (hstable : eta * M ≤ margin) :
    Contract lam M 1 (8 / (1 - margin)) (stableGradientDescent eta lam) := by
  have hmargin0 : 0 ≤ margin := (mul_nonneg heta.le hM).trans hstable
  have hd : 0 < 1 - margin := by linarith
  have hB : 4 ≤ stableGradientDescentSmoothConstant margin := by
    unfold stableGradientDescentSmoothConstant
    apply (le_div_iff₀ hd).2
    linarith
  have hh := contract_of_smooth_condition_nonnegative_interval
    (B := stableGradientDescentSmoothConstant margin) hlam hM (by norm_num : (0 : ℝ) < 1)
    (stableGradientDescent_spectralFilter heta hlam hmargin hstable)
    (stableGradientDescent_residual_contDiffOn heta hM hmargin hstable).absolutelyContinuousOnInterval
    (fun t ht => (stableGradientDescent_inverse_size heta hlam hsmall hmargin hstable ht).trans
      (by linarith))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact stableGradientDescent_combined_bound heta hlam hmargin hstable ht)
  have heq : max (stableGradientDescentSmoothConstant margin) 1 * max 2 (1 : ℝ) =
      8 / (1 - margin) := by
    rw [max_eq_left (by linarith : 1 ≤ stableGradientDescentSmoothConstant margin)]
    norm_num [stableGradientDescentSmoothConstant]
    ring
  rwa [heq] at hh

theorem stableGradientDescent_contract_eventually {ι : Type*} {l : Filter ι}
    {eta M margin : ℝ} (heta : 0 < eta) (hM : 0 ≤ M)
    (hmargin : margin < 1) (hstable : eta * M ≤ margin)
    (lam : ι → ℝ) (hlam : ∀ᶠ i in l, 0 < lam i) (hlim : Filter.Tendsto lam l (nhds 0)) :
    ∀ᶠ i in l, Contract (lam i) M 1 (8 / (1 - margin)) (stableGradientDescent eta (lam i)) := by
  have hsmall : ∀ᶠ i in l, eta * lam i ≤ 1 := by
    have hlim' : Filter.Tendsto (fun i => eta * lam i) l (nhds 0) := by
      simpa only [mul_zero] using hlim.const_mul eta
    exact (hlim'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le
  filter_upwards [hlam, hsmall] with i hi hsi
  exact stableGradientDescent_contract heta hi hM hsi hmargin hstable

theorem stableGradientDescent_of_integer_iterations {eta lam t : ℝ} {ν : ℕ}
    (hν : gradientDescentIterations eta lam = (ν : ℝ)) (ht : t ≠ 0) :
    stableGradientDescent eta lam t = (1 - (1 - eta * t) ^ ν) / t := by
  simp [stableGradientDescent, ht, hν, Real.rpow_natCast]

end
end KernelSeq.ResidualFilter
