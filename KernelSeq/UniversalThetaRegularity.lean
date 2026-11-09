import KernelSeq.LogInteractionFactorization
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Scalar regularity of the universal interaction profile

The apparent singularity at zero is removed using the analytic divided slope of `exp`.
No smoothness or Fourier-multiplier certificate is assumed.
-/

namespace KernelSeq

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The everywhere positive analytic extension of `(exp z - 1) / z`. -/
def thetaDenominator (z : ℝ) : ℝ := dslope Real.exp 0 z

@[simp] theorem thetaDenominator_zero : thetaDenominator 0 = 1 := by
  simp [thetaDenominator, Real.deriv_exp]

theorem thetaDenominator_of_ne {z : ℝ} (hz : z ≠ 0) :
    thetaDenominator z = (Real.exp z - 1) / z := by
  simp [thetaDenominator, dslope_of_ne Real.exp hz, slope, div_eq_mul_inv, mul_comm]

theorem thetaDenominator_pos (z : ℝ) : 0 < thetaDenominator z := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · rw [thetaDenominator_of_ne (ne_of_lt hz)]
    exact div_pos_of_neg_of_neg (sub_neg.mpr (by simpa using Real.exp_lt_exp.mpr hz)) hz
  · simp
  · rw [thetaDenominator_of_ne (ne_of_gt hz)]
    exact div_pos (sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hz)) hz

theorem thetaDenominator_analyticAt (z : ℝ) : AnalyticAt ℝ thetaDenominator z := by
  by_cases hz : z = 0
  · subst z
    obtain ⟨p, hp⟩ := (analyticAt_rexp : AnalyticAt ℝ Real.exp 0)
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℝ (fun y : ℝ => (Real.exp y - 1) / y) z :=
      (analyticAt_rexp.sub analyticAt_const).div analyticAt_id hz
    apply hq.congr
    filter_upwards [eventually_ne_nhds hz] with y hy
    exact (thetaDenominator_of_ne hy).symm

/-- A formula for the actual manuscript profile with no division by zero. -/
theorem interactionTheta_eq_analytic_quotient (α z : ℝ) :
    interactionTheta α z = Real.exp ((1 - α / 2) * z) / thetaDenominator z := by
  by_cases hz : z = 0
  · subst z; simp [interactionTheta]
  · rw [interactionTheta, if_neg hz, thetaDenominator_of_ne hz]
    field_simp

theorem interactionTheta_analyticAt (α z : ℝ) :
    AnalyticAt ℝ (interactionTheta α) z := by
  have h : AnalyticAt ℝ (fun y : ℝ => Real.exp ((1 - α / 2) * y) /
      thetaDenominator y) z :=
    (analyticAt_const.mul analyticAt_id).rexp.div (thetaDenominator_analyticAt z)
      (ne_of_gt (thetaDenominator_pos z))
  exact h.congr (Eventually.of_forall fun y =>
    (interactionTheta_eq_analytic_quotient α y).symm)

/-- In particular the removable extension is smooth, for every real parameter. -/
theorem interactionTheta_contDiff (α : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (interactionTheta α) :=
  (show AnalyticOnNhd ℝ (interactionTheta α) univ from
    fun z _ => interactionTheta_analyticAt α z).contDiff

theorem interactionTheta_pos (α z : ℝ) : 0 < interactionTheta α z := by
  rw [interactionTheta_eq_analytic_quotient]
  exact div_pos (Real.exp_pos _) (thetaDenominator_pos z)

/-- Stable formula on the positive half-line. -/
def thetaTail (a x : ℝ) : ℝ := x * Real.exp (-a * x) / (1 - Real.exp (-x))

theorem interactionTheta_pos_formula (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    interactionTheta α x = thetaTail (α / 2) x := by
  have he := Real.exp_ne_zero x
  have hmul : Real.exp ((1 - α / 2) * x) = Real.exp x * Real.exp (-(α / 2) * x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [interactionTheta, if_neg hx, thetaTail, hmul, Real.exp_neg]
  field_simp

theorem interactionTheta_neg_formula (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    interactionTheta α (-x) = thetaTail (1 - α / 2) x := by
  rw [interactionTheta, if_neg (neg_ne_zero.mpr hx), thetaTail]
  have h : (1 - α / 2) * -x = -(1 - α / 2) * x := by ring
  rw [h, show Real.exp (-x) - 1 = -(1 - Real.exp (-x)) by ring, div_neg]
  ring


/-- First derivative of the stable half-line expression. -/
def thetaTailFirst (a x : ℝ) : ℝ :=
  Real.exp (-a * x) * ((1 - a * x) / (1 - Real.exp (-x)) -
    x * Real.exp (-x) / (1 - Real.exp (-x)) ^ 2)

/-- Second derivative, arranged so every denominator is uniformly positive on `x ≥ 1`. -/
def thetaTailSecond (a x : ℝ) : ℝ :=
  Real.exp (-a * x) * ((a ^ 2 * x - 2 * a) / (1 - Real.exp (-x)) -
    2 * (1 - a * x) * Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 +
    x * Real.exp (-x) * (1 + Real.exp (-x)) / (1 - Real.exp (-x)) ^ 3)

theorem thetaTail_hasDerivAt (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (thetaTail a) (thetaTailFirst a x) x := by
  have hd0 : 1 - Real.exp (-x) ≠ 0 := by
    intro h
    have : -x = 0 := Real.exp_injective (by simpa using (show Real.exp (-x) = 1 by linarith))
    exact hx (by linarith)
  have hE := ((hasDerivAt_id x).const_mul (-a)).exp
  have he := ((hasDerivAt_id x).neg).exp
  convert ((hasDerivAt_id x).mul hE).div ((hasDerivAt_const x 1).sub he) hd0 using 1 <;>
    first | rfl | (dsimp [thetaTailFirst]; field_simp; ring)

theorem thetaTailFirst_hasDerivAt (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (thetaTailFirst a) (thetaTailSecond a x) x := by
  have hd0 : 1 - Real.exp (-x) ≠ 0 := by
    intro h
    have : -x = 0 := Real.exp_injective (by simpa using (show Real.exp (-x) = 1 by linarith))
    exact hx (by linarith)
  have hE := ((hasDerivAt_id x).const_mul (-a)).exp
  have he := ((hasDerivAt_id x).neg).exp
  have hd := (hasDerivAt_const x 1).sub he
  have hC := (hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul a)
  convert hE.mul ((hC.div hd hd0).sub
    (((hasDerivAt_id x).mul he).div (hd.pow 2) (pow_ne_zero 2 hd0))) using 1 <;>
    first | rfl | (dsimp [thetaTailSecond]; field_simp; ring)


/-- A fixed positive denominator lower bound on either exponential tail. -/
def thetaTailGap : ℝ := 1 - Real.exp (-1)

theorem thetaTailGap_pos : 0 < thetaTailGap := by
  unfold thetaTailGap
  have h : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
  exact sub_pos.mpr (by simpa only [Real.exp_zero] using h)

/-- Universal coefficient for the second-derivative tail when `0 ≤ a ≤ 1`. -/
def thetaTailConstant : ℝ :=
  2 / thetaTailGap + 2 / thetaTailGap ^ 2 + 2 / thetaTailGap ^ 3

theorem thetaTailConstant_pos : 0 < thetaTailConstant := by
  have := thetaTailGap_pos
  unfold thetaTailConstant
  positivity

private theorem thetaTail_denominator_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 < Real.exp (-x) ∧ Real.exp (-x) ≤ 1 ∧
      thetaTailGap ≤ 1 - Real.exp (-x) ∧ 0 < 1 - Real.exp (-x) := by
  have he : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have hg := thetaTailGap_pos
  refine ⟨Real.exp_pos _, ?_, ?_, ?_⟩
  · exact (Real.exp_le_exp.mpr (by linarith : -x ≤ 0)).trans_eq Real.exp_zero
  · unfold thetaTailGap; linarith
  · unfold thetaTailGap at hg; linarith

theorem thetaTail_abs_le {a x : ℝ} (hx : 1 ≤ x) :
    |thetaTail a x| ≤ (1 / thetaTailGap) * (1 + x) * Real.exp (-a * x) := by
  obtain ⟨he, he1, hd, hd0⟩ := thetaTail_denominator_bounds hx
  rw [thetaTail, abs_div, abs_mul, abs_of_nonneg (by linarith : 0 ≤ x),
    abs_of_pos (Real.exp_pos _), abs_of_pos hd0]
  calc
    x * Real.exp (-a * x) / (1 - Real.exp (-x)) ≤
        (1 + x) * Real.exp (-a * x) / thetaTailGap := by
      gcongr
      · exact thetaTailGap_pos
      · linarith
    _ = _ := by ring

theorem thetaTailSecond_abs_le {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 1 ≤ x) :
    |thetaTailSecond a x| ≤ thetaTailConstant * (1 + x) * Real.exp (-a * x) := by
  obtain ⟨he, he1, hd, hd0⟩ := thetaTail_denominator_bounds hx
  have hg := thetaTailGap_pos
  have hx0 : 0 ≤ x := by linarith
  have hab : |1 - a * x| ≤ 1 + x := by
    calc
      |1 - a * x| ≤ |(1 : ℝ)| + |a * x| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (1 : ℝ) 0 (a * x)
      _ = 1 + a * x := by rw [abs_one, abs_of_nonneg (mul_nonneg ha0 hx0)]
      _ ≤ 1 + x := by nlinarith
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hac : |a ^ 2 * x - 2 * a| ≤ 2 * (1 + x) := by
    calc
      |a ^ 2 * x - 2 * a| ≤ |a ^ 2 * x| + |2 * a| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (a ^ 2 * x) 0 (2 * a)
      _ = a ^ 2 * x + 2 * a := by
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hx0), abs_of_nonneg (by positivity)]
      _ ≤ 2 * (1 + x) := by nlinarith [mul_le_mul_of_nonneg_right ha2 hx0]
  have h1 : |(a ^ 2 * x - 2 * a) / (1 - Real.exp (-x))| ≤
      2 * (1 + x) / thetaTailGap := by
    rw [abs_div, abs_of_pos hd0]
    gcongr
  have h2 : |2 * (1 - a * x) * Real.exp (-x) / (1 - Real.exp (-x)) ^ 2| ≤
      2 * (1 + x) / thetaTailGap ^ 2 := by
    rw [abs_div, abs_pow, abs_of_pos hd0, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos he]
    calc
      2 * |1 - a * x| * Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 ≤
          2 * (1 + x) * 1 / thetaTailGap ^ 2 := by
        gcongr
      _ = _ := by ring
  have h3 : |x * Real.exp (-x) * (1 + Real.exp (-x)) / (1 - Real.exp (-x)) ^ 3| ≤
      2 * (1 + x) / thetaTailGap ^ 3 := by
    rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ x * Real.exp (-x) * (1 + Real.exp (-x))),
      abs_of_pos (pow_pos hd0 3)]
    calc
      x * Real.exp (-x) * (1 + Real.exp (-x)) / (1 - Real.exp (-x)) ^ 3 ≤
          (1 + x) * 1 * (1 + 1) / thetaTailGap ^ 3 := by
        gcongr
        all_goals first | exact thetaTailGap_pos | exact thetaTailGap_pos.le | positivity | linarith
      _ = _ := by ring
  unfold thetaTailSecond
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-a * x) * |(a ^ 2 * x - 2 * a) / (1 - Real.exp (-x)) -
        2 * (1 - a * x) * Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 +
        x * Real.exp (-x) * (1 + Real.exp (-x)) / (1 - Real.exp (-x)) ^ 3| ≤
      Real.exp (-a * x) * (2 * (1 + x) / thetaTailGap +
        2 * (1 + x) / thetaTailGap ^ 2 + 2 * (1 + x) / thetaTailGap ^ 3) := by
      gcongr
      apply le_trans (abs_add_le _ _)
      apply add_le_add
      · exact (abs_sub _ _).trans (add_le_add h1 h2)
      · exact h3
    _ = _ := by unfold thetaTailConstant; ring


/-- The explicit tail formula is the genuine second derivative of the removable profile. -/
theorem interactionTheta_secondDeriv_pos (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv (interactionTheta α)) x = thetaTailSecond (α / 2) x := by
  have h : interactionTheta α =ᶠ[𝓝 x] thetaTail (α / 2) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact interactionTheta_pos_formula α hy
  have h' : deriv (thetaTail (α / 2)) =ᶠ[𝓝 x] thetaTailFirst (α / 2) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (thetaTail_hasDerivAt (α / 2) hy).deriv
  exact h.deriv.deriv_eq.trans (h'.deriv_eq.trans (thetaTailFirst_hasDerivAt (α / 2) hx).deriv)

private theorem thetaTail_reflect_hasDerivAt (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => thetaTail a (-y)) (-thetaTailFirst a (-x)) x := by
  convert (thetaTail_hasDerivAt a (neg_ne_zero.mpr hx)).comp x (hasDerivAt_id x).neg using 1 <;>
    first | rfl | ring

private theorem thetaTailFirst_reflect_hasDerivAt (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => -thetaTailFirst a (-y)) (thetaTailSecond a (-x)) x := by
  convert ((thetaTailFirst_hasDerivAt a (neg_ne_zero.mpr hx)).comp x
    (hasDerivAt_id x).neg).neg using 1 <;> first | rfl | ring

theorem interactionTheta_secondDeriv_neg (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv (interactionTheta α)) (-x) = thetaTailSecond (1 - α / 2) x := by
  have h : interactionTheta α =ᶠ[𝓝 (-x)] (fun y => thetaTail (1 - α / 2) (-y)) := by
    filter_upwards [eventually_ne_nhds (neg_ne_zero.mpr hx)] with y hy
    simpa only [neg_neg] using interactionTheta_neg_formula α (neg_ne_zero.mpr hy)
  have h' : deriv (fun y => thetaTail (1 - α / 2) (-y)) =ᶠ[𝓝 (-x)]
      (fun y => -thetaTailFirst (1 - α / 2) (-y)) := by
    filter_upwards [eventually_ne_nhds (neg_ne_zero.mpr hx)] with y hy
    exact (thetaTail_reflect_hasDerivAt (1 - α / 2) hy).deriv
  simpa only [neg_neg] using h.deriv.deriv_eq.trans
    (h'.deriv_eq.trans (thetaTailFirst_reflect_hasDerivAt (1 - α / 2) (neg_ne_zero.mpr hx)).deriv)

/-- Positive-tail bound, uniform over the full manuscript range `0 < α ≤ 1`. -/
theorem interactionTheta_secondDeriv_pos_bound {α x : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hx : 1 ≤ x) :
    |deriv (deriv (interactionTheta α)) x| ≤
      thetaTailConstant * (1 + x) * Real.exp (-(α / 2) * x) := by
  rw [interactionTheta_secondDeriv_pos α (by linarith)]
  exact thetaTailSecond_abs_le (by linarith) (by linarith) hx

/-- Negative-tail bound. The second decay exponent remains positive without symmetry assumptions. -/
theorem interactionTheta_secondDeriv_neg_bound {α x : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hx : 1 ≤ x) :
    |deriv (deriv (interactionTheta α)) (-x)| ≤
      thetaTailConstant * (1 + x) * Real.exp (-(1 - α / 2) * x) := by
  rw [interactionTheta_secondDeriv_neg α (by linarith)]
  exact thetaTailSecond_abs_le (by linarith) (by linarith) hx


private theorem thetaTailEnvelope_integrableOn {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (1 + x) * Real.exp (-a * x)) (Ioi 1) := by
  have h0 := integrableOn_exp_mul_Ioi (show -a < 0 by linarith) (1 : ℝ)
  have h1 : IntegrableOn (fun x : ℝ => x * Real.exp (-a * x)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) le_rfl ha
  have hh := h0.add (h1.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
  exact hh.congr_fun (fun x _ => by dsimp; ring) measurableSet_Ioi

set_option maxHeartbeats 800000 in
/-- Continuous functions controlled by the two genuine exponential tails are integrable. -/
private theorem integrable_of_thetaTail_bounds {f : ℝ → ℝ} (hf : Continuous f)
    {a b C : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ x : ℝ, 1 ≤ x → |f x| ≤ C * (1 + x) * Real.exp (-a * x))
    (hl : ∀ x : ℝ, 1 ≤ x → |f (-x)| ≤ C * (1 + x) * Real.exp (-b * x)) :
    Integrable f := by
  have hiR : IntegrableOn f (Ioi 1) := by
    apply ((thetaTailEnvelope_integrableOn ha).const_mul C).mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs, mul_assoc] using hr x hx.le
  have hiL' : IntegrableOn (fun x => f (-x)) (Ioi 1) := by
    apply ((thetaTailEnvelope_integrableOn hb).const_mul C).mono'
      (hf.comp continuous_neg).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs, mul_assoc, Function.comp_apply] using hl x hx.le
  have hiL : IntegrableOn f (Iio (-1)) := by
    have hh : IntegrableOn (fun x => f (-x)) (Ioi (-(-1 : ℝ))) := by
      simpa only [neg_neg] using hiL'
    simpa only [neg_neg] using hh.comp_neg_Iio (c := (-1 : ℝ))
  have hiM : IntegrableOn f (Icc (-1) 1) := hf.integrableOn_Icc
  rw [← integrableOn_univ]
  apply ((hiL.union hiM).union hiR).mono_set
  intro x _
  simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi]
  rcases lt_or_ge x (-1) with hx | hx
  · exact Or.inl (Or.inl hx)
  · rcases le_or_gt x 1 with hx' | hx'
    · exact Or.inl (Or.inr ⟨hx, hx'⟩)
    · exact Or.inr hx'

/-- Actual `θ_α ∈ L¹(ℝ)` for the manuscript parameter range. -/
theorem interactionTheta_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    Integrable (interactionTheta α) := by
  apply integrable_of_thetaTail_bounds (interactionTheta_contDiff α (n := 0)).continuous
    (a := α / 2) (b := 1 - α / 2) (C := 1 / thetaTailGap) (by linarith) (by linarith)
  · intro x hx
    rw [interactionTheta_pos_formula α (by linarith)]
    exact thetaTail_abs_le hx
  · intro x hx
    rw [interactionTheta_neg_formula α (by linarith)]
    exact thetaTail_abs_le hx

/-- Actual classical second derivative belongs to `L¹`; no derivative certificate is an input. -/
theorem interactionTheta_secondDeriv_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    Integrable (deriv (deriv (interactionTheta α))) := by
  have hc : Continuous (deriv (deriv (interactionTheta α))) := by
    have h : ContDiff ℝ (1 + 1) (interactionTheta α) := interactionTheta_contDiff α
    exact h.deriv'.continuous_deriv (by norm_num)
  exact integrable_of_thetaTail_bounds hc (a := α / 2) (b := 1 - α / 2)
    (C := thetaTailConstant) (by linarith) (by linarith)
    (fun _ hx => interactionTheta_secondDeriv_pos_bound hα0 hα1 hx)
    (fun _ hx => interactionTheta_secondDeriv_neg_bound hα0 hα1 hx)


private theorem thetaTailFirst_abs_le {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 1 ≤ x) :
    |thetaTailFirst a x| ≤
      (1 / thetaTailGap + 1 / thetaTailGap ^ 2) * (1 + x) * Real.exp (-a * x) := by
  obtain ⟨he, he1, hd, hd0⟩ := thetaTail_denominator_bounds hx
  have hg := thetaTailGap_pos
  have hx0 : 0 ≤ x := by linarith
  have hab : |1 - a * x| ≤ 1 + x :=
    (abs_sub _ _).trans (by rw [abs_one, abs_of_nonneg (mul_nonneg ha0 hx0)]; nlinarith)
  have h1 : |(1 - a * x) / (1 - Real.exp (-x))| ≤ (1 + x) / thetaTailGap := by
    rw [abs_div, abs_of_pos hd0]
    gcongr
  have h2 : |x * Real.exp (-x) / (1 - Real.exp (-x)) ^ 2| ≤
      (1 + x) / thetaTailGap ^ 2 := by
    rw [abs_div, abs_pow, abs_of_pos hd0, abs_mul, abs_of_nonneg hx0, abs_of_pos he]
    calc
      x * Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 ≤
        (1 + x) * 1 / thetaTailGap ^ 2 := by gcongr; linarith
      _ = _ := by ring
  unfold thetaTailFirst
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-a * x) * ((1 + x) / thetaTailGap + (1 + x) / thetaTailGap ^ 2) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (Real.exp_pos _).le
    _ = _ := by ring

/-- The first derivative is integrable as well, supplying the actual integration-by-parts chain. -/
theorem interactionTheta_deriv_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    Integrable (deriv (interactionTheta α)) := by
  have hc := (interactionTheta_contDiff α (n := 1)).continuous_deriv le_rfl
  apply integrable_of_thetaTail_bounds hc (a := α / 2) (b := 1 - α / 2)
    (C := 1 / thetaTailGap + 1 / thetaTailGap ^ 2) (by linarith) (by linarith)
  · intro x hx
    have heq : interactionTheta α =ᶠ[𝓝 x] thetaTail (α / 2) := by
      filter_upwards [eventually_ne_nhds (show x ≠ 0 by linarith)] with y hy
      exact interactionTheta_pos_formula α hy
    rw [heq.deriv_eq, (thetaTail_hasDerivAt (α / 2) (by linarith)).deriv]
    exact thetaTailFirst_abs_le (by linarith) (by linarith) hx
  · intro x hx
    have heq : interactionTheta α =ᶠ[𝓝 (-x)] (fun y => thetaTail (1 - α / 2) (-y)) := by
      filter_upwards [eventually_ne_nhds (show -x ≠ 0 by linarith)] with y hy
      simpa only [neg_neg] using interactionTheta_neg_formula α (neg_ne_zero.mpr hy)
    rw [heq.deriv_eq, (thetaTail_reflect_hasDerivAt (1 - α / 2) (by linarith)).deriv,
      neg_neg, abs_neg]
    exact thetaTailFirst_abs_le (by linarith) (by linarith) hx


open scoped FourierTransform RealInnerProductSpace

/-- An elementary Sobolev criterion for Fourier `L¹`, proved by two actual integrations by parts.
The bound uses the integrable majorant `(1 + ξ²)⁻¹`. -/
theorem fourier_integrable_of_integrable_two_derivatives {f : ℝ → ℂ}
    (h0 : Integrable f) (h1 : Integrable (deriv f)) (h2 : Integrable (deriv (deriv f)))
    (hd0 : Differentiable ℝ f) (hd1 : Differentiable ℝ (deriv f)) : Integrable (𝓕 f) := by
  have hF0 (x : ℝ) : ‖𝓕 f x‖ ≤ ∫ y : ℝ, ‖f y‖ := by
    rw [Real.fourier_eq]
    simpa only [Circle.norm_smul] using
      norm_integral_le_integral_norm (fun y : ℝ =>
        Real.fourierChar (-inner ℝ y x) • f y)
  have hF2 (x : ℝ) : ‖𝓕 (deriv (deriv f)) x‖ ≤ ∫ y : ℝ, ‖deriv (deriv f) y‖ := by
    rw [Real.fourier_eq]
    simpa only [Circle.norm_smul] using
      norm_integral_le_integral_norm (fun y : ℝ =>
        Real.fourierChar (-inner ℝ y x) • deriv (deriv f) y)
  have hD0 := Real.fourier_deriv h0 hd0 h1
  have hD1 := Real.fourier_deriv h1 hd1 h2
  have hdecay (x : ℝ) : x ^ 2 * ‖𝓕 f x‖ ≤ ∫ y : ℝ, ‖deriv (deriv f) y‖ := by
    have hid : ‖𝓕 (deriv (deriv f)) x‖ =
        (2 * Real.pi) ^ 2 * x ^ 2 * ‖𝓕 f x‖ := by
      rw [hD1, hD0]
      simp only [norm_smul, norm_mul, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, mul_one, abs_of_pos Real.pi_pos]
      rw [Complex.norm_two]
      ring_nf
      rw [sq_abs]
      ring
    have hc : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.one_le_pi_div_two]
    calc
      x ^ 2 * ‖𝓕 f x‖ ≤ (2 * Real.pi) ^ 2 * x ^ 2 * ‖𝓕 f x‖ := by
        nlinarith [mul_nonneg (sq_nonneg x) (norm_nonneg (𝓕 f x))]
      _ = ‖𝓕 (deriv (deriv f)) x‖ := hid.symm
      _ ≤ _ := hF2 x
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h0
  apply (integrable_inv_one_add_sq.const_mul
    ((∫ y : ℝ, ‖f y‖) + ∫ y : ℝ, ‖deriv (deriv f) y‖)).mono' hc.aestronglyMeasurable
  filter_upwards with x
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)]
  nlinarith [hF0 x, hdecay x]


/-- Complex-valued lift for Mathlib's Fourier transform; the underlying scalar profile is real. -/
def interactionThetaComplex (α x : ℝ) : ℂ := interactionTheta α x

theorem interactionThetaComplex_contDiff (α : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (interactionThetaComplex α) :=
  Complex.ofRealCLM.contDiff.comp (interactionTheta_contDiff α)

theorem interactionThetaComplex_deriv (α : ℝ) :
    deriv (interactionThetaComplex α) = fun x => Complex.ofReal (deriv (interactionTheta α) x) := by
  funext x
  exact (((interactionTheta_contDiff α (n := 1)).differentiable_one x).hasDerivAt.ofReal_comp).deriv

theorem interactionThetaComplex_secondDeriv (α : ℝ) :
    deriv (deriv (interactionThetaComplex α)) =
      fun x => Complex.ofReal (deriv (deriv (interactionTheta α)) x) := by
  rw [interactionThetaComplex_deriv]
  funext x
  have h : ContDiff ℝ (1 + 1) (interactionTheta α) := interactionTheta_contDiff α
  exact ((h.deriv'.differentiable_one x).hasDerivAt.ofReal_comp).deriv

/-- Fourier `L¹` regularity of the actual universal theta profile. -/
theorem interactionTheta_fourier_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    Integrable (𝓕 (interactionThetaComplex α)) := by
  have h0 : Integrable (interactionThetaComplex α) :=
    Complex.ofRealCLM.integrable_comp (interactionTheta_integrable hα0 hα1)
  have h1 : Integrable (deriv (interactionThetaComplex α)) := by
    rw [interactionThetaComplex_deriv]
    exact Complex.ofRealCLM.integrable_comp (interactionTheta_deriv_integrable hα0 hα1)
  have h2 : Integrable (deriv (deriv (interactionThetaComplex α))) := by
    rw [interactionThetaComplex_secondDeriv]
    exact Complex.ofRealCLM.integrable_comp (interactionTheta_secondDeriv_integrable hα0 hα1)
  have hc : ContDiff ℝ (1 + 1) (interactionThetaComplex α) := interactionThetaComplex_contDiff α
  exact fourier_integrable_of_integrable_two_derivatives h0 h1 h2
    (hc.differentiable (by norm_num)) hc.deriv'.differentiable_one

/-- Pointwise Fourier inversion, including the former singularity at `z = 0`. -/
theorem interactionTheta_fourier_inversion {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    𝓕⁻ (𝓕 (interactionThetaComplex α)) = interactionThetaComplex α :=
  (interactionThetaComplex_contDiff α (n := 0)).continuous.fourierInv_fourier_eq
    (Complex.ofRealCLM.integrable_comp (interactionTheta_integrable hα0 hα1))
    (interactionTheta_fourier_integrable hα0 hα1)


/-- The pointwise inverse transform with Mathlib's `2π` normalization made explicit. -/
theorem interactionTheta_fourier_integral {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (z : ℝ) :
    (interactionTheta α z : ℂ) = ∫ ξ : ℝ,
      (𝓕 (interactionThetaComplex α)) ξ *
        Complex.exp (((2 * Real.pi * ξ * z : ℝ) : ℂ) * Complex.I) := by
  have h := congrFun (interactionTheta_fourier_inversion hα0 hα1) z
  rw [Real.fourierInv_eq'] at h
  exact h.symm.trans (integral_congr_ae (Eventually.of_forall fun ξ => by
    simp only [Real.inner_apply, smul_eq_mul]
    rw [mul_assoc (2 * Real.pi) ξ z, mul_comm]))

/-- Fourier density for the unnormalized exponent `exp (i ξ z)` used by real Schur factors. -/
def interactionThetaFourierDensity (α ξ : ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • (𝓕 (interactionThetaComplex α)) ((2 * Real.pi)⁻¹ * ξ)

theorem interactionThetaFourierDensity_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    Integrable (interactionThetaFourierDensity α) := by
  exact ((interactionTheta_fourier_integrable hα0 hα1).comp_mul_left'
    (inv_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0))).smul ((2 * Real.pi)⁻¹ : ℝ)

/-- A genuine Fourier-L¹ representation with exactly the exponent used in the operator layer. -/
theorem interactionTheta_density_integral {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (z : ℝ) :
    (interactionTheta α z : ℂ) = ∫ ξ : ℝ, interactionThetaFourierDensity α ξ *
      Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I) := by
  let k : ℝ := 2 * Real.pi
  have hk : 0 < k := by dsimp [k]; positivity
  let g : ℝ → ℂ := fun ξ => (𝓕 (interactionThetaComplex α)) ξ *
    Complex.exp (((k * ξ * z : ℝ) : ℂ) * Complex.I)
  have hscale : (fun ξ : ℝ => interactionThetaFourierDensity α ξ *
      Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)) =
      fun ξ : ℝ => k⁻¹ • g (k⁻¹ * ξ) := by
    funext ξ
    dsimp only [interactionThetaFourierDensity, g]
    rw [← smul_mul_assoc]
    congr 2
    dsimp only [k]
    congr 2
    field_simp
  rw [hscale, integral_smul, Measure.integral_comp_inv_mul_left,
    abs_of_pos hk, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  exact interactionTheta_fourier_integral hα0 hα1 z

/-- Taking real parts gives the exact real Fourier representation of `θ`. -/
theorem interactionTheta_real_density_integral {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (z : ℝ) :
    interactionTheta α z = (∫ ξ : ℝ, interactionThetaFourierDensity α ξ *
      Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)).re := by
  exact congrArg Complex.re (interactionTheta_density_integral hα0 hα1 z)

end
end KernelSeq
