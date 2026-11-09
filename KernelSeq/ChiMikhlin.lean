import KernelSeq.AnalyticSchurBounds
import KernelSeq.UniversalThetaRegularity
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The actual chi interaction symbol satisfies the C1 HMS conditions

The removable value at zero is proved compatible with a globally analytic
quotient of exponential divided slopes. Stable half-axis formulas give the
weighted derivative bounds outside a compact interval; continuity supplies a
finite bound on that interval. No smoothness or boundedness certificate for
the interaction symbol is assumed.
-/

open Set Filter Topology

namespace KernelSeq

noncomputable section

/-- The removable extension is an actual analytic quotient, for every real
parameter, including parameters at which its numerator vanishes identically. -/
theorem interactionChi_eq_analytic_quotient (α z : ℝ) :
    interactionChi α z = -(1 - α / 2) * thetaDenominator ((1 - α / 2) * z) / thetaDenominator z := by
  by_cases hz : z = 0
  · subst z
    simp only [interactionChi, if_true, mul_zero, thetaDenominator_zero, mul_one, div_one]
    ring
  · by_cases ha : 1 - α / 2 = 0
    · rw [interactionChi, if_neg hz, ha, zero_mul, Real.exp_zero, sub_self, zero_div, neg_zero,
        zero_mul, zero_div]
    · rw [interactionChi, if_neg hz, thetaDenominator_of_ne (mul_ne_zero ha hz), thetaDenominator_of_ne hz]
      have ha2 : 2 - α ≠ 0 := by intro h; apply ha; linarith
      field_simp [ha, ha2, hz, exp_sub_one_ne_zero hz]
      ring

/-- There is no singularity at zero: the actual manuscript chi is analytic
everywhere, not merely a separately defined smooth substitute. -/
theorem interactionChi_analyticAt (α z : ℝ) : AnalyticAt ℝ (interactionChi α) z := by
  have hcomp : AnalyticAt ℝ (fun y : ℝ => thetaDenominator ((1 - α / 2) * y)) z :=
    (thetaDenominator_analyticAt _).comp (analyticAt_const.mul analyticAt_id)
  have h : AnalyticAt ℝ (fun y : ℝ => -(1 - α / 2) * thetaDenominator ((1 - α / 2) * y) /
      thetaDenominator y) z := (analyticAt_const.mul hcomp).div (thetaDenominator_analyticAt z)
        (ne_of_gt (thetaDenominator_pos z))
  exact h.congr (Eventually.of_forall fun y => (interactionChi_eq_analytic_quotient α y).symm)

theorem interactionChi_contDiff (α : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (interactionChi α) :=
  (show AnalyticOnNhd ℝ (interactionChi α) univ from fun z _ => interactionChi_analyticAt α z).contDiff

/-- The actual chi takes values in [-1,0] on the manuscript parameter range.
This includes its genuine removable value at zero. -/
theorem interactionChi_mem_Icc {α : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (z : ℝ) :
    interactionChi α z ∈ Icc (-1 : ℝ) 0 := by
  have ha0 : 0 ≤ 1 - α / 2 := by linarith
  have ha1 : 1 - α / 2 ≤ 1 := by linarith
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · rw [interactionChi, if_neg (ne_of_lt hz)]
    have hden : Real.exp z - 1 < 0 := sub_neg.mpr (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hz)
    have haz : z ≤ (1 - α / 2) * z := by nlinarith
    have hnum : (1 - α / 2) * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 hz.le
    have he1 := Real.exp_le_exp.mpr haz
    have he2 : Real.exp ((1 - α / 2) * z) ≤ 1 := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnum
    constructor
    · apply (le_div_iff_of_neg hden).mpr
      linarith
    · exact div_nonpos_of_nonneg_of_nonpos (by linarith) hden.le
  · simp only [interactionChi, if_true]
    exact ⟨by linarith, by linarith⟩
  · rw [interactionChi, if_neg (ne_of_gt hz)]
    have hden : 0 < Real.exp z - 1 := sub_pos.mpr (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hz)
    have haz : (1 - α / 2) * z ≤ z := by nlinarith
    have hnum : 0 ≤ (1 - α / 2) * z := mul_nonneg ha0 hz.le
    have he1 := Real.exp_le_exp.mpr haz
    have he2 : 1 ≤ Real.exp ((1 - α / 2) * z) := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnum
    constructor
    · apply (le_div_iff₀ hden).mpr
      linarith
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

theorem interactionChi_abs_le_one {α : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (z : ℝ) :
    |interactionChi α z| ≤ 1 := by
  obtain ⟨hl, hr⟩ := interactionChi_mem_Icc hα0 hα2 z
  exact abs_le.mpr ⟨by linarith, hr.trans (by norm_num)⟩

/-- A stable positive-half-axis ratio, with one bounded denominator. -/
def chiTail (a x : ℝ) : ℝ :=
  (Real.exp (-x) - Real.exp (-a * x)) / (1 - Real.exp (-x))

/-- Its true derivative, written with a single squared denominator. -/
def chiTailFirst (a x : ℝ) : ℝ :=
  (a * Real.exp (-a * x) + (1 - a) * Real.exp (-(a + 1) * x) - Real.exp (-x)) /
    (1 - Real.exp (-x)) ^ 2

theorem interactionChi_pos_formula (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    interactionChi α x = chiTail (α / 2) x := by
  rw [interactionChi, if_neg hx, chiTail]
  have he : Real.exp ((1 - α / 2) * x) = Real.exp x * Real.exp (-(α / 2) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

theorem interactionChi_neg_formula (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    interactionChi α (-x) = -1 - chiTail (1 - α / 2) x := by
  rw [interactionChi, if_neg (neg_ne_zero.mpr hx), chiTail]
  have he : (1 - α / 2) * -x = -(1 - α / 2) * x := by ring
  rw [he]
  have hd : 1 - Real.exp (-x) ≠ 0 := by
    have hh := exp_sub_one_ne_zero (neg_ne_zero.mpr hx)
    exact fun h => hh (by linarith)
  field_simp [hd, exp_sub_one_ne_zero (neg_ne_zero.mpr hx)]
  ring

theorem chiTail_hasDerivAt (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (chiTail a) (chiTailFirst a x) x := by
  have hd : 1 - Real.exp (-x) ≠ 0 := by
    intro h
    have hh : Real.exp (-x) = Real.exp 0 := by simpa only [Real.exp_zero] using (show Real.exp (-x) = 1 by linarith)
    exact hx (by linarith [Real.exp_injective hh])
  have h1 := ((hasDerivAt_id x).neg).exp
  have h2 := ((hasDerivAt_id x).const_mul (-a)).exp
  have he : Real.exp (-(a + 1) * x) = Real.exp (-a * x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  convert (h1.sub h2).div ((hasDerivAt_const x 1).sub h1) hd using 1 <;>
    first | rfl | (dsimp [chiTail, chiTailFirst]; rw [he]; field_simp; ring)


/-- The stable tail derivative has a uniform weighted bound. Every term is
controlled by `y exp(-y) ≤ exp(-1)`, with a genuine denominator gap. -/
theorem chiTailFirst_weighted_abs_le {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 1 ≤ x) :
    x * |chiTailFirst a x| ≤ 3 / thetaTailGap ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have he : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have hd : thetaTailGap ≤ 1 - Real.exp (-x) := by unfold thetaTailGap; linarith
  have hd0 : 0 < 1 - Real.exp (-x) := thetaTailGap_pos.trans_le hd
  have he1 : Real.exp (-1) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
  have hxe : x * Real.exp (-x) ≤ 1 := (Real.mul_exp_neg_le_exp_neg_one x).trans he1
  have hxa : x * (a * Real.exp (-a * x)) ≤ 1 := by
    have hh := (Real.mul_exp_neg_le_exp_neg_one (a * x)).trans he1
    rw [show -(a * x) = -a * x by ring] at hh
    nlinarith
  have heax : Real.exp (-(a + 1) * x) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by nlinarith)
  have hmid : (1 - a) * Real.exp (-(a + 1) * x) ≤ Real.exp (-x) := by
    calc
      _ ≤ (1 - a) * Real.exp (-x) := mul_le_mul_of_nonneg_left heax (by linarith)
      _ ≤ 1 * Real.exp (-x) := mul_le_mul_of_nonneg_right (by linarith : 1 - a ≤ 1) (Real.exp_pos _).le
      _ = _ := one_mul _
  have hxm : x * ((1 - a) * Real.exp (-(a + 1) * x)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hmid hx0).trans hxe
  have hn : |a * Real.exp (-a * x) + (1 - a) * Real.exp (-(a + 1) * x) - Real.exp (-x)| ≤
      a * Real.exp (-a * x) + (1 - a) * Real.exp (-(a + 1) * x) + Real.exp (-x) := by
    refine (abs_sub _ _).trans_eq ?_
    rw [abs_of_nonneg (add_nonneg (mul_nonneg ha0 (Real.exp_pos _).le)
      (mul_nonneg (by linarith) (Real.exp_pos _).le)), abs_of_pos (Real.exp_pos _)]
  have hnum : x * |a * Real.exp (-a * x) + (1 - a) * Real.exp (-(a + 1) * x) - Real.exp (-x)| ≤ 3 := by
    have hh := mul_le_mul_of_nonneg_left hn hx0
    nlinarith
  rw [chiTailFirst, abs_div, abs_pow, abs_of_pos hd0]
  calc
    _ = (x * |a * Real.exp (-a * x) + (1 - a) * Real.exp (-(a + 1) * x) - Real.exp (-x)|) /
        (1 - Real.exp (-x)) ^ 2 := by ring
    _ ≤ 3 / (1 - Real.exp (-x)) ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ 3 / thetaTailGap ^ 2 := div_le_div_of_nonneg_left (by norm_num)
      (sq_pos_of_pos thetaTailGap_pos) (pow_le_pow_left₀ thetaTailGap_pos.le hd 2)

/-- Actual derivative on the positive half-axis. -/
theorem interactionChi_deriv_pos (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (interactionChi α) x = chiTailFirst (α / 2) x := by
  have heq : interactionChi α =ᶠ[𝓝 x] chiTail (α / 2) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact interactionChi_pos_formula α hy
  exact heq.deriv_eq.trans (chiTail_hasDerivAt (α / 2) hx).deriv

private theorem chiTail_reflect_hasDerivAt (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => chiTail a (-y)) (-chiTailFirst a (-x)) x := by
  convert (chiTail_hasDerivAt a (neg_ne_zero.mpr hx)).comp x (hasDerivAt_id x).neg using 1 <;>
    first | rfl | ring

/-- The reflected stable formula gives the genuine derivative on the negative
half-axis, including its chain-rule sign. -/
theorem interactionChi_deriv_neg (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (interactionChi α) (-x) = chiTailFirst (1 - α / 2) x := by
  have heq : interactionChi α =ᶠ[𝓝 (-x)] (fun y => -1 - chiTail (1 - α / 2) (-y)) := by
    filter_upwards [eventually_ne_nhds (neg_ne_zero.mpr hx)] with y hy
    simpa only [neg_neg] using interactionChi_neg_formula α (neg_ne_zero.mpr hy)
  have hd := (hasDerivAt_const (-x) (-1)).sub (chiTail_reflect_hasDerivAt (1 - α / 2) (neg_ne_zero.mpr hx))
  exact heq.deriv_eq.trans (by simpa only [neg_neg, sub_neg_eq_add, zero_add, Pi.sub_def] using hd.deriv)

/-- The actual weighted derivative is uniformly controlled outside [-1,1]. -/
theorem interactionChi_weighted_deriv_tail {α z : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 2)
    (hz : 1 ≤ |z|) : |z| * |deriv (interactionChi α) z| ≤ 3 / thetaTailGap ^ 2 := by
  rcases le_or_gt 0 z with hzp | hzn
  · rw [abs_of_nonneg hzp] at hz ⊢
    rw [interactionChi_deriv_pos α (by linarith)]
    exact chiTailFirst_weighted_abs_le (by linarith) (by linarith) hz
  · have hx : 1 ≤ -z := by simpa only [abs_of_neg hzn] using hz
    have hh := chiTailFirst_weighted_abs_le (a := 1 - α / 2) (by linarith) (by linarith) hx
    rw [abs_of_neg hzn]
    have hder : deriv (interactionChi α) z = chiTailFirst (1 - α / 2) (-z) := by
      simpa only [neg_neg] using interactionChi_deriv_neg α (show -z ≠ 0 by linarith)
    rw [hder]
    exact hh

/-- A compact middle-interval bound taken from the actual derivative, rather
than an assumed bound or a substitute smooth function. -/
def chiCoreBound (α : ℝ) : ℝ :=
  sSup ((fun z : ℝ => |z| * |deriv (interactionChi α) z|) '' Icc (-1 : ℝ) 1)

/-- A named genuine finite HMS constant. The outer `max 1` also controls the
actual symbol values. Its compact part depends only on α. -/
def chiMikhlinBound (α : ℝ) : ℝ := max 1 (max (3 / thetaTailGap ^ 2) (chiCoreBound α))

theorem chiMikhlinBound_nonneg (α : ℝ) : 0 ≤ chiMikhlinBound α :=
  zero_le_one.trans (le_max_left _ _)

/-- The compact bound is finite because the actual removable profile is C∞. -/
theorem chiCoreBound_control (α : ℝ) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) :
    |z| * |deriv (interactionChi α) z| ≤ chiCoreBound α := by
  have hd : Continuous (deriv (interactionChi α)) :=
    (interactionChi_contDiff α (n := 1)).continuous_deriv le_rfl
  have hc : Continuous (fun z : ℝ => |z| * |deriv (interactionChi α) z|) := continuous_abs.mul hd.abs
  exact le_csSup (isCompact_Icc.bddAbove_image hc.continuousOn) ⟨z, hz, rfl⟩

/-- The complete actual weighted derivative bound combines the proved tails
and the compact maximum, with no boundedness certificate as an input. -/
theorem interactionChi_weighted_deriv_bound {α : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (z : ℝ) :
    |z| * |deriv (interactionChi α) z| ≤ chiMikhlinBound α := by
  by_cases hz : z ∈ Icc (-1 : ℝ) 1
  · exact (chiCoreBound_control α hz).trans ((le_max_right _ _).trans (le_max_right _ _))
  · have htail : 1 ≤ |z| := by
      simp only [mem_Icc, not_and_or, not_le] at hz
      rcases hz with hz | hz
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        exact hz.le
    exact (interactionChi_weighted_deriv_tail hα0 hα2 htail).trans
      ((le_max_left _ _).trans (le_max_right _ _))

/-- The actual off-diagonal symbol is C¹ on the whole off-diagonal domain.
Its diagonal zero convention does not claim continuity across that diagonal. -/
theorem interactionChiOffDiagonal_contDiffOn (α : ℝ) :
    ContDiffOn ℝ 1 (Function.uncurry (interactionChiOffDiagonal α)) schurOffDiagonal := by
  have hc : ContDiff ℝ 1 (fun z : ℝ × ℝ => interactionChi α (z.1 - z.2)) :=
    (interactionChi_contDiff α).comp (contDiff_fst.sub contDiff_snd)
  apply hc.contDiffOn.congr
  intro z hz
  change (if z.1 = z.2 then 0 else interactionChi α (z.1 - z.2)) = _
  exact if_neg hz

/-- The genuine left partial derivative, proved on the off-diagonal domain by
local equality and the chain rule. -/
theorem interactionChiOffDiagonal_deriv_left (α t s : ℝ) (hts : t ≠ s) :
    deriv (fun u => interactionChiOffDiagonal α u s) t = deriv (interactionChi α) (t - s) := by
  have heq : (fun u => interactionChiOffDiagonal α u s) =ᶠ[𝓝 t]
      (fun u => interactionChi α (u - s)) := by
    filter_upwards [eventually_ne_nhds hts] with u hu
    exact if_neg hu
  have hd := ((interactionChi_analyticAt α (t - s)).differentiableAt.hasDerivAt).comp t
    ((hasDerivAt_id t).sub_const s)
  exact heq.deriv_eq.trans (by simpa only [mul_one, Function.comp_def, id_eq] using hd.deriv)

/-- The genuine right partial derivative includes the negative chain-rule
sign; its absolute value has the same weighted bound. -/
theorem interactionChiOffDiagonal_deriv_right (α t s : ℝ) (hts : t ≠ s) :
    deriv (fun u => interactionChiOffDiagonal α t u) s = -deriv (interactionChi α) (t - s) := by
  have heq : (fun u => interactionChiOffDiagonal α t u) =ᶠ[𝓝 s]
      (fun u => interactionChi α (t - u)) := by
    filter_upwards [eventually_ne_nhds hts.symm] with u hu
    exact if_neg hu.symm
  have hd := ((interactionChi_analyticAt α (t - s)).differentiableAt.hasDerivAt).comp s
    ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  exact heq.deriv_eq.trans (by simpa only [sub_zero, zero_sub, mul_neg, mul_one, Pi.sub_def, Function.comp_def] using hd.deriv)

/-- The actual interaction chi satisfies every strict one-dimensional HMS
symbol condition. This theorem uses no HMS multiplier leaf and no regularity
or size certificate; it supplies the genuine symbol premises for that leaf.
It is slightly stronger than the source parameter range `0 < α ≤ 1`. -/
theorem interactionChiOffDiagonal_hms {α : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 2) :
    HMSBoundedSymbol (interactionChiOffDiagonal α) (chiMikhlinBound α) where
  bound_nonneg := chiMikhlinBound_nonneg α
  smooth_offDiagonal := interactionChiOffDiagonal_contDiffOn α
  size_bound := by
    intro t s
    by_cases hts : t = s
    · rw [interactionChiOffDiagonal, if_pos hts, abs_zero]
      exact chiMikhlinBound_nonneg α
    · rw [interactionChiOffDiagonal, if_neg hts]
      exact (interactionChi_abs_le_one hα0 hα2 (t - s)).trans (le_max_left _ _)
  deriv_left_bound := by
    intro t s hts
    rw [interactionChiOffDiagonal_deriv_left α t s hts]
    exact interactionChi_weighted_deriv_bound hα0 hα2 (t - s)
  deriv_right_bound := by
    intro t s hts
    rw [interactionChiOffDiagonal_deriv_right α t s hts, abs_neg]
    exact interactionChi_weighted_deriv_bound hα0 hα2 (t - s)

/-- The untruncated smooth difference symbol has the same actual HMS bound.
Applying `offDiagonalGridKernel` to this symbol gives exactly the manuscript
`interactionChiOffDiagonal`; no further diagonal-restriction theorem is used
in verifying these scalar symbol conditions. -/
theorem interactionChi_hms {α : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 2) :
    HMSBoundedSymbol (fun t s => interactionChi α (t - s)) (chiMikhlinBound α) where
  bound_nonneg := chiMikhlinBound_nonneg α
  smooth_offDiagonal := by
    have hc : ContDiff ℝ 1 (fun z : ℝ × ℝ => interactionChi α (z.1 - z.2)) :=
      (interactionChi_contDiff α).comp (contDiff_fst.sub contDiff_snd)
    exact hc.contDiffOn
  size_bound := fun t s => (interactionChi_abs_le_one hα0 hα2 (t - s)).trans (le_max_left _ _)
  deriv_left_bound := by
    intro t s _
    have hd := ((interactionChi_analyticAt α (t - s)).differentiableAt.hasDerivAt).comp t
      ((hasDerivAt_id t).sub_const s)
    have hder : deriv (fun u => interactionChi α (u - s)) t = deriv (interactionChi α) (t - s) := by
      simpa only [mul_one, Function.comp_def, id_eq] using hd.deriv
    rw [hder]
    exact interactionChi_weighted_deriv_bound hα0 hα2 (t - s)
  deriv_right_bound := by
    intro t s _
    have hd := ((interactionChi_analyticAt α (t - s)).differentiableAt.hasDerivAt).comp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    have hder : deriv (fun u => interactionChi α (t - u)) s = -deriv (interactionChi α) (t - s) := by
      simpa only [sub_zero, zero_sub, mul_neg, mul_one, Pi.sub_def, Function.comp_def] using hd.deriv
    rw [hder, abs_neg]
    exact interactionChi_weighted_deriv_bound hα0 hα2 (t - s)

end
end KernelSeq
