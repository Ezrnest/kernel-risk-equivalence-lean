import KernelSeq.CompactDOI
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A fixed smooth even symbol for Lipschitz divided differences

An actual radial smooth bump on the real line is one on `[-2,2]` and zero
outside `(-3,3)`. Multiplying the slope `t / s` by that bump constructs a
fixed, bounded, even, degree-zero homogeneous function on the plane, smooth
away from the origin. Its restriction to every one-Lipschitz graph is the
actual zero-diagonal divided difference, including repeated scalar labels.

This is the concrete scalar symbol underlying the finite specialization of
Caspers--Montgomery-Smith--Potapov--Sukochev, Theorem 5.1. No Fourier, Schur,
or Schatten multiplier norm bound is asserted in this module.
-/

open Set Filter Topology
open scoped ContDiff

namespace KernelSeq
noncomputable section

/-- The fixed actual smooth cutoff, with a margin around the Lipschitz cone. -/
def lipschitzEvenBump : ContDiffBump (0 : ℝ) where
  rIn := 2
  rOut := 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def lipschitzEvenCutoff (r : ℝ) : ℝ := lipschitzEvenBump r

theorem lipschitzEvenCutoff_nonneg (r : ℝ) : 0 ≤ lipschitzEvenCutoff r :=
  lipschitzEvenBump.nonneg

theorem lipschitzEvenCutoff_le_one (r : ℝ) : lipschitzEvenCutoff r ≤ 1 :=
  lipschitzEvenBump.le_one

theorem lipschitzEvenCutoff_neg (r : ℝ) :
    lipschitzEvenCutoff (-r) = lipschitzEvenCutoff r := lipschitzEvenBump.neg r

theorem lipschitzEvenCutoff_eq_one {r : ℝ} (hr : |r| ≤ 2) :
    lipschitzEvenCutoff r = 1 := by
  apply lipschitzEvenBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, lipschitzEvenBump] using hr

theorem lipschitzEvenCutoff_eq_zero {r : ℝ} (hr : 3 ≤ |r|) :
    lipschitzEvenCutoff r = 0 := by
  apply lipschitzEvenBump.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, lipschitzEvenBump] using hr

theorem lipschitzEvenCutoff_contDiff : ContDiff ℝ ∞ lipschitzEvenCutoff :=
  lipschitzEvenBump.contDiff

/-- Division is totalized, so this definition has the genuine value zero
on the vertical axis. Away from the origin it is locally zero near that axis. -/
def lipschitzEvenSymbol (s t : ℝ) : ℝ :=
  lipschitzEvenCutoff (t / s) * (t / s)

@[simp]
theorem lipschitzEvenSymbol_zero_left (t : ℝ) : lipschitzEvenSymbol 0 t = 0 := by
  simp [lipschitzEvenSymbol]

@[simp]
theorem lipschitzEvenSymbol_zero_right (s : ℝ) : lipschitzEvenSymbol s 0 = 0 := by
  simp [lipschitzEvenSymbol]

/-- The symbol is actually zero outside its fixed cone, including its boundary. -/
theorem lipschitzEvenSymbol_eq_zero {s t : ℝ} (h : 3 * |s| ≤ |t|) :
    lipschitzEvenSymbol s t = 0 := by
  by_cases hs : s = 0
  · simp [hs]
  · have hr : 3 ≤ |t / s| := by
      rw [abs_div]
      exact (le_div_iff₀ (abs_pos.mpr hs)).mpr h
    simp only [lipschitzEvenSymbol, lipschitzEvenCutoff_eq_zero hr, zero_mul]

/-- The fixed planar symbol has a global numerical size bound. -/
theorem lipschitzEvenSymbol_abs_le (s t : ℝ) : |lipschitzEvenSymbol s t| ≤ 3 := by
  by_cases hr : 3 ≤ |t / s|
  · simp only [lipschitzEvenSymbol, lipschitzEvenCutoff_eq_zero hr, zero_mul, abs_zero]
    norm_num
  · calc
      _ = lipschitzEvenCutoff (t / s) * |t / s| := by
        rw [lipschitzEvenSymbol, abs_mul, abs_of_nonneg (lipschitzEvenCutoff_nonneg _)]
      _ ≤ 1 * |t / s| := mul_le_mul_of_nonneg_right (lipschitzEvenCutoff_le_one _) (abs_nonneg _)
      _ ≤ 3 := by linarith

/-- Evenness under simultaneous reflection of the two coordinates. -/
theorem lipschitzEvenSymbol_even (s t : ℝ) :
    lipschitzEvenSymbol (-s) (-t) = lipschitzEvenSymbol s t := by
  simp only [lipschitzEvenSymbol, neg_div_neg_eq]

/-- Degree-zero homogeneity holds for every nonzero real dilation. -/
theorem lipschitzEvenSymbol_homogeneous (s t : ℝ) {r : ℝ} (hr : r ≠ 0) :
    lipschitzEvenSymbol (r * s) (r * t) = lipschitzEvenSymbol s t := by
  have hd : (r * t) / (r * s) = t / s := mul_div_mul_left t s hr
  simp only [lipschitzEvenSymbol, hd]

/-- Genuine smoothness at every nonzero point of the plane. The vertical-axis
case uses a neighborhood on which the constructed symbol vanishes exactly. -/
theorem lipschitzEvenSymbol_contDiffAt {z : ℝ × ℝ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (Function.uncurry lipschitzEvenSymbol) z := by
  by_cases hs : z.1 = 0
  · have ht : z.2 ≠ 0 := by
      intro ht
      apply hz
      exact Prod.ext hs ht
    have hopen : IsOpen {p : ℝ × ℝ | 3 * |p.1| < |p.2|} :=
      isOpen_lt (by fun_prop) (by fun_prop)
    have hmem : z ∈ {p : ℝ × ℝ | 3 * |p.1| < |p.2|} := by
      simp only [mem_setOf_eq, hs, abs_zero, mul_zero]
      exact abs_pos.mpr ht
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hmem] with p hp
    exact lipschitzEvenSymbol_eq_zero hp.le
  · have hdiv : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => p.2 / p.1) z :=
      contDiffAt_snd.div contDiffAt_fst hs
    exact (lipschitzEvenCutoff_contDiff.contDiffAt.comp z hdiv).mul hdiv

theorem lipschitzEvenSymbol_contDiffOn :
    ContDiffOn ℝ ∞ (Function.uncurry lipschitzEvenSymbol) ({0}ᶜ : Set (ℝ × ℝ)) := by
  intro z hz
  exact (lipschitzEvenSymbol_contDiffAt (by simpa only [mem_compl_iff, mem_singleton_iff] using hz)).contDiffWithinAt

/-- On every actual one-Lipschitz graph the fixed symbol is precisely the
zero-diagonal divided difference. No graph-identification premise is used. -/
theorem dividedDifference_eq_lipschitzEvenSymbol {f : ℝ → ℝ}
    (hf : ∀ x y, |f x - f y| ≤ |x - y|) (x y : ℝ) :
    dividedDifference f x y = lipschitzEvenSymbol (x - y) (f x - f y) := by
  by_cases hxy : x = y
  · subst y
    simp [dividedDifference]
  · have hr : |(f x - f y) / (x - y)| ≤ 2 := by
      rw [abs_div]
      have hs : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
      have hh := (div_le_one hs).mpr (hf x y)
      linarith
    rw [lipschitzEvenSymbol, lipschitzEvenCutoff_eq_one hr, one_mul]
    simp only [dividedDifference, if_neg hxy]

end
end KernelSeq
