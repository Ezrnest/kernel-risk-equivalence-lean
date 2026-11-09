import KernelSeq.AnalyticSchurBounds
import KernelSeq.FourierSchur
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Reducing the finite Lipschitz leaf to the general finite HMS leaf

Real Steklov averages provide genuine C1 approximations with the original
Lipschitz constant. Their divided differences satisfy the actual HMS symbol
conditions. This avoids treating nonsmooth cutoff filters as C1 symbols.
-/

open MeasureTheory Filter Topology

namespace KernelSeq
noncomputable section

theorem continuous_of_abs_lipschitz {f : ℝ → ℝ} {L : ℝ}
    (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|) : Continuous f :=
  (LipschitzWith.of_dist_le' (fun s t => by simpa only [Real.dist_eq] using hLip s t)).continuous

def steklovPrimitive (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, f t

def steklovProfile (f : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  (steklovPrimitive f (x + ε) - steklovPrimitive f x) / ε

theorem steklovPrimitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (steklovPrimitive f) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem steklovPrimitive_contDiff {f : ℝ → ℝ} (hf : Continuous f) :
    ContDiff ℝ 1 (steklovPrimitive f) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (steklovPrimitive_hasDerivAt hf x).differentiableAt, ?_⟩
  have heq : deriv (steklovPrimitive f) = f := funext (fun x => (steklovPrimitive_hasDerivAt hf x).deriv)
  rw [heq]
  exact hf

theorem steklovProfile_contDiff {f : ℝ → ℝ} (hf : Continuous f) (ε : ℝ) :
    ContDiff ℝ 1 (steklovProfile f ε) := by
  have hp := steklovPrimitive_contDiff hf
  convert! ((hp.comp (contDiff_id.add contDiff_const)).sub hp).div_const ε using 1

theorem steklovProfile_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (ε x : ℝ) :
    HasDerivAt (steklovProfile f ε) ((f (x + ε) - f x) / ε) x := by
  have h1 := (steklovPrimitive_hasDerivAt hf (x + ε)).comp x ((hasDerivAt_id x).add_const ε)
  convert! (h1.sub (steklovPrimitive_hasDerivAt hf x)).div_const ε using 1
  simp

theorem steklovProfile_deriv_bound {f : ℝ → ℝ} {L ε : ℝ} (hε : ε ≠ 0)
    (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|) (x : ℝ) :
    |deriv (steklovProfile f ε) x| ≤ L := by
  rw [(steklovProfile_hasDerivAt (continuous_of_abs_lipschitz hLip) ε x).deriv, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hε)).mpr
  simpa only [add_sub_cancel_left] using hLip (x + ε) x

theorem steklovProfile_lipschitz {f : ℝ → ℝ} {L ε : ℝ} (hε : ε ≠ 0)
    (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|) (s t : ℝ) :
    |steklovProfile f ε s - steklovProfile f ε t| ≤ L * |s - t| := by
  have hf := steklovProfile_contDiff (continuous_of_abs_lipschitz hLip) ε
  have ht := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) => hf.differentiable (by norm_num) x)
    (fun x _ => by simpa only [Real.norm_eq_abs] using steklovProfile_deriv_bound hε hLip x)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ t) (Set.mem_univ s)
  simpa only [Real.norm_eq_abs] using ht

theorem steklovProfile_tendsto {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun ε => steklovProfile f ε x) (𝓝[≠] (0 : ℝ)) (𝓝 (f x)) := by
  have ht := (steklovPrimitive_hasDerivAt hf x).tendsto_slope_zero
  simpa only [steklovProfile, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht

theorem dividedDifference_eq_quotient (f : ℝ → ℝ) (s t : ℝ) :
    dividedDifference f s t = (f s - f t) / (s - t) := by
  by_cases h : s = t
  · simp [dividedDifference, h]
  · simp only [dividedDifference, if_neg h]

theorem dividedDifference_deriv_left {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {s t : ℝ} (hst : s ≠ t) :
    deriv (fun u => dividedDifference f u t) s =
      (deriv f s - dividedDifference f s t) / (s - t) := by
  have hd := (((hf.differentiable (by norm_num) s).hasDerivAt).sub_const (f t)).div
    ((hasDerivAt_id s).sub_const t) (sub_ne_zero.mpr hst)
  have heq : (fun u => dividedDifference f u t) = (fun u => (f u - f t) / (u - t)) :=
    funext (fun u => dividedDifference_eq_quotient f u t)
  have hd' : HasDerivAt (fun u => (f u - f t) / (u - t))
      ((deriv f s * (s - t) - (f s - f t)) / (s - t) ^ 2) s := by
    convert! hd using 1
    simp
  rw [heq, hd'.deriv, dividedDifference_eq_quotient]
  field_simp [sub_ne_zero.mpr hst]

theorem dividedDifference_deriv_right {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {s t : ℝ} (hst : s ≠ t) :
    deriv (fun u => dividedDifference f s u) t =
      (dividedDifference f s t - deriv f t) / (s - t) := by
  have hd := ((hasDerivAt_const t (f s)).sub
    ((hf.differentiable (by norm_num) t).hasDerivAt)).div
    ((hasDerivAt_const t s).sub (hasDerivAt_id t)) (sub_ne_zero.mpr hst)
  have heq : (fun u => dividedDifference f s u) = (fun u => (f s - f u) / (s - u)) :=
    funext (fun u => dividedDifference_eq_quotient f s u)
  have hd' : HasDerivAt (fun u => (f s - f u) / (s - u))
      ((-(deriv f t) * (s - t) + (f s - f t)) / (s - t) ^ 2) t := by
    convert! hd using 1
    simp
    ring
  rw [heq, hd'.deriv, dividedDifference_eq_quotient]
  field_simp [sub_ne_zero.mpr hst]
  ring

theorem dividedDifference_hms {f : ℝ → ℝ} {L : ℝ} (hf : ContDiff ℝ 1 f) (hL : 0 ≤ L)
    (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|) :
    HMSBoundedSymbol (dividedDifference f) (2 * L) where
  bound_nonneg := by positivity
  smooth_offDiagonal := by
    have hnum : ContDiff ℝ 1 (fun z : ℝ × ℝ => f z.1 - f z.2) :=
      (hf.comp contDiff_fst).sub (hf.comp contDiff_snd)
    have hden : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 - z.2) := contDiff_fst.sub contDiff_snd
    have hq := hnum.contDiffOn.div hden.contDiffOn
      (fun z (hz : z ∈ schurOffDiagonal) => sub_ne_zero.mpr hz)
    have heq : Function.uncurry (dividedDifference f) =
        (fun z : ℝ × ℝ => (f z.1 - f z.2) / (z.1 - z.2)) :=
      funext (fun z => dividedDifference_eq_quotient f z.1 z.2)
    rw [heq]
    exact hq
  size_bound := by
    intro s t
    have hd : |dividedDifference f s t| ≤ L := by
      simpa only [Real.norm_eq_abs] using dividedDifference_norm_le hL (hLip s t)
    exact hd.trans (by linarith)
  deriv_left_bound := by
    intro s t hst
    have hd : |deriv f s| ≤ L := by
      simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lip' (f := f) (x₀ := s) hL
        (Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hLip u s))
    have hdd : |dividedDifference f s t| ≤ L := by
      simpa only [Real.norm_eq_abs] using dividedDifference_norm_le hL (hLip s t)
    rw [dividedDifference_deriv_left hf hst, abs_div]
    have heq : |s - t| * (|deriv f s - dividedDifference f s t| / |s - t|) =
        |deriv f s - dividedDifference f s t| := by field_simp
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  deriv_right_bound := by
    intro s t hst
    have hd : |deriv f t| ≤ L := by
      simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lip' (f := f) (x₀ := t) hL
        (Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hLip u t))
    have hdd : |dividedDifference f s t| ≤ L := by
      simpa only [Real.norm_eq_abs] using dividedDifference_norm_le hL (hLip s t)
    rw [dividedDifference_deriv_right hf hst, abs_div]
    have heq : |s - t| * (|dividedDifference f s t - deriv f t| / |s - t|) =
        |dividedDifference f s t - deriv f t| := by field_simp
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)

end
end KernelSeq
