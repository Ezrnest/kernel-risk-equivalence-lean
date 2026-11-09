import KernelSeq.FiniteSingularTruncationNorms
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Finite weak-(1,1) and strong-(2,2) interpolation

The actual singular-value truncation supplies the high and low pieces.
The weak and strong estimates are explicit inputs for a genuine linear
operator; no interpolation estimate is assumed.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace KernelSeq
noncomputable section

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/-- A true singular truncation gives the distribution estimate used in
weak-(1,1), strong-(2,2) interpolation. Threshold equality belongs to the
low part, and all zero singular values are retained correctly. -/
theorem finiteMarcinkiewicz_count_le (b : HilbertBasis ι ℝ H)
    (T : (H →L[ℝ] H) →ₗ[ℝ] (H →L[ℝ] H)) {K L : ℝ}
    (hweak : ∀ A t, 0 < t → t * (finiteSingularCount (T A) t : ℝ) ≤
      K * hsSchattenNorm b (finiteOperatorColumns b A) 1)
    (hstrong : ∀ A, hsSchattenNorm b (finiteOperatorColumns b (T A)) 2 ≤
      L * hsSchattenNorm b (finiteOperatorColumns b A) 2)
    (A : H →L[ℝ] H) {t : ℝ} (ht : 0 < t) :
    (finiteSingularCount (T A) t : ℝ) ≤
      (2 * K / t) * (∑ i : Fin (Module.finrank ℝ H),
        if t < A.toLinearMap.singularValues i then A.toLinearMap.singularValues i else 0) +
      (4 * L ^ 2 / t ^ 2) * (∑ i : Fin (Module.finrank ℝ H),
        if A.toLinearMap.singularValues i ≤ t then A.toLinearMap.singularValues i ^ 2 else 0) := by
  classical
  let Ah := finiteSingularTruncation A (finiteSingularCount A t)
  let Al := A - Ah
  have hdec : T A = T Ah + T Al := by rw [← map_add]; congr 1; dsimp only [Al]; abel
  have hc := finiteSingularCount_add_le (T Ah) (T Al)
    (show 0 ≤ t / 2 by positivity) (show 0 ≤ t / 2 by positivity)
  have hc' : (finiteSingularCount (T A) t : ℝ) ≤
      (finiteSingularCount (T Ah) (t / 2) : ℝ) +
        (finiteSingularCount (T Al) (t / 2) : ℝ) := by
    rw [← hdec, show t / 2 + t / 2 = t by ring] at hc
    exact_mod_cast hc
  have hh := hweak Ah (t / 2) (by positivity)
  have hl := finiteSingularCount_mul_rpow_le b (T Al)
    (show 0 ≤ t / 2 by positivity) (show 0 < (2 : ℝ) by norm_num)
  have hs := hstrong Al
  have hsn := hsSchattenNorm_nonneg b (finiteOperatorColumns b (T Al)) 2
  have haln := hsSchattenNorm_nonneg b (finiteOperatorColumns b Al) 2
  have hsq : hsSchattenNorm b (finiteOperatorColumns b (T Al)) 2 ^ (2 : ℕ) ≤
      L ^ 2 * hsSchattenNorm b (finiteOperatorColumns b Al) 2 ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (L * hsSchattenNorm b (finiteOperatorColumns b Al) 2 -
      hsSchattenNorm b (finiteOperatorColumns b (T Al)) 2)]
  have hhigh := finiteSingularHigh_rpow b A ht.le (show 0 < (1 : ℝ) by norm_num)
  have hlow := finiteSingularLow_rpow b A ht.le (show 0 < (2 : ℝ) by norm_num)
  simp only [Real.rpow_one] at hhigh
  simp only [Real.rpow_two] at hlow hl
  change hsSchattenNorm b (finiteOperatorColumns b Ah) 1 = _ at hhigh
  change hsSchattenNorm b (finiteOperatorColumns b Al) 2 ^ (2 : ℕ) = _ at hlow
  rw [← hhigh, ← hlow]
  have hhh : (finiteSingularCount (T Ah) (t / 2) : ℝ) ≤
      2 * K / t * hsSchattenNorm b (finiteOperatorColumns b Ah) 1 := by
    apply (mul_le_mul_iff_right₀ ht).mp
    have heq : t * (2 * K / t * hsSchattenNorm b (finiteOperatorColumns b Ah) 1) =
      2 * (K * hsSchattenNorm b (finiteOperatorColumns b Ah) 1) := by field_simp
    rw [heq]
    linarith
  have hll : (finiteSingularCount (T Al) (t / 2) : ℝ) ≤
      4 * L ^ 2 / t ^ 2 * hsSchattenNorm b (finiteOperatorColumns b Al) 2 ^ (2 : ℕ) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp
    have heq : t ^ 2 * (4 * L ^ 2 / t ^ 2 * hsSchattenNorm b (finiteOperatorColumns b Al) 2 ^ (2 : ℕ)) =
      4 * (L ^ 2 * hsSchattenNorm b (finiteOperatorColumns b Al) 2 ^ (2 : ℕ)) := by field_simp
    rw [heq]
    nlinarith
  exact hc'.trans (add_le_add hhh hll)

/-- The genuine high-piece power integral, including a zero singular value. -/
theorem marcinkiewicz_high_lintegral {s p : ℝ} (hs : 0 ≤ s) (hp : 1 < p) :
    ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (if t < s then s * t ^ (p - 2) else 0) =
      ENNReal.ofReal (s ^ p / (p - 1)) := by
  by_cases hs0 : s = 0
  · subst s
    simp [Real.zero_rpow (show p ≠ 0 by linarith)]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hfun : (fun t : ℝ => ENNReal.ofReal (if t < s then s * t ^ (p - 2) else 0)) =
      (Iio s).indicator (fun t => ENNReal.ofReal s * ENNReal.ofReal (t ^ (p - 2))) := by
    funext t
    by_cases ht : t < s <;> simp [ht, ENNReal.ofReal_mul hs]
  rw [hfun, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Iio_inter_Ioi, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hi : IntegrableOn (fun t : ℝ => t ^ (p - 2)) (Ioo 0 s) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hspos).mpr (by linarith)
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 s)] (fun t : ℝ => t ^ (p - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, ← ENNReal.ofReal_mul hs]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs,
    integral_rpow (Or.inl (by linarith : -1 < p - 2))]
  have hexp : p - 2 + 1 = p - 1 := by ring
  rw [hexp, Real.zero_rpow (by linarith : p - 1 ≠ 0), sub_zero]
  have hmul : s * s ^ (p - 1) = s ^ p := by
    calc
      _ = s ^ (1 : ℝ) * s ^ (p - 1) := by rw [Real.rpow_one]
      _ = s ^ (1 + (p - 1)) := (Real.rpow_add hspos _ _).symm
      _ = _ := by congr 1; ring
  rw [← mul_div_assoc, hmul]

/-- The genuine low-piece tail integral; multiplication by a zero singular
value is handled before invoking the improper power integral. -/
theorem marcinkiewicz_low_lintegral {s p : ℝ} (hs : 0 ≤ s) (hp : p < 2) (hp0 : 0 < p) :
    ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (if s ≤ t then s ^ 2 * t ^ (p - 3) else 0) =
      ENNReal.ofReal (s ^ p / (2 - p)) := by
  by_cases hs0 : s = 0
  · subst s
    simp [Real.zero_rpow hp0.ne']
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hfun : (fun t : ℝ => ENNReal.ofReal (if s ≤ t then s ^ 2 * t ^ (p - 3) else 0)) =
      (Ici s).indicator (fun t => ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (t ^ (p - 3))) := by
    funext t
    by_cases ht : s ≤ t <;> simp [ht, ENNReal.ofReal_mul (sq_nonneg s)]
  have hset : Ici s ∩ Ioi 0 = Ici s := inter_eq_left.mpr (fun t ht => hspos.trans_le ht)
  rw [hfun, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    hset, Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := s)).symm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hi := integrableOn_Ioi_rpow_of_lt (show p - 3 < -1 by linarith) hspos
  have hn : 0 ≤ᵐ[volume.restrict (Ioi s)] (fun t : ℝ => t ^ (p - 3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hspos.trans ht).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, ← ENNReal.ofReal_mul (sq_nonneg s)]
  congr 1
  rw [integral_Ioi_rpow_of_lt (show p - 3 < -1 by linarith) hspos]
  have hexp : p - 3 + 1 = p - 2 := by ring
  rw [hexp, Real.rpow_sub hspos, Real.rpow_two]
  rw [show 2 - p = -(p - 2) by ring]
  field_simp [hs0]

/-- Multiplying the actual count bound by the layer-cake density yields
the two integrable scalar kernels, without any interpolation certificate. -/
theorem finiteMarcinkiewicz_weighted_count_le (b : HilbertBasis ι ℝ H)
    (T : (H →L[ℝ] H) →ₗ[ℝ] (H →L[ℝ] H)) {K L : ℝ}
    (hweak : ∀ A t, 0 < t → t * (finiteSingularCount (T A) t : ℝ) ≤
      K * hsSchattenNorm b (finiteOperatorColumns b A) 1)
    (hstrong : ∀ A, hsSchattenNorm b (finiteOperatorColumns b (T A)) 2 ≤
      L * hsSchattenNorm b (finiteOperatorColumns b A) 2)
    (A : H →L[ℝ] H) {t p : ℝ} (ht : 0 < t) :
    (finiteSingularCount (T A) t : ℝ) * t ^ (p - 1) ≤
      2 * K * (∑ i : Fin (Module.finrank ℝ H),
        if t < A.toLinearMap.singularValues i then A.toLinearMap.singularValues i * t ^ (p - 2) else 0) +
      4 * L ^ 2 * (∑ i : Fin (Module.finrank ℝ H),
        if A.toLinearMap.singularValues i ≤ t then A.toLinearMap.singularValues i ^ 2 * t ^ (p - 3) else 0) := by
  have hh := mul_le_mul_of_nonneg_right (finiteMarcinkiewicz_count_le b T hweak hstrong A ht)
    (Real.rpow_nonneg ht.le (p - 1))
  refine hh.trans_eq ?_
  rw [add_mul]
  congr 1
  · rw [mul_assoc]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    swap
    · simp only [zero_mul, mul_zero]
    have hr : t ^ (p - 1) / t = t ^ (p - 2) := by
      calc
        _ = t ^ (p - 1) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = t ^ ((p - 1) - 1) := (Real.rpow_sub ht _ _).symm
        _ = _ := by congr 1; ring
    rw [show 2 * K / t * (A.toLinearMap.singularValues i * t ^ (p - 1)) =
      2 * K * (A.toLinearMap.singularValues i * (t ^ (p - 1) / t)) by ring, hr]
  · rw [mul_assoc]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    swap
    · simp only [zero_mul, mul_zero]
    have hr : t ^ (p - 1) / t ^ (2 : ℕ) = t ^ (p - 3) := by
      rw [← Real.rpow_two, ← Real.rpow_sub ht]
      congr 1
      ring
    rw [show 4 * L ^ 2 / t ^ 2 * (A.toLinearMap.singularValues i ^ 2 * t ^ (p - 1)) =
      4 * L ^ 2 * (A.toLinearMap.singularValues i ^ 2 * (t ^ (p - 1) / t ^ 2)) by ring, hr]

/-- Genuine finite Marcinkiewicz interpolation, with an explicit dimension
free constant. The only analytic inputs are the displayed weak-(1,1) and
strong-(2,2) estimates for the actual linear operator. -/
theorem finiteMarcinkiewicz_rpow_le (b : HilbertBasis ι ℝ H)
    (T : (H →L[ℝ] H) →ₗ[ℝ] (H →L[ℝ] H)) {K L : ℝ}
    (hK : 0 ≤ K) (_hL : 0 ≤ L)
    (hweak : ∀ A t, 0 < t → t * (finiteSingularCount (T A) t : ℝ) ≤
      K * hsSchattenNorm b (finiteOperatorColumns b A) 1)
    (hstrong : ∀ A, hsSchattenNorm b (finiteOperatorColumns b (T A)) 2 ≤
      L * hsSchattenNorm b (finiteOperatorColumns b A) 2)
    (A : H →L[ℝ] H) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    hsSchattenNorm b (finiteOperatorColumns b (T A)) p ^ p ≤
      (2 * K * p / (p - 1) + 4 * L ^ 2 * p / (2 - p)) *
        hsSchattenNorm b (finiteOperatorColumns b A) p ^ p := by
  classical
  let s : Fin (Module.finrank ℝ H) → ℝ := fun i => A.toLinearMap.singularValues i
  let hi : Fin (Module.finrank ℝ H) → ℝ → ℝ := fun i t => if t < s i then s i * t ^ (p - 2) else 0
  let lo : Fin (Module.finrank ℝ H) → ℝ → ℝ := fun i t => if s i ≤ t then s i ^ 2 * t ^ (p - 3) else 0
  have hsn (i) : 0 ≤ s i := A.toLinearMap.singularValues_nonneg i
  have hhin (t) (ht : 0 < t) (i) : 0 ≤ hi i t := by
    dsimp only [hi]
    split_ifs
    · exact mul_nonneg (hsn i) (Real.rpow_nonneg ht.le _)
    · exact le_rfl
  have hlon (t) (ht : 0 < t) (i) : 0 ≤ lo i t := by
    dsimp only [lo]
    split_ifs <;> positivity
  have hhim (i) : Measurable (fun t => ENNReal.ofReal (hi i t)) := by
    apply ENNReal.measurable_ofReal.comp
    exact (measurable_const.mul (measurable_id.pow_const _)).ite
      (measurableSet_lt measurable_id measurable_const) measurable_const
  have hlom (i) : Measurable (fun t => ENNReal.ofReal (lo i t)) := by
    apply ENNReal.measurable_ofReal.comp
    exact (measurable_const.mul (measurable_id.pow_const _)).ite
      (measurableSet_le measurable_const measurable_id) measurable_const
  let G : ℝ → ℝ≥0∞ := fun t => ∑ i, ENNReal.ofReal (hi i t)
  let F : ℝ → ℝ≥0∞ := fun t => ∑ i, ENNReal.ofReal (lo i t)
  have hGm : Measurable G := Finset.measurable_sum _ fun i _ => hhim i
  have hFm : Measurable F := Finset.measurable_sum _ fun i _ => hlom i
  have hGi : ∫⁻ t in Ioi 0, G t = ∑ i, ENNReal.ofReal (s i ^ p / (p - 1)) := by
    rw [show (∫⁻ t in Ioi 0, G t) = ∑ i, ∫⁻ t in Ioi 0, ENNReal.ofReal (hi i t) from
      lintegral_finsetSum _ (fun i _ => hhim i)]
    apply Finset.sum_congr rfl
    intro i _
    exact marcinkiewicz_high_lintegral (hsn i) hp1
  have hFi : ∫⁻ t in Ioi 0, F t = ∑ i, ENNReal.ofReal (s i ^ p / (2 - p)) := by
    rw [show (∫⁻ t in Ioi 0, F t) = ∑ i, ∫⁻ t in Ioi 0, ENNReal.ofReal (lo i t) from
      lintegral_finsetSum _ (fun i _ => hlom i)]
    apply Finset.sum_congr rfl
    intro i _
    exact marcinkiewicz_low_lintegral (hsn i) hp2 (by linarith)
  have h2K : 0 ≤ 2 * K := by positivity
  have h4L : 0 ≤ 4 * L ^ 2 := by positivity
  have hmajor : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (finiteSingularCount (T A) t : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 1)) ≤
        ENNReal.ofReal (2 * K) * G t + ENNReal.ofReal (4 * L ^ 2) * F t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hnhi := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hhin t ht i)
    have hnlo := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hlon t ht i)
    change _ ≤ ENNReal.ofReal (2 * K) * (∑ i, ENNReal.ofReal (hi i t)) +
      ENNReal.ofReal (4 * L ^ 2) * (∑ i, ENNReal.ofReal (lo i t))
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ Finset.univ) => hhin t ht i),
      ← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ Finset.univ) => hlon t ht i),
      ← ENNReal.ofReal_mul h2K, ← ENNReal.ofReal_mul h4L,
      ← ENNReal.ofReal_add (mul_nonneg h2K hnhi) (mul_nonneg h4L hnlo),
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (finiteMarcinkiewicz_weighted_count_le b T hweak hstrong A ht)
  have hsum1 : (∑ i, ENNReal.ofReal (s i ^ p / (p - 1))) =
      ENNReal.ofReal ((∑ i, s i ^ p) / (p - 1)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      div_nonneg (Real.rpow_nonneg (hsn i) p) (by linarith)), Finset.sum_div]
  have hsum2 : (∑ i, ENNReal.ofReal (s i ^ p / (2 - p))) =
      ENNReal.ofReal ((∑ i, s i ^ p) / (2 - p)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      div_nonneg (Real.rpow_nonneg (hsn i) p) (by linarith)), Finset.sum_div]
  have hsum0 : 0 ≤ ∑ i, s i ^ p := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hsn i) p
  have hC : 0 ≤ 2 * K * p / (p - 1) + 4 * L ^ 2 * p / (2 - p) := by positivity
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Real.rpow_nonneg
    (hsSchattenNorm_nonneg b (finiteOperatorColumns b A) p) p))).mp
  rw [finiteSchatten_rpow_eq_lintegral_count b (T A) (by linarith)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0,
        (ENNReal.ofReal (2 * K) * G t + ENNReal.ofReal (4 * L ^ 2) * F t) :=
      mul_le_mul_right (lintegral_mono_ae hmajor) _
    _ = ENNReal.ofReal p * (ENNReal.ofReal (2 * K) *
        ENNReal.ofReal ((∑ i, s i ^ p) / (p - 1)) + ENNReal.ofReal (4 * L ^ 2) *
        ENNReal.ofReal ((∑ i, s i ^ p) / (2 - p))) := by
      rw [lintegral_add_left (measurable_const.mul hGm),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hGi, hFi, hsum1, hsum2]
    _ = _ := by
      rw [← ENNReal.ofReal_mul h2K, ← ENNReal.ofReal_mul h4L,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by linarith : 0 ≤ p),
        finiteSchatten_rpow_eq_sum_singularValues b A (by linarith)]
      congr 1
      dsimp only [s]
      ring

end
end KernelSeq
