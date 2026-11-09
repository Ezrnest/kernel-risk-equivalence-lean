import KernelSeq.FiniteMarcinkiewicz

/-!
# Finite-field weak-(1,1), strong-(2,2) interpolation

Normalized counting measure is used on the finite probability index.
The input and output are actual fields of finite operators. Spectral
truncation is performed separately at each point; no block embedding,
pinching estimate or interpolation certificate is assumed.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace KernelSeq
noncomputable section

variable {Ω ι H : Type*} [Fintype Ω] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/-- The actual normalized finite probability Schatten moment. Empty index
types give zero, consistent with the normalized finite-sum convention. -/
def finiteFieldSchattenMoment (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) (p : ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, hsSchattenNorm b (finiteOperatorColumns b (A ω)) p ^ p

/-- The normalized actual singular exceedance count of an operator field. -/
def finiteFieldSingularCount (A : Ω → H →L[ℝ] H) (t : ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, (finiteSingularCount (A ω) t : ℝ)

omit [FiniteDimensional ℝ H] in
theorem finiteFieldSchattenMoment_nonneg (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) (p : ℝ) : 0 ≤ finiteFieldSchattenMoment b A p := by
  unfold finiteFieldSchattenMoment
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun ω _ => Real.rpow_nonneg (hsSchattenNorm_nonneg b _ p) p)

omit [CompleteSpace H] in
theorem finiteFieldSingularCount_nonneg (A : Ω → H →L[ℝ] H) (t : ℝ) :
    0 ≤ finiteFieldSingularCount A t := by
  unfold finiteFieldSingularCount
  positivity

/-- The finite-field moment is exactly the normalized sum of the actual
singular moments. The exponent may be below two. -/
theorem finiteFieldSchattenMoment_eq_sum_singularValues (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    finiteFieldSchattenMoment b A p = (Fintype.card Ω : ℝ)⁻¹ *
      ∑ i : Ω × Fin (Module.finrank ℝ H), (A i.1).toLinearMap.singularValues i.2 ^ p := by
  unfold finiteFieldSchattenMoment
  simp_rw [finiteSchatten_rpow_eq_sum_singularValues b _ hp]
  rw [Fintype.sum_prod_type]

/-- True layer cake for the normalized finite probability field. -/
theorem finiteFieldSchattenMoment_eq_lintegral_count (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (finiteFieldSchattenMoment b A p) = ENNReal.ofReal p *
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (finiteFieldSingularCount A t) *
        ENNReal.ofReal (t ^ (p - 1)) := by
  have hw : 0 ≤ (Fintype.card Ω : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hm (ω : Ω) : Measurable (fun t : ℝ =>
      (finiteSingularCount (A ω) t : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 1))) := by
    have hc : Measurable (fun t : ℝ => (finiteSingularCount (A ω) t : ℝ≥0∞)) :=
      (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
        (finiteSingularCount_antitone (A ω)).measurable
    exact hc.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  have hfun : (fun t : ℝ => ENNReal.ofReal (finiteFieldSingularCount A t) *
      ENNReal.ofReal (t ^ (p - 1))) = fun t => ENNReal.ofReal ((Fintype.card Ω : ℝ)⁻¹) *
        ∑ ω, (finiteSingularCount (A ω) t : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 1)) := by
    funext t
    unfold finiteFieldSingularCount
    rw [ENNReal.ofReal_mul hw, ENNReal.ofReal_sum_of_nonneg (fun ω _ => Nat.cast_nonneg _),
      mul_assoc, Finset.sum_mul]
    simp only [ENNReal.ofReal_natCast]
  rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum _ (fun ω _ => hm ω)]
  unfold finiteFieldSchattenMoment
  rw [ENNReal.ofReal_mul hw, ENNReal.ofReal_sum_of_nonneg
    (fun ω _ => Real.rpow_nonneg (hsSchattenNorm_nonneg b _ p) p)]
  simp_rw [finiteSchatten_rpow_eq_lintegral_count b _ hp]
  rw [← Finset.mul_sum]
  ring

/-- Actual field counting is subadditive at split nonnegative thresholds. -/
theorem finiteFieldSingularCount_add_le (A B : Ω → H →L[ℝ] H) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    finiteFieldSingularCount (A + B) (s + t) ≤
      finiteFieldSingularCount A s + finiteFieldSingularCount B t := by
  unfold finiteFieldSingularCount
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro ω _
  exact_mod_cast finiteSingularCount_add_le (A ω) (B ω) hs ht

/-- Actual field counts satisfy the genuine moment estimate. -/
theorem finiteFieldSingularCount_mul_rpow_le (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {t p : ℝ} (ht : 0 ≤ t) (hp : 0 < p) :
    finiteFieldSingularCount A t * t ^ p ≤ finiteFieldSchattenMoment b A p := by
  unfold finiteFieldSingularCount finiteFieldSchattenMoment
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_le_sum fun ω _ => finiteSingularCount_mul_rpow_le b (A ω) ht hp

/-- Genuine pointwise strict-high singular truncation of a finite field. -/
def finiteFieldSingularHigh (A : Ω → H →L[ℝ] H) (t : ℝ) : Ω → H →L[ℝ] H :=
  fun ω => finiteSingularTruncation (A ω) (finiteSingularCount (A ω) t)

/-- Its actual complementary low field. -/
def finiteFieldSingularLow (A : Ω → H →L[ℝ] H) (t : ℝ) : Ω → H →L[ℝ] H :=
  A - finiteFieldSingularHigh A t

theorem finiteFieldSingularHigh_moment_one (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {t : ℝ} (ht : 0 ≤ t) :
    finiteFieldSchattenMoment b (finiteFieldSingularHigh A t) 1 = (Fintype.card Ω : ℝ)⁻¹ *
      ∑ i : Ω × Fin (Module.finrank ℝ H), if t < (A i.1).toLinearMap.singularValues i.2 then
        (A i.1).toLinearMap.singularValues i.2 else 0 := by
  unfold finiteFieldSchattenMoment finiteFieldSingularHigh
  simp_rw [finiteSingularHigh_rpow b _ ht (show 0 < (1 : ℝ) by norm_num), Real.rpow_one]
  rw [Fintype.sum_prod_type]

theorem finiteFieldSingularLow_moment_two (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {t : ℝ} (ht : 0 ≤ t) :
    finiteFieldSchattenMoment b (finiteFieldSingularLow A t) 2 = (Fintype.card Ω : ℝ)⁻¹ *
      ∑ i : Ω × Fin (Module.finrank ℝ H), if (A i.1).toLinearMap.singularValues i.2 ≤ t then
        (A i.1).toLinearMap.singularValues i.2 ^ 2 else 0 := by
  unfold finiteFieldSchattenMoment finiteFieldSingularLow finiteFieldSingularHigh
  simp only [Pi.sub_apply]
  simp_rw [finiteSingularLow_rpow b _ ht (show 0 < (2 : ℝ) by norm_num), Real.rpow_two]
  rw [Fintype.sum_prod_type]

/-- The genuine field-level count estimate uses only the two actual field
estimates and actual pointwise singular truncation. -/
theorem finiteFieldMarcinkiewicz_count_le (b : HilbertBasis ι ℝ H)
    (T : (Ω → H →L[ℝ] H) →ₗ[ℝ] (Ω → H →L[ℝ] H)) {K L : ℝ}
    (hweak : ∀ A t, 0 < t → t * finiteFieldSingularCount (T A) t ≤
      K * finiteFieldSchattenMoment b A 1)
    (hstrong : ∀ A, finiteFieldSchattenMoment b (T A) 2 ≤
      L ^ 2 * finiteFieldSchattenMoment b A 2)
    (A : Ω → H →L[ℝ] H) {t : ℝ} (ht : 0 < t) :
    finiteFieldSingularCount (T A) t ≤
      (2 * K / t) * finiteFieldSchattenMoment b (finiteFieldSingularHigh A t) 1 +
      (4 * L ^ 2 / t ^ 2) * finiteFieldSchattenMoment b (finiteFieldSingularLow A t) 2 := by
  let Ah := finiteFieldSingularHigh A t
  let Al := finiteFieldSingularLow A t
  have hdec : T A = T Ah + T Al := by
    rw [← map_add]
    congr 1
    change A = Ah + (A - Ah)
    abel
  have hc := finiteFieldSingularCount_add_le (T Ah) (T Al)
    (show 0 ≤ t / 2 by positivity) (show 0 ≤ t / 2 by positivity)
  rw [← hdec, show t / 2 + t / 2 = t by ring] at hc
  have hh := hweak Ah (t / 2) (by positivity)
  have hl := (finiteFieldSingularCount_mul_rpow_le b (T Al)
    (show 0 ≤ t / 2 by positivity) (show 0 < (2 : ℝ) by norm_num)).trans (hstrong Al)
  simp only [Real.rpow_two] at hl
  have hhh : finiteFieldSingularCount (T Ah) (t / 2) ≤
      2 * K / t * finiteFieldSchattenMoment b Ah 1 := by
    apply (mul_le_mul_iff_right₀ ht).mp
    have heq : t * (2 * K / t * finiteFieldSchattenMoment b Ah 1) =
      2 * (K * finiteFieldSchattenMoment b Ah 1) := by field_simp
    rw [heq]
    linarith
  have hll : finiteFieldSingularCount (T Al) (t / 2) ≤
      4 * L ^ 2 / t ^ 2 * finiteFieldSchattenMoment b Al 2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp
    have heq : t ^ 2 * (4 * L ^ 2 / t ^ 2 * finiteFieldSchattenMoment b Al 2) =
      4 * (L ^ 2 * finiteFieldSchattenMoment b Al 2) := by field_simp
    rw [heq]
    nlinarith
  exact hc.trans (add_le_add hhh hll)

private theorem high_density_sum {J : Type*} [Fintype J] (s : J → ℝ)
    {t : ℝ} (ht : 0 < t) (p C : ℝ) :
    (C / t * ∑ i, if t < s i then s i else 0) * t ^ (p - 1) =
      C * ∑ i, if t < s i then s i * t ^ (p - 2) else 0 := by
  classical
  rw [mul_assoc]
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
  rw [show C / t * (s i * t ^ (p - 1)) = C * (s i * (t ^ (p - 1) / t)) by ring, hr]

private theorem low_density_sum {J : Type*} [Fintype J] (s : J → ℝ)
    {t : ℝ} (ht : 0 < t) (p C : ℝ) :
    (C / t ^ 2 * ∑ i, if s i ≤ t then s i ^ 2 else 0) * t ^ (p - 1) =
      C * ∑ i, if s i ≤ t then s i ^ 2 * t ^ (p - 3) else 0 := by
  classical
  rw [mul_assoc]
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
  rw [show C / t ^ 2 * (s i ^ 2 * t ^ (p - 1)) =
    C * (s i ^ 2 * (t ^ (p - 1) / t ^ 2)) by ring, hr]

/-- The actual field count with the true layer-cake density is bounded by
the two explicitly integrable finite singular-value kernels. -/
theorem finiteFieldMarcinkiewicz_weighted_count_le (b : HilbertBasis ι ℝ H)
    (T : (Ω → H →L[ℝ] H) →ₗ[ℝ] (Ω → H →L[ℝ] H)) {K L : ℝ}
    (hweak : ∀ A t, 0 < t → t * finiteFieldSingularCount (T A) t ≤
      K * finiteFieldSchattenMoment b A 1)
    (hstrong : ∀ A, finiteFieldSchattenMoment b (T A) 2 ≤
      L ^ 2 * finiteFieldSchattenMoment b A 2)
    (A : Ω → H →L[ℝ] H) {t p : ℝ} (ht : 0 < t) :
    finiteFieldSingularCount (T A) t * t ^ (p - 1) ≤
      (2 * K * (Fintype.card Ω : ℝ)⁻¹) *
        (∑ i : Ω × Fin (Module.finrank ℝ H), if t < (A i.1).toLinearMap.singularValues i.2 then
          (A i.1).toLinearMap.singularValues i.2 * t ^ (p - 2) else 0) +
      (4 * L ^ 2 * (Fintype.card Ω : ℝ)⁻¹) *
        (∑ i : Ω × Fin (Module.finrank ℝ H), if (A i.1).toLinearMap.singularValues i.2 ≤ t then
          (A i.1).toLinearMap.singularValues i.2 ^ 2 * t ^ (p - 3) else 0) := by
  have hh := mul_le_mul_of_nonneg_right (finiteFieldMarcinkiewicz_count_le b T hweak hstrong A ht)
    (Real.rpow_nonneg ht.le (p - 1))
  rw [finiteFieldSingularHigh_moment_one b A ht.le, finiteFieldSingularLow_moment_two b A ht.le] at hh
  refine hh.trans_eq ?_
  rw [add_mul]
  congr 1
  · calc
      _ = (2 * K * (Fintype.card Ω : ℝ)⁻¹ / t *
          ∑ i : Ω × Fin (Module.finrank ℝ H), if t < (A i.1).toLinearMap.singularValues i.2 then
            (A i.1).toLinearMap.singularValues i.2 else 0) * t ^ (p - 1) := by ring
      _ = _ := high_density_sum (fun i : Ω × Fin (Module.finrank ℝ H) =>
        (A i.1).toLinearMap.singularValues i.2) ht p _
  · calc
      _ = (4 * L ^ 2 * (Fintype.card Ω : ℝ)⁻¹ / t ^ 2 *
          ∑ i : Ω × Fin (Module.finrank ℝ H), if (A i.1).toLinearMap.singularValues i.2 ≤ t then
            (A i.1).toLinearMap.singularValues i.2 ^ 2 else 0) * t ^ (p - 1) := by ring
      _ = _ := low_density_sum (fun i : Ω × Fin (Module.finrank ℝ H) =>
        (A i.1).toLinearMap.singularValues i.2) ht p _



/-- Genuine interpolation of actual finite probability operator fields,
with the same dimension-free constant. The only analytic inputs are the displayed weak-(1,1) and
strong-(2,2) estimates for the actual linear operator. -/
theorem finiteFieldMarcinkiewicz_moment_le (b : HilbertBasis ι ℝ H)
    (T : (Ω → H →L[ℝ] H) →ₗ[ℝ] (Ω → H →L[ℝ] H)) {K L : ℝ}
    (hK : 0 ≤ K) (_hL : 0 ≤ L)
    (hweak : ∀ A t, 0 < t → t * finiteFieldSingularCount (T A) t ≤
      K * finiteFieldSchattenMoment b A 1)
    (hstrong : ∀ A, finiteFieldSchattenMoment b (T A) 2 ≤
      L ^ 2 * finiteFieldSchattenMoment b A 2)
    (A : Ω → H →L[ℝ] H) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    finiteFieldSchattenMoment b (T A) p ≤
      (2 * K * p / (p - 1) + 4 * L ^ 2 * p / (2 - p)) *
        finiteFieldSchattenMoment b A p := by
  classical
  let s : Ω × Fin (Module.finrank ℝ H) → ℝ := fun i => (A i.1).toLinearMap.singularValues i.2
  let hi : Ω × Fin (Module.finrank ℝ H) → ℝ → ℝ := fun i t => if t < s i then s i * t ^ (p - 2) else 0
  let lo : Ω × Fin (Module.finrank ℝ H) → ℝ → ℝ := fun i t => if s i ≤ t then s i ^ 2 * t ^ (p - 3) else 0
  have hsn (i) : 0 ≤ s i := (A i.1).toLinearMap.singularValues_nonneg i.2
  let w : ℝ := (Fintype.card Ω : ℝ)⁻¹
  have hw : 0 ≤ w := inv_nonneg.mpr (Nat.cast_nonneg _)
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
  have h2K : 0 ≤ 2 * K * w := by positivity
  have h4L : 0 ≤ 4 * L ^ 2 * w := by positivity
  have hmajor : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ENNReal.ofReal (finiteFieldSingularCount (T A) t) * ENNReal.ofReal (t ^ (p - 1)) ≤
        ENNReal.ofReal (2 * K * w) * G t + ENNReal.ofReal (4 * L ^ 2 * w) * F t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hnhi := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hhin t ht i)
    have hnlo := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hlon t ht i)
    change _ ≤ ENNReal.ofReal (2 * K * w) * (∑ i, ENNReal.ofReal (hi i t)) +
      ENNReal.ofReal (4 * L ^ 2 * w) * (∑ i, ENNReal.ofReal (lo i t))
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ Finset.univ) => hhin t ht i),
      ← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ Finset.univ) => hlon t ht i),
      ← ENNReal.ofReal_mul h2K, ← ENNReal.ofReal_mul h4L,
      ← ENNReal.ofReal_add (mul_nonneg h2K hnhi) (mul_nonneg h4L hnlo),
      ← ENNReal.ofReal_mul (finiteFieldSingularCount_nonneg (T A) t)]
    exact ENNReal.ofReal_le_ofReal (finiteFieldMarcinkiewicz_weighted_count_le b T hweak hstrong A ht)
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
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (finiteFieldSchattenMoment_nonneg b A p))).mp
  rw [finiteFieldSchattenMoment_eq_lintegral_count b (T A) (by linarith)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0,
        (ENNReal.ofReal (2 * K * w) * G t + ENNReal.ofReal (4 * L ^ 2 * w) * F t) :=
      mul_le_mul_right (lintegral_mono_ae hmajor) _
    _ = ENNReal.ofReal p * (ENNReal.ofReal (2 * K * w) *
        ENNReal.ofReal ((∑ i, s i ^ p) / (p - 1)) + ENNReal.ofReal (4 * L ^ 2 * w) *
        ENNReal.ofReal ((∑ i, s i ^ p) / (2 - p))) := by
      rw [lintegral_add_left (measurable_const.mul hGm),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hGi, hFi, hsum1, hsum2]
    _ = _ := by
      rw [← ENNReal.ofReal_mul h2K, ← ENNReal.ofReal_mul h4L,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by linarith : 0 ≤ p),
        finiteFieldSchattenMoment_eq_sum_singularValues b A (by linarith)]
      congr 1
      dsimp only [s, w]
      ring

/-- Matching-outer-p norm on the finite probability operator field. -/
def finiteFieldSchattenNorm (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) (p : ℝ) : ℝ :=
  finiteFieldSchattenMoment b A p ^ p⁻¹

omit [FiniteDimensional ℝ H] in
theorem finiteFieldSchattenNorm_nonneg (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) (p : ℝ) : 0 ≤ finiteFieldSchattenNorm b A p :=
  Real.rpow_nonneg (finiteFieldSchattenMoment_nonneg b A p) _

omit [FiniteDimensional ℝ H] in
theorem finiteFieldSchattenNorm_rpow (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    finiteFieldSchattenNorm b A p ^ p = finiteFieldSchattenMoment b A p := by
  exact Real.rpow_inv_rpow (finiteFieldSchattenMoment_nonneg b A p) hp.ne'

/-- The interpolation conclusion in the genuine matching-outer-p field
norm. No L2-to-Lp transfer or additional loss of p is inserted. -/
theorem finiteFieldMarcinkiewicz_norm_le (b : HilbertBasis ι ℝ H)
    (T : (Ω → H →L[ℝ] H) →ₗ[ℝ] (Ω → H →L[ℝ] H)) {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hweak : ∀ A t, 0 < t → t * finiteFieldSingularCount (T A) t ≤
      K * finiteFieldSchattenMoment b A 1)
    (hstrong : ∀ A, finiteFieldSchattenMoment b (T A) 2 ≤
      L ^ 2 * finiteFieldSchattenMoment b A 2)
    (A : Ω → H →L[ℝ] H) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    finiteFieldSchattenNorm b (T A) p ≤
      (2 * K * p / (p - 1) + 4 * L ^ 2 * p / (2 - p)) ^ p⁻¹ *
        finiteFieldSchattenNorm b A p := by
  have hp0 : 0 < p := by linarith
  have hC : 0 ≤ 2 * K * p / (p - 1) + 4 * L ^ 2 * p / (2 - p) := by positivity
  have h := Real.rpow_le_rpow (finiteFieldSchattenMoment_nonneg b (T A) p)
    (finiteFieldMarcinkiewicz_moment_le b T hK hL hweak hstrong A hp1 hp2)
    (inv_nonneg.mpr hp0.le)
  simpa only [finiteFieldSchattenNorm, Real.mul_rpow hC
    (finiteFieldSchattenMoment_nonneg b A p)] using h

end
end KernelSeq
