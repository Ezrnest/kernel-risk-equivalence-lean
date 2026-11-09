import KernelSeq.WalshTransformDuality
import KernelSeq.DyadicSchattenEndpoint
import KernelSeq.WalshGeneralWeakType

/-!
# Actual matching-exponent Walsh Schatten bounds

Finite-field interpolation and genuine trace duality retain one power of
the large exponent. The actual weak-type transform theorem is supplied by
the proved finite Walsh decomposition, rather than by a UMD certificate.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

private theorem marcinkiewicz64_dual_coefficient_le {p q : ℝ}
    (hpq : p.HolderConjugate q) (hq : 4 ≤ q) :
    (2 * 64 * p / (p - 1) + 4 * (1 : ℝ) ^ 2 * p / (2 - p)) ^ p⁻¹ ≤ 130 * q := by
  have hp1 : 1 < p := hpq.lt
  have hp2 : p < 2 := by
    rw [hpq.symm.conjugate_eq]
    apply (div_lt_iff₀ (show 0 < q - 1 by linarith)).mpr
    linarith
  have hr1 : p / (p - 1) = q := hpq.conjugate_eq.symm
  have hr2 : p / (2 - p) = q / (q - 2) := by
    apply (div_eq_div_iff (show 2 - p ≠ 0 by linarith) (show q - 2 ≠ 0 by linarith)).mpr
    have hm := hpq.symm.sub_one_mul_conj
    nlinarith
  have heq : 2 * 64 * p / (p - 1) + 4 * (1 : ℝ) ^ 2 * p / (2 - p) =
      128 * q + 4 * (q / (q - 2)) := by
    calc
      _ = 128 * (p / (p - 1)) + 4 * (p / (2 - p)) := by ring
      _ = _ := by rw [hr1, hr2]
  have hrat : q / (q - 2) ≤ 2 := by
    apply (div_le_iff₀ (show 0 < q - 2 by linarith)).mpr
    linarith
  have hC0 : 0 ≤ 2 * 64 * p / (p - 1) + 4 * (1 : ℝ) ^ 2 * p / (2 - p) := by positivity
  have hC : 2 * 64 * p / (p - 1) + 4 * (1 : ℝ) ^ 2 * p / (2 - p) ≤ 130 * q := by
    rw [heq]
    linarith
  have hpinv : p⁻¹ ≤ 1 := by linarith [hpq.inv_add_inv_eq_one, hpq.symm.inv_pos]
  exact (Real.rpow_le_rpow hC0 hC hpq.inv_pos.le).trans
    (Real.rpow_le_self_of_one_le (by linarith) hpinv)

variable {n : ℕ} {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H] [Fintype ι]

/-- The exact actual M2 contraction gives its matching-L2 norm version. -/
theorem walshPrefixTransformLinearMap_norm_two_le (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) :
    finiteFieldSchattenNorm b (walshPrefixTransformLinearMap σ N F) 2 ≤ finiteFieldSchattenNorm b F 2 := by
  have h := walshPrefixTransformLinearMap_moment_two_le b F σ hσ N
  have hT := finiteFieldSchattenNorm_rpow b (walshPrefixTransformLinearMap σ N F) (by norm_num : 0 < (2 : ℝ))
  have hF := finiteFieldSchattenNorm_rpow b F (by norm_num : 0 < (2 : ℝ))
  simp only [Real.rpow_two] at hT hF
  apply (sq_le_sq₀ (finiteFieldSchattenNorm_nonneg b _ 2) (finiteFieldSchattenNorm_nonneg b _ 2)).mp
  simpa only [hT, hF] using h

variable {Ω : Type*} [Fintype Ω]

omit [FiniteDimensional ℝ H] in
private theorem fieldTrace_add_left (b : HilbertBasis ι ℝ H)
    (A B D : Ω → H →L[ℝ] H) :
    finiteFieldTracePairing b (A + B) D = finiteFieldTracePairing b A D + finiteFieldTracePairing b B D := by
  simp only [finiteFieldTracePairing, Pi.add_apply, finiteOperatorColumns_trace_inner,
    finiteOperatorColumns_add, inner_add_left, Finset.sum_add_distrib, mul_add]

/-- The actual matching-q field norm satisfies the triangle inequality
for q ≥ 2, proved directly by its genuine norming field and trace Holder. -/
theorem finiteFieldSchattenNorm_add_le (b : HilbertBasis ι ℝ H)
    (A B : Ω → H →L[ℝ] H) {q : ℝ} (hq : 2 ≤ q) :
    finiteFieldSchattenNorm b (A + B) q ≤ finiteFieldSchattenNorm b A q + finiteFieldSchattenNorm b B q := by
  have hpq := (Real.HolderConjugate.conjExponent (by linarith : 1 < q)).symm
  obtain ⟨D, hDn, hDt⟩ := exists_finiteFieldSchatten_norming b (A + B) hpq hq
  have hpart (F : Ω → H →L[ℝ] H) : finiteFieldTracePairing b F D ≤ finiteFieldSchattenNorm b F q := by
    calc
      _ = finiteFieldTracePairing b D F := finiteFieldTracePairing_comm b F D
      _ ≤ |finiteFieldTracePairing b D F| := le_abs_self _
      _ ≤ finiteFieldSchattenNorm b D (Real.conjExponent q) * finiteFieldSchattenNorm b F q :=
        finiteFieldTracePairing_holder b D F hpq hq
      _ ≤ 1 * finiteFieldSchattenNorm b F q :=
        mul_le_mul_of_nonneg_right hDn (finiteFieldSchattenNorm_nonneg b F q)
      _ = _ := one_mul _
  rw [← hDt, fieldTrace_add_left]
  exact add_le_add (hpart A) (hpart B)

omit [FiniteDimensional ℝ H] in
theorem finiteFieldSchattenNorm_zero (b : HilbertBasis ι ℝ H) {q : ℝ} (hq : 2 ≤ q) :
    finiteFieldSchattenNorm b (0 : Ω → H →L[ℝ] H) q = 0 := by
  have h := finiteFieldSchattenNorm_smul b 0 (0 : Ω → H →L[ℝ] H) hq
  simpa only [zero_smul, abs_zero, zero_mul] using h

theorem finiteFieldSchattenNorm_sum_le {J : Type*} (b : HilbertBasis ι ℝ H)
    (s : Finset J) (F : J → Ω → H →L[ℝ] H) {q : ℝ} (hq : 2 ≤ q) :
    finiteFieldSchattenNorm b (∑ j ∈ s, F j) q ≤ ∑ j ∈ s, finiteFieldSchattenNorm b (F j) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, finiteFieldSchattenNorm_zero b hq, le_refl]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (finiteFieldSchattenNorm_add_le b (F j) (∑ k ∈ s, F k) hq).trans
      (add_le_add le_rfl ih)

/-- The proved arbitrary-operator Walsh weak-(1,1) theorem in the exact
normalized-field format consumed by the genuine interpolation theorem. -/
theorem walshPrefixTransformLinearMap_weak_one (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ)
    {t : ℝ} (ht : 0 < t) :
    t * finiteFieldSingularCount (walshPrefixTransformLinearMap σ N F) t ≤
      64 * finiteFieldSchattenMoment b F 1 := by
  rw [walshPrefixTransformLinearMap_apply]
  unfold finiteFieldSingularCount finiteFieldSchattenMoment
  simp only [Real.rpow_one]
  have h := mul_le_mul_of_nonneg_left (sum_walshPrefixTransform_weak_one b F σ hσ N ht)
    (show 0 ≤ (Fintype.card (WalshCube n) : ℝ)⁻¹ by positivity)
  nlinarith only [h]

/-- True matching-Lq Walsh bound for arbitrary finite operator fields.
The weak-(1,1), L2 and duality inputs have all been proved for this map. -/
theorem walshPrefixTransformLinearMap_norm_le_of_four_le (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ)
    {q : ℝ} (hq : 4 ≤ q) :
    finiteFieldSchattenNorm b (walshPrefixTransformLinearMap σ N F) q ≤
      (130 * q) * finiteFieldSchattenNorm b F q := by
  have hq2 : 2 ≤ q := by linarith
  have hpq := (Real.HolderConjugate.conjExponent (by linarith : 1 < q)).symm
  have hp2 : Real.conjExponent q < 2 := by
    unfold Real.conjExponent
    apply (div_lt_iff₀ (show 0 < q - 1 by linarith)).mpr
    linarith
  have h := finiteFieldMarcinkiewicz_dual_norm_le b (walshPrefixTransformLinearMap σ N)
    (show 0 ≤ (64 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num) hpq hq2 hp2
    (fun G _ ht => walshPrefixTransformLinearMap_weak_one b G σ hσ N ht)
    (fun G => by simpa only [one_pow, one_mul] using walshPrefixTransformLinearMap_moment_two_le b G σ hσ N)
    (fun G K => walshPrefixTransformLinearMap_trace_selfadjoint b G K σ N) F
  exact h.trans (mul_le_mul_of_nonneg_right (marcinkiewicz64_dual_coefficient_le hpq hq)
    (finiteFieldSchattenNorm_nonneg b F q))

/-- The actual dyadic matching-exponent estimate keeps exactly one power
of q. It includes the Hilbert endpoint q=2 and all finite Walsh cubes. -/
theorem walshPrefixTransformLinearMap_dyadic_norm_le (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N m : ℕ) :
    finiteFieldSchattenNorm b (walshPrefixTransformLinearMap σ N F) (dyadicSchattenExponent m) ≤
      (130 * dyadicSchattenExponent m) * finiteFieldSchattenNorm b F (dyadicSchattenExponent m) := by
  cases m with
  | zero =>
    simp only [dyadicSchattenExponent, zero_add, pow_one]
    have h := walshPrefixTransformLinearMap_norm_two_le b F σ hσ N
    nlinarith [finiteFieldSchattenNorm_nonneg b F 2]
  | succ m =>
    apply walshPrefixTransformLinearMap_norm_le_of_four_le b F σ hσ N
    unfold dyadicSchattenExponent
    rw [pow_succ, pow_succ]
    have hpow : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith

/-- Equivalent actual moment formulation, for use with finite probability
and Riesz-product arguments. No transform norm certificate is an input. -/
theorem walshPrefixTransformLinearMap_dyadic_moment_le (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N m : ℕ) :
    finiteFieldSchattenMoment b (walshPrefixTransformLinearMap σ N F) (dyadicSchattenExponent m) ≤
      (130 * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        finiteFieldSchattenMoment b F (dyadicSchattenExponent m) := by
  have hq := dyadicSchattenExponent_ge_two m
  have hq0 : 0 < dyadicSchattenExponent m := by linarith
  have h := Real.rpow_le_rpow (finiteFieldSchattenNorm_nonneg b _ _)
    (walshPrefixTransformLinearMap_dyadic_norm_le b F σ hσ N m) hq0.le
  rwa [Real.mul_rpow (by positivity) (finiteFieldSchattenNorm_nonneg b F _),
    finiteFieldSchattenNorm_rpow b _ hq0, finiteFieldSchattenNorm_rpow b F hq0] at h

end
end KernelSeq
