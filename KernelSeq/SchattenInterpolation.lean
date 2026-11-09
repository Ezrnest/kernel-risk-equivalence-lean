import KernelSeq.HilbertSchmidtIdeal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite-Schatten interpolation for actual Hilbert--Schmidt operators

Defines the singular-value power sums using the constructed compact spectral
theorem for `A* A`. The power-sum convergence and the `S₂`/operator-norm
interpolation bound are proved from the actual HS columns. This supplies the
interpolation step for the logarithmic Schatten bound.
-/

namespace KernelSeq

variable {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual compact positive operator whose eigenvalues are squared singular values. -/
noncomputable def hsSingularCovariance (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) : H →L[ℝ] H :=
  (hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b c)

theorem hsSingularCovariance_isCompact (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) : IsCompactOperator (hsSingularCovariance b c) :=
  (hilbertSchmidtOperator_isCompact b c).clm_comp (hilbertSchmidtOperator b c).adjoint

theorem hsSingularCovariance_isPositive (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) : (hsSingularCovariance b c).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

abbrev HSSingularIndex (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E) : Type _ :=
  CompactSpectralIndex (hsSingularCovariance b c)

noncomputable def hsSingularBasis (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E) :
    HilbertBasis (HSSingularIndex b c) ℝ H :=
  compactEigenbasis _ (hsSingularCovariance_isCompact b c)
    (hsSingularCovariance_isPositive b c).isSymmetric

theorem hsSingularValue_nonneg (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (i : HSSingularIndex b c) : 0 ≤ i.1 :=
  compactEigenvalue_nonneg _ (hsSingularCovariance_isCompact b c)
    (hsSingularCovariance_isPositive b c) i

theorem hsSingularValue_le_opNorm_sq (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (i : HSSingularIndex b c) :
    i.1 ≤ ‖hilbertSchmidtOperator b c‖ ^ 2 := by
  have h := (le_abs_self i.1).trans (compactEigenvalue_norm_le _
    (hsSingularCovariance_isCompact b c) (hsSingularCovariance_isPositive b c).isSymmetric i)
  simpa only [hsSingularCovariance, ContinuousLinearMap.norm_adjoint_comp_self, pow_two] using h

/-- Each singular coordinate has exactly its actual squared image norm. -/
theorem hsSingularBasis_image_norm_sq (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (i : HSSingularIndex b c) :
    ‖hilbertSchmidtOperator b c (hsSingularBasis b c i)‖ ^ 2 = i.1 := by
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  change inner ℝ (hsSingularBasis b c i)
    (hsSingularCovariance b c (hsSingularBasis b c i)) = _
  have he : hsSingularCovariance b c (hsSingularBasis b c i) = i.1 • hsSingularBasis b c i :=
    compactEigenbasis_eigen _ (hsSingularCovariance_isCompact b c)
      (hsSingularCovariance_isPositive b c).isSymmetric i
  rw [he]
  simp only [inner_smul_right, real_inner_self_eq_norm_sq,
    (hsSingularBasis b c).orthonormal.norm_eq_one, one_pow, mul_one]

/-- Squared singular values genuinely sum to the HS norm squared. -/
theorem hasSum_hsSquaredSingularValues (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    HasSum (fun i : HSSingularIndex b c => i.1) (‖c‖ ^ 2) := by
  have h := hilbertSchmidtOperator_basis_energy b (hsSingularBasis b c) c
  have hs := h.1.hasSum
  rw [h.2] at hs
  simpa only [hsSingularBasis_image_norm_sq] using hs

/-- The scalar power estimate used for every squared singular value. -/
theorem singularValue_power_le {t a p : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hta : t ≤ a ^ 2) (hp : 2 ≤ p) : t ^ (p / 2) ≤ a ^ (p - 2) * t := by
  have hr : 0 ≤ p / 2 - 1 := by linarith
  have hfactor : (a ^ 2) ^ (p / 2 - 1) = a ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    congr 1
    ring
  have htdecomp : t ^ (p / 2) = t ^ (p / 2 - 1) * t := by
    calc
      t ^ (p / 2) = t ^ ((p / 2 - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add_of_nonneg ht hr zero_le_one, Real.rpow_one]
  rw [htdecomp]
  exact mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow ht hta hr).trans_eq hfactor) ht

/-- All finite Schatten power sums with `p ≥ 2` converge, by comparison with
the actual squared singular values. -/
theorem summable_hsSingularPower (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    Summable (fun i : HSSingularIndex b c => i.1 ^ (p / 2)) := by
  apply Summable.of_nonneg_of_le
    (fun i => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _) _
    ((hasSum_hsSquaredSingularValues b c).summable.mul_left
      (‖hilbertSchmidtOperator b c‖ ^ (p - 2)))
  intro i
  exact singularValue_power_le (hsSingularValue_nonneg b c i) (norm_nonneg _)
    (hsSingularValue_le_opNorm_sq b c i) hp

theorem hsSingularPower_sum_le (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    (∑' i : HSSingularIndex b c, i.1 ^ (p / 2)) ≤
      ‖hilbertSchmidtOperator b c‖ ^ (p - 2) * ‖c‖ ^ 2 := by
  have h := (summable_hsSingularPower b c hp).tsum_le_tsum
    (fun i => singularValue_power_le (hsSingularValue_nonneg b c i) (norm_nonneg _)
      (hsSingularValue_le_opNorm_sq b c i) hp)
    ((hasSum_hsSquaredSingularValues b c).summable.mul_left
      (‖hilbertSchmidtOperator b c‖ ^ (p - 2)))
  simpa only [tsum_mul_left, (hasSum_hsSquaredSingularValues b c).tsum_eq] using h

/-- The actual singular-value Schatten quantity. Theorems below use `p ≥ 2`,
where convergence has already been proved rather than encoded as a premise. -/
noncomputable def hsSchattenNorm (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (p : ℝ) : ℝ :=
  (∑' i : HSSingularIndex b c, i.1 ^ (p / 2)) ^ (1 / p)

/-- Actual finite-Schatten interpolation, including zero operators and `p=2`. -/
theorem hsSchattenNorm_le_opNorm_mul_hsNorm (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b c p ≤
      ‖hilbertSchmidtOperator b c‖ ^ (1 - 2 / p) * ‖c‖ ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  have h := Real.rpow_le_rpow
    (tsum_nonneg (fun i : HSSingularIndex b c => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _))
    (hsSingularPower_sum_le b c hp) (one_div_nonneg.mpr hp0.le)
  change hsSchattenNorm b c p ≤ _ at h
  refine h.trans_eq ?_
  rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _),
    ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast ‖c‖ 2,
    ← Real.rpow_mul (norm_nonneg _)]
  have he : (p - 2) * (1 / p) = 1 - 2 / p := by
    calc
      _ = p / p - 2 / p := by ring
      _ = _ := by rw [div_self hp0.ne']
  rw [he]
  congr 2
  ring

theorem hsSchattenNorm_two (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b c 2 = ‖c‖ := by
  rw [hsSchattenNorm]
  norm_num only [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  rw [(hasSum_hsSquaredSingularValues b c).tsum_eq, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg _)]

/-- The explicit exponent used in the manuscript's endpoint optimization. -/
noncomputable def optimizedSchattenExponent (a b : ℝ) : ℝ :=
  2 * Real.log (Real.exp 1 + b / a)

theorem optimizedSchattenExponent_ge_two {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    2 ≤ optimizedSchattenExponent a b := by
  have he := Real.log_le_log (Real.exp_pos 1)
    (le_add_of_nonneg_right (div_nonneg hb ha.le) : Real.exp 1 ≤ Real.exp 1 + b / a)
  rw [Real.log_exp] at he
  dsimp only [optimizedSchattenExponent]
  linarith

/-- The interpolation factor is uniformly at most `e` for the chosen exponent. -/
theorem optimizedSchatten_ratio_rpow_le_exp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b / a) ^ (2 / optimizedSchattenExponent a b) ≤ Real.exp 1 := by
  let t := b / a
  let l := Real.log (Real.exp 1 + t)
  have ht : 0 < t := div_pos hb ha
  have hl : 1 ≤ l := by
    have h := optimizedSchattenExponent_ge_two ha hb.le
    dsimp only [optimizedSchattenExponent] at h
    dsimp only [l, t]
    linarith
  have hlpos : 0 < l := by linarith
  have he : 2 / optimizedSchattenExponent a b = 1 / l := by
    change 2 / (2 * l) = 1 / l
    field_simp
  change t ^ (2 / optimizedSchattenExponent a b) ≤ _
  rw [he, Real.rpow_def_of_pos ht]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log t ≤ l := Real.log_le_log ht
    (le_add_of_nonneg_left (Real.exp_pos 1).le)
  simpa only [div_eq_mul_inv, one_div, one_mul] using (div_le_one hlpos).mpr hlog

/-- A concrete endpoint exponent attains the logarithmic bound. No infimum
attainment, maximal singular value, or positive HS lower bound is assumed. -/
theorem exists_schatten_logarithmic_endpoint (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    ∃ p : ℝ, 2 ≤ p ∧ p * hsSchattenNorm b c p ≤
      2 * Real.exp 1 * ‖hilbertSchmidtOperator b c‖ *
        Real.log (Real.exp 1 + ‖c‖ / ‖hilbertSchmidtOperator b c‖) := by
  let a := ‖hilbertSchmidtOperator b c‖
  let d := ‖c‖
  by_cases ha : a = 0
  · have hc : c = 0 := by
      apply hilbertSchmidtOperator_injective b
      rw [map_zero]
      exact norm_eq_zero.mp ha
    refine ⟨2, le_rfl, ?_⟩
    rw [hc, hsSchattenNorm_two]
    simp
  · have hapos : 0 < a := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
    have hdpos : 0 < d := hapos.trans_le (hilbertSchmidtOperator_le b c)
    let p := optimizedSchattenExponent a d
    have hp : 2 ≤ p := optimizedSchattenExponent_ge_two hapos hdpos.le
    have hfactor : a ^ (1 - 2 / p) * d ^ (2 / p) = a * (d / a) ^ (2 / p) := by
      rw [Real.rpow_sub hapos, Real.rpow_one, Real.div_rpow hdpos.le hapos.le]
      ring
    refine ⟨p, hp, ?_⟩
    have hi := hsSchattenNorm_le_opNorm_mul_hsNorm b c hp
    change hsSchattenNorm b c p ≤ a ^ (1 - 2 / p) * d ^ (2 / p) at hi
    rw [hfactor] at hi
    calc
      p * hsSchattenNorm b c p ≤ p * (a * (d / a) ^ (2 / p)) :=
        mul_le_mul_of_nonneg_left hi (by linarith)
      _ ≤ p * (a * Real.exp 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (optimizedSchatten_ratio_rpow_le_exp hapos hdpos) hapos.le)
        (by linarith)
      _ = _ := by dsimp only [p, optimizedSchattenExponent, a, d]; ring

/-- The optimized deterministic Schatten endpoint bound with constant `2e`.
The right-hand side is automatically zero for the zero operator. -/
theorem schatten_logarithmic_endpoint_inf (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    sInf (Set.range (fun p : {p : ℝ // 2 ≤ p} => p.1 * hsSchattenNorm b c p.1)) ≤
      2 * Real.exp 1 * ‖hilbertSchmidtOperator b c‖ *
        Real.log (Real.exp 1 + ‖c‖ / ‖hilbertSchmidtOperator b c‖) := by
  obtain ⟨p, hp, hbound⟩ := exists_schatten_logarithmic_endpoint b c
  apply (csInf_le (show BddBelow (Set.range
    (fun p : {p : ℝ // 2 ≤ p} => p.1 * hsSchattenNorm b c p.1)) from ?_)
      (Set.mem_range_self (⟨p, hp⟩ : {p : ℝ // 2 ≤ p}))).trans hbound
  refine ⟨0, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact mul_nonneg (by linarith [r.2]) (Real.rpow_nonneg
    (tsum_nonneg (fun i : HSSingularIndex b c => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _)) _)

end KernelSeq
