import KernelSeq.HighDimensionalKRRScales
import KernelSeq.SpherePolynomialLayerDimension

/-!
# Ridge bias and variance on the spherical degree split
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology ContDiff BigOperators
noncomputable section

theorem ridge_shrinkage_eq {lam t : ℝ} :
    ResidualFilter.shrinkage (ResidualFilter.ridge lam) t = t/(t+lam) := by
  unfold ResidualFilter.shrinkage ResidualFilter.ridge
  ring

theorem ridge_shrinkage_sq_le_trace_weight {lam t U : ℝ}
    (hlam : 0 < lam) (ht : 0 ≤ t) (hU : t ≤ U) :
    ResidualFilter.shrinkage (ResidualFilter.ridge lam) t^2 ≤ (U/lam^2)*t := by
  rw [ridge_shrinkage_eq]
  have hden : 0 < t+lam := add_pos_of_nonneg_of_pos ht hlam
  have hq := div_le_div_of_nonneg_left ht hlam (show lam ≤ t+lam by linarith)
  calc
    (t/(t+lam))^2 ≤ (t/lam)^2 :=
      pow_le_pow_left₀ (div_nonneg ht hden.le) hq 2
    _ = (t*t)/(lam^2) := by rw [div_pow, pow_two t]
    _ ≤ (U*t)/(lam^2) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hU ht) (sq_nonneg _)
    _ = _ := by ring

theorem ridge_degree_variance_le (D : ℕ → ℝ) (μ : ℕ → ℝ) (p : ℕ)
    {lam U : ℝ} (hlam : 0 < lam)
    (hD : ∀ j, 0 ≤ D j) (hμ : ∀ j, 0 ≤ μ j)
    (htail : ∀ j > p, μ j ≤ U)
    (htrace : Summable (fun j => D j*μ j))
    (hQ : Summable (fun j => D j*(ResidualFilter.shrinkage (ResidualFilter.ridge lam) (μ j))^2)) :
    (∑' j, D j*(ResidualFilter.shrinkage (ResidualFilter.ridge lam) (μ j))^2) ≤
      (∑ j ∈ Finset.range (p+1), D j) + (U/lam^2)*(∑' j, D j*μ j) := by
  let Dlow := fun j => if j ∈ Finset.range (p+1) then D j else 0
  have hDlow : Summable Dlow := summable_of_ne_finset_zero (s := Finset.range (p+1))
    (fun j hj => if_neg hj)
  have hU0 : 0 ≤ U := (hμ (p+1)).trans (htail (p+1) (by omega))
  have hmajor := hDlow.add (htrace.mul_left (U/lam^2))
  have hpoint (j : ℕ) :
      D j*(ResidualFilter.shrinkage (ResidualFilter.ridge lam) (μ j))^2 ≤
        Dlow j+(U/lam^2)*(D j*μ j) := by
    by_cases hj : j ∈ Finset.range (p+1)
    · rw [show Dlow j = D j from if_pos hj, ridge_shrinkage_eq]
      have hden : 0 < μ j+lam := add_pos_of_nonneg_of_pos (hμ j) hlam
      have hq : μ j/(μ j+lam) ≤ 1 := (div_le_one hden).mpr (by linarith)
      have hq2 : (μ j/(μ j+lam))^2 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg (hμ j) hden.le) hq 2
      exact (mul_le_of_le_one_right (hD j) hq2).trans
        (le_add_of_nonneg_right (mul_nonneg (div_nonneg hU0 (sq_nonneg _)) (mul_nonneg (hD j) (hμ j))))
    · have hjp : p < j := by rw [Finset.mem_range] at hj; omega
      rw [show Dlow j = 0 from if_neg hj,zero_add]
      calc
        _ ≤ D j*((U/lam^2)*μ j) := mul_le_mul_of_nonneg_left
          (ridge_shrinkage_sq_le_trace_weight hlam (hμ j) (htail j hjp)) (hD j)
        _ = _ := by ring
  have h := hQ.tsum_le_tsum hpoint hmajor
  rw [hDlow.tsum_add (htrace.mul_left (U/lam^2)), tsum_mul_left] at h
  have hsum : (∑' j, Dlow j) = ∑ j ∈ Finset.range (p+1), D j := by
    rw [tsum_eq_sum (s := Finset.range (p+1)) (fun j hj => show Dlow j = 0 from if_neg hj)]
    exact Finset.sum_congr rfl (fun j hj => if_pos hj)
  rwa [hsum] at h

theorem ridge_biasWeight_low_le {lam t ell s : ℝ}
    (hlam : 0 < lam) (hell : 0 < ell) (ht : ell ≤ t) (hs : s ≤ 2) :
    t^s*(ResidualFilter.residual (ResidualFilter.ridge lam) t)^2 ≤ lam^2*ell^(s-2) := by
  have ht0 : 0 < t := hell.trans_le ht
  have hd0 : 0 < t+lam := add_pos ht0 hlam
  rw [ResidualFilter.ridge_residual hd0.ne']
  have hh := div_le_div_of_nonneg_left hlam.le ht0 (show t ≤ t+lam by linarith)
  calc
    t^s*(lam/(t+lam))^2 ≤ t^s*(lam/t)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg hlam.le hd0.le) hh 2)
        (Real.rpow_nonneg ht0.le _)
    _ = lam^2*t^(s-2) := by
      rw [Real.rpow_sub ht0, Real.rpow_two, div_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hell ht (by linarith)) (sq_nonneg _)

theorem ridge_biasWeight_high_le {lam t U s : ℝ}
    (hlam : 0 < lam) (ht : 0 ≤ t) (hU : t ≤ U) (hs : 0 ≤ s) :
    t^s*(ResidualFilter.residual (ResidualFilter.ridge lam) t)^2 ≤ U^s := by
  have hd0 : 0 < t+lam := add_pos_of_nonneg_of_pos ht hlam
  rw [ResidualFilter.ridge_residual hd0.ne']
  have hr : lam/(t+lam) ≤ 1 := (div_le_one hd0).mpr (by linarith)
  have hr2 : (lam/(t+lam))^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hlam.le hd0.le) hr 2
  exact (mul_le_of_le_one_right (Real.rpow_nonneg ht _) hr2).trans
    (Real.rpow_le_rpow ht hU hs)

theorem spherical_fixedDegree_isTheta {J : Type*} {l : Filter J}
    (ι : J → Type*) [∀ i, Fintype (ι i)] [∀ i, Nonempty (ι i)]
    (Φ : ℝ → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (m : ℕ) (hm : 0 < a m) (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    (fun i => zonalSphereDegreeValue (ι := ι i) a m) =Θ[l]
      (fun i => (Fintype.card (ι i) : ℝ)^(-(m : ℝ))) := by
  have h := zonalSphereDegreeValue_ratio_tendsto ι a ha Φ hseries hΦ m hm hd
  have hc : 0 < a m*(m.factorial : ℝ) := mul_pos hm (by positivity)
  exact (isTheta_of_div_tendsto_nhds_ne_zero h one_ne_zero).symm.trans
    ((isTheta_const_mul_left hc.ne').mpr (isTheta_refl _ _))

theorem spherical_lowDegree_uniform_lower {J : Type*} {l : Filter J}
    (ι : J → Type*) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (Φ : ℝ → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (p : ℕ) (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    ∃ c > 0, ∀ᶠ i in l, ∀ j ≤ p,
      c*(Fintype.card (ι i) : ℝ)^(-(p : ℝ)) ≤ zonalSphereDegreeValue (ι := ι i) a j := by
  let d := fun i => (Fintype.card (ι i) : ℝ)
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hfixed (j : ℕ) (hj : j ≤ p) :
      ∃ c > 0, ∀ᶠ i in l, c*d i^(-(p : ℝ)) ≤ zonalSphereDegreeValue (ι := ι i) a j := by
    have hjr : (j : ℝ) ≤ p := by exact_mod_cast hj
    have h := (dimensionPower_isBigO hdR (by linarith : -(p : ℝ) ≤ -(j : ℝ))).trans
      (spherical_fixedDegree_isTheta ι Φ a (fun k => (ha k).le) hseries hΦ j (ha j) hd).symm.isBigO
    obtain ⟨C,hC,hb⟩ := h.exists_pos
    refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
    filter_upwards [hb.bound, hd.eventually (eventually_ge_atTop j)] with i hi hdi
    have hp := zonalSphereDegreeValue_pos a (fun k => (ha k).le) Φ hseries j hdi (ha j)
    change ‖d i^(-(p : ℝ))‖ ≤ C*‖zonalSphereDegreeValue (ι := ι i) a j‖ at hi
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by
      dsimp [d]; positivity) _), abs_of_pos hp] at hi
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hC).mpr (by linarith)
  choose c hc hcl using fun j : Fin (p+1) => hfixed j (Nat.le_of_lt_succ j.isLt)
  let cmin := Finset.univ.inf' (Finset.univ_nonempty (α := Fin (p+1))) c
  refine ⟨cmin, (Finset.lt_inf'_iff _).mpr (fun j _ => hc j),?_⟩
  have hh : ∀ᶠ i in l, ∀ j : Fin (p+1), c j*d i^(-(p : ℝ)) ≤
      zonalSphereDegreeValue (ι := ι i) a j := (Filter.eventually_all).mpr hcl
  filter_upwards [hh] with i hi j hj
  let jj : Fin (p+1) := ⟨j,Nat.lt_succ_of_le hj⟩
  exact (mul_le_mul_of_nonneg_right (Finset.inf'_le c (Finset.mem_univ jj))
    (Real.rpow_nonneg (by positivity : 0 ≤ (Fintype.card (ι i) : ℝ)) _)).trans (hi jj)

end
end KernelSeq
