import KernelSeq.HighDimensionalRidgeBounds

/-! Original high-dimensional powers in the ridge sequence estimates. -/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology ContDiff
noncomputable section

theorem highDimensionalRidge_rate_exponents {s γ : ℝ}
    (_hs : 0 < s) (hs1 : s ≤ 1) (_hγ : s+1 ≤ γ) :
    let p := (highDimensionalDegree s γ : ℝ)
    let b := highDimensionalRidgeExponent s γ
    let ζ := highDimensionalRiskExponent s γ
    2*b-p-1 ≤ p ∧ p-γ ≤ -ζ ∧ -((p+1)*s) ≤ -ζ ∧
      -2*b-p*(s-2) = -ζ := by
  intro p b ζ
  have hb : b = p + min (highDimensionalRemainder s γ) s / 2 := rfl
  have hz : ζ = p*s+min (highDimensionalRemainder s γ) s := highDimensionalRiskExponent_eq
  have hmin := min_le_right (highDimensionalRemainder s γ) s
  have hz1 : ζ ≤ γ-p := min_le_left _ _
  have hz2 : ζ ≤ (p+1)*s := min_le_right _ _
  refine ⟨by linarith,by linarith,by linarith,?_⟩
  rw [hb,hz]
  ring

theorem ridge_biasWeight_low_dimension_bound {d t lam c C s γ : ℝ}
    (hd : 0 < d) (hlp : 0 < lam) (hc : 0 < c) (_hC : 0 < C)
    (hs : 0 < s) (hs1 : s ≤ 1) (hγ : s+1 ≤ γ)
    (ht : c*d^(-(highDimensionalDegree s γ : ℝ)) ≤ t)
    (hlam : lam ≤ C*d^(-highDimensionalRidgeExponent s γ)) :
    t^s*(ResidualFilter.residual (ResidualFilter.ridge lam) t)^2 ≤
      (C^2*c^(s-2))*d^(-highDimensionalRiskExponent s γ) := by
  let p := (highDimensionalDegree s γ : ℝ)
  let b := highDimensionalRidgeExponent s γ
  let ζ := highDimensionalRiskExponent s γ
  have hd' (r : ℝ) : 0 < d^r := Real.rpow_pos_of_pos hd r
  have hL := ridge_biasWeight_low_le (s := s) hlp (mul_pos hc (hd' _)) ht (by linarith)
  have hS := pow_le_pow_left₀ hlp.le hlam 2
  refine hL.trans ((mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg (mul_pos hc (hd' _)).le _)).trans_eq ?_)
  change (C*d^(-b))^2*(c*d^(-p))^(s-2) = (C^2*c^(s-2))*d^(-ζ)
  rw [mul_pow, Real.mul_rpow hc.le (hd' _).le, ← Real.rpow_mul hd.le, ← Real.rpow_two (d^(-b)),
    ← Real.rpow_mul hd.le]
  calc
    _ = C^2*c^(s-2)*(d^((-b)*2)*d^((-p)*(s-2))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hd]
      congr 2
      convert (highDimensionalRidge_rate_exponents hs hs1 hγ).2.2.2 using 1
      ring

theorem ridge_biasWeight_high_dimension_bound {d t lam C s γ : ℝ}
    (hd : 1 ≤ d) (hlp : 0 < lam) (ht0 : 0 ≤ t)
    (hs : 0 < s) (hs1 : s ≤ 1) (hγ : s+1 ≤ γ)
    (ht : t ≤ C*d^(-((highDimensionalDegree s γ : ℝ)+1))) :
    t^s*(ResidualFilter.residual (ResidualFilter.ridge lam) t)^2 ≤
      C^s*d^(-highDimensionalRiskExponent s γ) := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hp (r : ℝ) : 0 < d^r := Real.rpow_pos_of_pos hd0 r
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left (ht0.trans ht) (hp _)
  refine (ridge_biasWeight_high_le hlp ht0 ht hs.le).trans ?_
  rw [Real.mul_rpow hC (hp _).le, ← Real.rpow_mul hd0.le]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hC _)
  apply Real.rpow_le_rpow_of_exponent_le hd
  have h := (highDimensionalRidge_rate_exponents hs hs1 hγ).2.2.1
  exact (show -((highDimensionalDegree s γ : ℝ)+1)*s = -(((highDimensionalDegree s γ : ℝ)+1)*s) by ring).trans_le h

theorem spherical_layerDimension_isBigO {J : Type*} {l : Filter J}
    (ι : J → Type*) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (m : ℕ) (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    (fun i => (Module.finrank ℝ (spherePolynomialLayer (ι i) m) : ℝ)) =O[l]
      (fun i => (Fintype.card (ι i) : ℝ)^(m : ℝ)) := by
  have h := spherePolynomialLayer_dimension_ratio_tendsto ι m hd
  have hθ := (isTheta_of_div_tendsto_nhds_ne_zero h one_ne_zero).symm
  have hc : ((m.factorial : ℝ)⁻¹) ≠ 0 := by positivity
  have hbase : (fun i => (Fintype.card (ι i) : ℝ)^m/(m.factorial : ℝ)) =Θ[l]
      (fun i => (Fintype.card (ι i) : ℝ)^(m : ℝ)) := by
    have hh := (isTheta_const_mul_left hc).mpr
      (isTheta_refl (fun i => (Fintype.card (ι i) : ℝ)^m) l)
    simpa [Real.rpow_natCast,div_eq_mul_inv,mul_comm] using hh
  exact (hθ.trans hbase).isBigO

end
end KernelSeq
