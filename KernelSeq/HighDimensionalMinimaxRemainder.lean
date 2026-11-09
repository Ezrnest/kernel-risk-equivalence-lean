import KernelSeq.HighDimensionalPhaseLimits
import KernelSeq.SphereDimensionAsymptotics
import KernelSeq.GaussianPriorOutsideMoment

/-!
# Bounds on the actual high-dimensional prior shaving remainder

The binomial block dimensions make the maximal coordinate source energy
of order d⁻ᵖ. The actual Gaussian exponential remainder is negligible at
every polynomial scale. Finally, decreasing the shaving amount recovers
the original sharp constant in all four phases.
-/

namespace KernelSeq
open Filter
open scoped Topology
noncomputable section

def highDimensionalPriorWeightFactor (p : ℕ) (R : ℝ) : ℝ :=
  R^2*(2^p*(p.factorial : ℝ)+2^(p+1)*((p+1).factorial : ℝ))

theorem highDimensionalPriorWeightFactor_pos (p : ℕ) {R : ℝ} (hR : 0 < R) :
    0 < highDimensionalPriorWeightFactor p R := by
  unfold highDimensionalPriorWeightFactor
  positivity

private theorem squarefree_choose_inv_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (m : ℕ) (hd : 2*m ≤ Fintype.card ι) :
    (((Fintype.card ι).choose m : ℝ))⁻¹ ≤
      (2^m*(m.factorial : ℝ))*(Fintype.card ι : ℝ)^(-(m : ℝ)) := by
  have h := squarefreeSphereBlock_dimension_lower (ι := ι) m hd
  rw [squarefreeSphereBlock_finrank] at h
  have hd0 : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hbase : 0 < (Fintype.card ι : ℝ)^m/(2^m*(m.factorial : ℝ)) := by positivity
  have hh := one_div_le_one_div_of_le hbase h
  refine (show (((Fintype.card ι).choose m : ℝ))⁻¹ ≤
      1/((Fintype.card ι : ℝ)^m/(2^m*(m.factorial : ℝ))) by simpa only [one_div] using hh).trans_eq ?_
  rw [Real.rpow_neg hd0.le, Real.rpow_natCast, div_div_eq_mul_div, one_mul, div_eq_mul_inv]

theorem spherical_minimax_prior_weight_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ℕ) (hd : 2*(p+1) ≤ Fintype.card ι) {S R : ℝ} (hS : S ≤ R^2) :
    let B := highDimensionalPriorWeightFactor p R*(Fintype.card ι : ℝ)^(-(p : ℝ))
    S/((Fintype.card ι).choose p : ℝ) ≤ B ∧ S/((Fintype.card ι).choose (p+1) : ℝ) ≤ B := by
  dsimp only
  let D := (Fintype.card ι : ℝ)
  let C := (2 : ℝ)^p*(p.factorial : ℝ)+(2 : ℝ)^(p+1)*((p+1).factorial : ℝ)
  have hD : 1 ≤ D := Nat.one_le_cast.mpr Fintype.card_pos
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have haux (m : ℕ) (hm : p ≤ m) (hmd : 2*m ≤ Fintype.card ι)
      (hC : (2 : ℝ)^m*(m.factorial : ℝ) ≤ C) :
      S/((Fintype.card ι).choose m : ℝ) ≤ highDimensionalPriorWeightFactor p R*D^(-(p : ℝ)) := by
    have hexp : D^(-(m : ℝ)) ≤ D^(-(p : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hD (neg_le_neg (Nat.cast_le.mpr hm))
    have hweight : (((Fintype.card ι).choose m : ℝ))⁻¹ ≤ C*D^(-(p : ℝ)) :=
      (squarefree_choose_inv_le m hmd).trans
        ((mul_le_mul_of_nonneg_left hexp (by positivity)).trans
          (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hD0 _)))
    rw [div_eq_mul_inv]
    calc
      _ ≤ R^2*(C*D^(-(p : ℝ))) := mul_le_mul hS hweight (by positivity) (sq_nonneg R)
      _ = _ := by unfold highDimensionalPriorWeightFactor; dsimp only [C]; ring
  exact ⟨haux p le_rfl (by omega) (le_add_of_nonneg_right (by positivity)),
    haux (p+1) (Nat.le_succ _) hd (le_add_of_nonneg_left (by positivity))⟩

theorem dimension_exponential_shaving_remainder_tendsto_zero {I : Type*} {l : Filter I}
    (d : I → ℝ) (hd : Tendsto d l atTop) (hd0 : ∀ i, 0 < d i)
    {p K c : ℝ} (hp : 0 < p) (hK : 0 < K) (hc : 0 < c) (ζ C : ℝ) :
    Tendsto (fun i => d i^ζ*(C*Real.exp (-c/(2*(K*d i^(-p)))))) l (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (ζ/p) (c/(2*K)) (by positivity)).comp
    ((tendsto_rpow_atTop hp).comp hd)
  have h' := h.const_mul C
  rw [mul_zero] at h'
  apply h'.congr
  intro i
  change C*((d i^p)^(ζ/p)*Real.exp (-(c/(2*K))*d i^p)) = _
  have hpow : (d i^p)^(ζ/p) = d i^ζ := by
    rw [← Real.rpow_mul (hd0 i).le]
    congr 1
    field_simp
  have he : -(c/(2*K))*d i^p = -c/(2*(K*d i^(-p))) := by
    rw [Real.rpow_neg (hd0 i).le]
    field_simp [(Real.rpow_pos_of_pos (hd0 i) p).ne']
  rw [hpow, he]
  ring

theorem highDimensionalPinskerConstant_shaved_lower (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    {s γ R σ η ε : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hη : 0 < η)
    (hε : 0 ≤ ε) (hε1 : ε < 1) :
    (1-ε)*highDimensionalPinskerConstant a s γ R σ η ≤
      highDimensionalPinskerConstant a s γ (Real.sqrt (1-ε)*R) σ η := by
  have hc : 0 < 1-ε := sub_pos.mpr hε1
  have hsource (m : ℕ) : highDimensionalSourceConstant a s (Real.sqrt (1-ε)*R) m =
      (1-ε)*highDimensionalSourceConstant a s R m := by
    unfold highDimensionalSourceConstant
    rw [mul_pow, Real.sq_sqrt hc.le]
    ring
  let p := highDimensionalDegree s γ
  let A := highDimensionalSourceConstant a s R p
  let B := highDimensionalNoiseConstant σ η p
  have hA : 0 < A := highDimensionalSourceConstant_pos ha hR p
  have hB : 0 < B := highDimensionalNoiseConstant_pos hσ hη p
  simp only [highDimensionalPinskerConstant, hsource]
  split_ifs
  · change (1-ε)*(A*B/(A+B)) ≤ (1-ε)*A*B/((1-ε)*A+B)
    have hden : (1-ε)*A+B ≤ A+B := by nlinarith [mul_nonneg hε hA.le]
    rw [← mul_div_assoc, ← mul_assoc]
    exact div_le_div_of_nonneg_left (by positivity) (add_pos (mul_pos hc hA) hB) hden
  · change (1-ε)*B ≤ B
    nlinarith [mul_nonneg hε hB.le]
  · change (1-ε)*(B+highDimensionalSourceConstant a s R (p+1)) ≤
      B+(1-ε)*highDimensionalSourceConstant a s R (p+1)
    nlinarith only [mul_nonneg hε hB.le]
  · exact le_rfl

end
end KernelSeq
