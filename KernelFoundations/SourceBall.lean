import KernelFoundations.SingularCalculus
import KernelFoundations.CompactEmbedding

/-!
# Fractional covariance powers and source balls
-/

open MeasureTheory Submodule

namespace KernelFoundations
noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual positive fractional power of the prediction covariance. -/
def predictionSourcePower (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    (s : ℝ) (hs : 0 ≤ s) : E →L[ℝ] E :=
  compactSpectralMultiplier (S.comp S.adjoint)
    (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
    (ContinuousLinearMap.isPositive_self_comp_adjoint S) (fun t => t ^ (s / 2))
    (‖S.comp S.adjoint‖ ^ (s / 2)) (Real.rpow_nonneg (norm_nonneg _) _)
    (fun t ht => by
      rw [abs_of_nonneg (Real.rpow_nonneg ht.1 _)]
      exact Real.rpow_le_rpow ht.1 ht.2 (by positivity))

/-- The prediction source ball uses source vectors supported in the closed
prediction range. -/
def predictionSourceBall (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    (s : ℝ) (hs : 0 ≤ s) (R : ℝ) : Set E :=
  {f | ∃ h ∈ PredictionRange S, ‖h‖ ≤ R ∧ predictionSourcePower S hc s hs h = f}

theorem zero_mem_predictionSourceBall (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s) {R : ℝ} (hR : 0 ≤ R) :
    (0 : E) ∈ predictionSourceBall S hc s hs R :=
  ⟨0, (PredictionRange S).zero_mem, by simpa only [norm_zero] using hR, map_zero _⟩

theorem predictionSourceBall_zero (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s) :
    predictionSourceBall S hc s hs 0 = {0} := by
  ext f
  constructor
  · rintro ⟨g, _, hg, rfl⟩
    have hg0 : g = 0 := norm_eq_zero.mp (le_antisymm hg (norm_nonneg g))
    simp only [hg0, map_zero, Set.mem_singleton_iff]
  · rintro rfl
    exact zero_mem_predictionSourceBall S hc s hs le_rfl

theorem predictionSourcePower_mem_predictionRange (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    {h : E} (hh : h ∈ PredictionRange S) :
    predictionSourcePower S hc s hs h ∈ PredictionRange S :=
  compactSpectralMultiplier_mem_predictionRange S
    (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc) _ _ _ _ hh

theorem predictionSourceBall_mem_predictionRange (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s) (R : ℝ)
    {f : E} (hf : f ∈ predictionSourceBall S hc s hs R) : f ∈ PredictionRange S := by
  obtain ⟨h, hh, _, rfl⟩ := hf
  exact predictionSourcePower_mem_predictionRange S hc s hs hh

theorem predictionSourcePower_coefficient (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    (h : E) (i : PredictionSingularIndex S) :
    inner ℝ (predictionSingularBasis S hc i : E) (predictionSourcePower S hc s hs h) =
      i.1.1 ^ (s / 2) * inner ℝ (predictionSingularBasis S hc i : E) h :=
  predictionSingularBasis_multiplier_coefficient S hc
    (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc) _ _ _ _ h i

theorem predictionSourcePower_coefficient_sq (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    (h : E) (i : PredictionSingularIndex S) :
    inner ℝ (predictionSingularBasis S hc i : E) (predictionSourcePower S hc s hs h) ^ 2 =
      i.1.1 ^ s * inner ℝ (predictionSingularBasis S hc i : E) h ^ 2 := by
  rw [predictionSourcePower_coefficient, mul_pow]
  congr 1
  rw [← Real.rpow_two, ← Real.rpow_mul i.2.le]
  congr 1
  ring

/-- The scalar source estimate, with a constant depending only on the
spectral upper bound and source exponents, valid also at zero. -/
theorem source_regularized_weight_bound {lam M t s α : ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (ht : t ∈ Set.Icc (0 : ℝ) M)
    (hs : 0 ≤ s) (hα : 0 ≤ α) :
    t ^ s * (lam / (t + lam)) ^ α ≤
      (1 + M) ^ (s - min s α) * lam ^ (min s α) := by
  let r := min s α
  have hr : 0 ≤ r := le_min hs hα
  have hsr : 0 ≤ s-r := sub_nonneg.mpr (min_le_left _ _)
  have hαr : 0 ≤ α-r := sub_nonneg.mpr (min_le_right _ _)
  have hden : 0 < t+lam := add_pos_of_nonneg_of_pos ht.1 hlam
  have hw : 0 ≤ lam/(t+lam) := (div_pos hlam hden).le
  have hw1 : lam/(t+lam) ≤ 1 := (div_le_one hden).mpr (by linarith [ht.1])
  have hmix : t*(lam/(t+lam)) ≤ lam := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  have htPow : t^s = t^(s-r)*t^r := by
    simpa only [sub_add_cancel] using Real.rpow_add_of_nonneg ht.1 hsr hr
  have hwPow : (lam/(t+lam))^α = (lam/(t+lam))^r*(lam/(t+lam))^(α-r) := by
    simpa only [add_sub_cancel] using Real.rpow_add_of_nonneg hw hr hαr
  have h₁ : t^(s-r) ≤ (1+M)^(s-r) :=
    Real.rpow_le_rpow ht.1 (by linarith [ht.2]) hsr
  have h₂ := Real.rpow_le_rpow (mul_nonneg ht.1 hw) hmix hr
  have h₃ := Real.rpow_le_one hw hw1 hαr
  calc
    _ = t^(s-r) * (t*(lam/(t+lam)))^r * (lam/(t+lam))^(α-r) := by
      rw [htPow, hwPow, Real.mul_rpow ht.1 hw]
      ring
    _ ≤ ((1+M)^(s-r) * lam^r) * 1 := by
      exact mul_le_mul (mul_le_mul h₁ h₂ (Real.rpow_nonneg (mul_nonneg ht.1 hw) _)
        (Real.rpow_nonneg (by positivity) _)) h₃
        (Real.rpow_nonneg hw _) (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hlam.le _))
    _ = _ := by simp only [mul_one, r]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The `L²(μ)` source ball associated with a square-integrable feature map. -/
def featureSourceBall (k : X → H) (hk : MemLp k 2 μ) (s : ℝ) (hs : 0 ≤ s) (R : ℝ) :
    Set (Lp ℝ 2 μ) :=
  predictionSourceBall (featureEmbedding μ k hk) (populationCovariance_feature_isCompact μ k hk) s hs R

theorem featureSourceBall_supported (k : X → H) (hk : MemLp k 2 μ)
    (s : ℝ) (hs : 0 ≤ s) (R : ℝ) {f : Lp ℝ 2 μ} (hf : f ∈ featureSourceBall k hk s hs R) :
    f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure := by
  simpa only [predictionCovariance, closure_range_self_comp_adjoint] using
    predictionSourceBall_mem_predictionRange (featureEmbedding μ k hk)
      (populationCovariance_feature_isCompact μ k hk) s hs R hf


end
end KernelFoundations
