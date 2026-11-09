import KernelSeq.PinskerOracle

/-!
# Exact leading limit of the actual Pinsker sequence benchmark

The variance is the actual filter dimension of the population covariance,
not its leading power supplied as an assumption. Its proven exact-counting
asymptotic is combined with the original oracle identity.
-/

namespace KernelSeq
open MeasureTheory Filter Topology
noncomputable section

variable {X H I : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

def pinskerWorstSequenceBenchmark (k : X → H) (hk : MemLp k 2 μ)
    (s β R σ D n : ℝ) : ℝ :=
  let lam := pinskerOracleScale s β R σ D n
  R^2 * lam^s + σ^2 / n * featureFilterDimension k hk (ResidualFilter.pinsker lam s)

theorem pinskerWorstSequenceBenchmark_normalized_limit
    {l : Filter I} (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {s β R σ D : ℝ} (hs : 1 ≤ s) (hβ : 1 < β)
    (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hcount : Tendsto
      (fun t => (featureSpectralCount k hk t : ℝ) / (D * t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1))
    (n : I → ℝ) (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop) :
    Tendsto (fun i => n i ^ pinskerRiskExponent s β *
      pinskerWorstSequenceBenchmark k hk s β R σ D (n i)) l
      (𝓝 (pinskerUpperConstant s β R σ D)) := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  let lam := fun i => pinskerOracleScale s β R σ D (n i)
  have hl (i : I) : 0 < lam i := pinskerOracleScale_pos hs0 hβ0 hR hσ hD (hn0 i)
  have hlGT : Tendsto lam l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨pinskerOracleScale_tendsto_zero n hn0 hn hs0 hβ0 hR hσ hD, Eventually.of_forall hl⟩
  let T := fun i => (D * pinskerVarianceConstant s β) * lam i ^ (-(1/β))
  let r := fun i => featureFilterDimension k hk (ResidualFilter.pinsker (lam i) s) / T i
  have hT (i : I) : 0 < T i := by
    exact mul_pos (mul_pos hD (pinskerVarianceConstant_pos hs0 hβ0))
      (Real.rpow_pos_of_pos (hl i) _)
  have hr : Tendsto r l (𝓝 1) :=
    (featureFilterDimension_pinsker_ratio_tendsto k hk e hβ hD hs hcount).comp hlGT
  have hid (i : I) : n i ^ pinskerRiskExponent s β *
      pinskerWorstSequenceBenchmark k hk s β R σ D (n i) =
      (pinskerUpperConstant s β R σ D / (s*β+1)) * (1+s*β*r i) := by
    have hbal : σ^2 / n i * T i = s*β * (R^2 * lam i^s) := by
      convert pinskerOracleScale_balance hs0 hβ0 hR hσ hD (hn0 i) using 1
      dsimp [T,lam]
      ring
    have hv : σ^2 / n i * featureFilterDimension k hk (ResidualFilter.pinsker (lam i) s) =
        (s*β * (R^2 * lam i^s)) * r i := by
      rw [← hbal]
      dsimp [r]
      field_simp [(hT i).ne', (hn0 i).ne']
    have hcancel : n i ^ pinskerRiskExponent s β * n i ^ (-pinskerRiskExponent s β) = 1 := by
      rw [← Real.rpow_add (hn0 i), add_neg_cancel, Real.rpow_zero]
    change n i ^ pinskerRiskExponent s β *
      (R^2 * lam i^s + σ^2 / n i * featureFilterDimension k hk (ResidualFilter.pinsker (lam i) s)) = _
    rw [hv, pinskerOracleScale_bias hs0 hβ0 hR hσ hD (hn0 i)]
    calc
      _ = (n i ^ pinskerRiskExponent s β * n i ^ (-pinskerRiskExponent s β)) *
          (pinskerUpperConstant s β R σ D / (s*β+1)) * (1+s*β*r i) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hc : pinskerUpperConstant s β R σ D / (s*β+1) * (1+s*β*1) =
      pinskerUpperConstant s β R σ D := by
    have hpos : 0 < s*β+1 := by positivity
    field_simp
    ring
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).add (hr.const_mul (s*β))).const_mul
    (pinskerUpperConstant s β R σ D / (s*β+1))
  rw [hc] at hlim
  exact hlim.congr' (Eventually.of_forall fun i => (hid i).symm)

end
end KernelSeq
