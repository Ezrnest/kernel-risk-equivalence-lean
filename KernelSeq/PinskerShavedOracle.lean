import KernelSeq.PinskerOracle
import KernelSeq.PinskerPriorProfiles

/-!
# The original shaved Pinsker threshold

The threshold retains both formulas displayed in the manuscript. It is the
actual oracle at radius `sqrt (1-delta)*R`, and its energy balance and sharp
constant are consequences of the original oracle formula.
-/

namespace KernelSeq

open Filter Topology
noncomputable section

def pinskerShavedOracleScale (s β R σ D n δ : ℝ) : ℝ :=
  (σ^2*D*(s*β)/(n*(1-δ)*R^2*(s*β+1)*(s*β+2)))^(β/(s*β+1))

theorem pinskerShavedOracleScale_eq_radius {s β R σ D n δ : ℝ} (hδ : δ < 1) :
    pinskerShavedOracleScale s β R σ D n δ =
      pinskerOracleScale s β (Real.sqrt (1-δ)*R) σ D n := by
  unfold pinskerShavedOracleScale pinskerOracleScale
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1-δ)]
  congr 2
  ring

theorem pinskerShavedOracleScale_eq_mul {s β R σ D n δ : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hn : 0 < n) (hδ : δ < 1) :
    pinskerShavedOracleScale s β R σ D n δ =
      pinskerOracleScale s β R σ D n * (1-δ)^(-pinskerOracleExponent s β) := by
  have hb : 0 < σ^2*D*(s*β)/(n*R^2*(s*β+1)*(s*β+2)) := by positivity
  have hd : 0 < 1-δ := by linarith
  have he : σ^2*D*(s*β)/(n*(1-δ)*R^2*(s*β+1)*(s*β+2)) =
      (σ^2*D*(s*β)/(n*R^2*(s*β+1)*(s*β+2)))/(1-δ) := by field_simp
  rw [pinskerShavedOracleScale, he, Real.div_rpow hb.le hd.le, Real.rpow_neg hd.le]
  rfl

theorem pinskerShavedOracleScale_pos {s β R σ D n δ : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hn : 0 < n) (hδ : δ < 1) : 0 < pinskerShavedOracleScale s β R σ D n δ := by
  unfold pinskerShavedOracleScale
  positivity

/-- Exact deterministic source-energy balance at the actual oracle. -/
theorem pinskerOracleScale_priorEnergy_balance {s β R σ D n : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hn : 0 < n) :
    (σ^2/n)*pinskerOracleScale s β R σ D n^(-s-1/β)*
      (D*pinskerPriorEnergyConstant s β) = R^2 := by
  have hl := pinskerOracleScale_pos hs hβ hR hσ hD hn
  have he : -s-1/β = -(s+1/β) := by ring
  rw [he, Real.rpow_neg hl.le, pinskerOracleScale_power hs hβ hR hσ hD hn]
  unfold pinskerPriorEnergyConstant
  field_simp

theorem pinskerShavedOracleScale_priorEnergy_balance {s β R σ D n δ : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hn : 0 < n) (hδ : δ < 1) :
    (σ^2/n)*pinskerShavedOracleScale s β R σ D n δ^(-s-1/β)*
      (D*pinskerPriorEnergyConstant s β) = (1-δ)*R^2 := by
  rw [pinskerShavedOracleScale_eq_radius hδ]
  have hRad : 0 < Real.sqrt (1-δ)*R := mul_pos (Real.sqrt_pos.2 (by linarith)) hR
  rw [pinskerOracleScale_priorEnergy_balance hs hβ hRad hσ hD hn,
    mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1-δ)]

/-- Shaving changes the original sharp constant by precisely the factor
displayed in the lower-bound proof. -/
theorem pinskerUpperConstant_shaved_radius {s β R σ D δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1) :
    pinskerUpperConstant s β (Real.sqrt (1-δ)*R) σ D =
      (1-δ)^(1/(s*β+1))*pinskerUpperConstant s β R σ D := by
  have hd : 0 ≤ 1-δ := by linarith
  unfold pinskerUpperConstant
  rw [Real.mul_rpow (Real.sqrt_nonneg _) hR, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hd]
  have he : (1/2 : ℝ)*(2/(s*β+1)) = 1/(s*β+1) := by ring
  rw [he]
  ring

theorem pinskerShavedOracleScale_tendsto_zero {I : Type*} {l : Filter I}
    (n : I → ℝ) (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop)
    {s β R σ D δ : ℝ} (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R)
    (hσ : 0 < σ) (hD : 0 < D) (hδ : δ < 1) :
    Tendsto (fun i => pinskerShavedOracleScale s β R σ D (n i) δ) l (𝓝 0) := by
  have hRad : 0 < Real.sqrt (1-δ)*R := mul_pos (Real.sqrt_pos.2 (by linarith)) hR
  simpa only [pinskerShavedOracleScale_eq_radius hδ] using
    pinskerOracleScale_tendsto_zero n hn0 hn hs hβ hRad hσ hD

end
end KernelSeq
