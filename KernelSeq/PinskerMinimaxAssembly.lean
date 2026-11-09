import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Scalar completion of the Pinsker minimax sandwich

These order/limit lemmas only assemble already proved bounds. The actual
Gaussian prior, source membership and remainder rates are supplied by their
concrete modules before applying them to the original minimax risk.
-/

namespace KernelSeq
open Filter Topology
open scoped ENNReal
noncomputable section

theorem real_le_toReal_add_of_ofReal_le {a r : ℝ} {M : ℝ≥0∞}
    (hr : 0 ≤ r) (hM : M ≠ ∞) (h : ENNReal.ofReal a ≤ M + ENNReal.ofReal r) :
    a ≤ M.toReal + r := by
  rw [← ENNReal.ofReal_toReal hM, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hr] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg ENNReal.toReal_nonneg hr)).mp h

/-- Letting the actual shaved-prior parameter decrease to zero recovers the
unshaved constant. The choice of the shaving amount is made in the proof. -/
theorem tendsto_of_pinsker_shaved_bounds {I : Type*} {l : Filter I}
    (M : I → ℝ) {C p : ℝ} (hC : 0 < C) (_hp : 0 < p) (hp1 : p ≤ 1)
    (hupper : ∀ ε > 0, ∀ᶠ i in l, M i ≤ C+ε)
    (hlower : ∀ δ, 0 < δ → δ < 1 → ∀ ε > 0,
      ∀ᶠ i in l, C*(1-δ)^p - ε ≤ M i) :
    Tendsto M l (𝓝 C) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min (1/2 : ℝ) (ε/(4*C))
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδhalf : δ ≤ 1/2 := min_le_left _ _
  have hδ1 : δ < 1 := by linarith
  have hδc : δ*C ≤ ε/4 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (1/2 : ℝ) (ε/(4*C))) hC.le
    have he : (ε/(4*C))*C = ε/4 := by field_simp
    exact hh.trans_eq he
  have hpow : 1-δ ≤ (1-δ)^p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
      (by linarith : 0 < 1-δ) (by linarith : 1-δ ≤ 1) hp1
  have hclower : C-ε/4 ≤ C*(1-δ)^p := by
    have hh := mul_le_mul_of_nonneg_left hpow hC.le
    nlinarith
  filter_upwards [hupper (ε/2) (by linarith), hlower δ hδ0 hδ1 (ε/4) (by linarith)] with i hu hl
  rw [Real.dist_eq]
  apply lt_of_le_of_lt (abs_le.mpr ⟨?_, ?_⟩) (by linarith : ε/2 < ε) <;> linarith

end
end KernelSeq
