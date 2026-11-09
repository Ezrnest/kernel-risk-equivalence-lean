import KernelSeq.PolynomialSpectrumThreshold
import Mathlib.Analysis.Asymptotics.Theta

/-!
# The original asymptotic spectral assumptions

Two-sided asymptotic comparison is converted to primitive spectral envelopes
after a spectral-index threshold. The converse is also proved, so using the
threshold form in scale verification does not strengthen the manuscript's
polynomial or exponential asymptotic assumptions.
-/

open Filter Topology Asymptotics

namespace KernelSeq

theorem isTheta_iff_eventual_positive_comparison {w v : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hv : ∀ j, 0 < v j) :
    w =Θ[atTop] v ↔ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∃ J0 : ℕ, ∀ j ≥ J0, c * v j ≤ w j ∧ w j ≤ C * v j := by
  constructor
  · intro h
    obtain ⟨C, hC, hupper⟩ := h.1.exists_pos
    obtain ⟨D, hD, hlower⟩ := h.2.exists_pos
    have he : ∀ᶠ j : ℕ in atTop, (1 / D) * v j ≤ w j ∧ w j ≤ C * v j := by
      filter_upwards [hupper.bound, hlower.bound] with j hu hl
      rw [Real.norm_eq_abs, abs_of_nonneg (hw j), Real.norm_eq_abs, abs_of_pos (hv j)] at hu
      rw [Real.norm_eq_abs, abs_of_pos (hv j), Real.norm_eq_abs, abs_of_nonneg (hw j)] at hl
      refine ⟨?_, hu⟩
      have hh : v j / D ≤ w j := (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hl)
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh
    obtain ⟨J0, hJ0⟩ := eventually_atTop.mp he
    exact ⟨1 / D, C, one_div_pos.mpr hD, hC, J0, hJ0⟩
  · rintro ⟨c, C, hc, _hC, J0, hbound⟩
    constructor
    · apply IsBigO.of_bound C
      filter_upwards [eventually_ge_atTop J0] with j hj
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hw j), abs_of_pos (hv j)] using (hbound j hj).2
    · apply IsBigO.of_bound c⁻¹
      filter_upwards [eventually_ge_atTop J0] with j hj
      rw [Real.norm_eq_abs, abs_of_pos (hv j), Real.norm_eq_abs, abs_of_nonneg (hw j)]
      have hh : v j ≤ w j / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using (hbound j hj).1)
      simpa only [div_eq_mul_inv, mul_comm] using hh

theorem polynomial_asymptotics_iff_threshold {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (β : ℝ) :
    w =Θ[atTop] (fun j => ((j : ℝ) + 1) ^ (-β)) ↔
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ J0 : ℕ, ∀ j ≥ J0,
        c * ((j : ℝ) + 1) ^ (-β) ≤ w j ∧ w j ≤ C * ((j : ℝ) + 1) ^ (-β) :=
  isTheta_iff_eventual_positive_comparison hw
    (fun j => Real.rpow_pos_of_pos (by positivity : 0 < (j : ℝ) + 1) _)

theorem exponential_asymptotics_iff_threshold {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (c0 ν : ℝ) :
    w =Θ[atTop] (fun j => Real.exp (-c0 * ((j : ℝ) + 1) ^ ν)) ↔
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ J0 : ℕ, ∀ j ≥ J0,
        c * Real.exp (-c0 * ((j : ℝ) + 1) ^ ν) ≤ w j ∧
          w j ≤ C * Real.exp (-c0 * ((j : ℝ) + 1) ^ ν) :=
  isTheta_iff_eventual_positive_comparison hw (fun _ => Real.exp_pos _)

end KernelSeq
