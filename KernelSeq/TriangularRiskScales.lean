import KernelSeq.ExpectationScale
import KernelSeq.TriangularRiskFacts

/-!
# Original deterministic scales for genuinely varying regression rows

These limits use only the actual row dimensions and original scalar scale
conditions. No common Hilbert space, common design distribution or fixed
target is used. They therefore apply on both an ordinary sequence filter and
the uniform family filter.
-/

open MeasureTheory Filter Topology

namespace KernelSeq
noncomputable section

universe uH uX uΩ
variable {J : Type*} {l : Filter J} {κ ρ A : ℝ}

theorem triangular_variance_scale_limits
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0)) :
    Tendsto (fun i => (m i).v) l (𝓝 0) ∧
      Tendsto (fun i => (m i).L / ((m i).n : ℝ)) l (𝓝 0) ∧
      Tendsto (fun i => (m i).L * intrinsicDimensionLog (m i).N (m i).r /
        ((m i).n : ℝ)) l (𝓝 0) ∧
      Tendsto (fun i => ((m i).L + 1) / ((m i).n : ℝ)) l (𝓝 0) ∧
      Tendsto (fun i => Real.sqrt (m i).v * intrinsicDimensionLog (m i).N (m i).r /
        dimensionLog (m i).N) l (𝓝 0) := by
  have hgood : ∀ᶠ i in l, 0 ≤ (m i).v ∧ 0 ≤ (m i).N ∧ 0 < (m i).Q ∧
      0 < (m i).r ∧ (m i).r ≤ 1 ∧ (m i).Q ≤ A ^ 2 * (m i).r * (m i).N := by
    filter_upwards [hQ] with i hi
    exact ⟨(m i).v_nonneg, (m i).N_nonneg, hi, (m i).r_pos hi,
      (m i).r_le_one, (m i).Q_le_retention⟩
  have hs := variance_compatibility_scale_limits (fun i => (m i).v) (fun i => (m i).N)
    (fun i => (m i).Q) (fun i => (m i).r) A hgood hc
  have hrow : ∀ᶠ i in l, 0 < ((m i).n : ℝ) ∧ 0 ≤ (m i).N ∧ 0 < (m i).Q ∧
      0 < (m i).r ∧ (m i).r ≤ 1 ∧ (m i).r ≤ (m i).L ∧
      (m i).Q ≤ A ^ 2 * (m i).r * (m i).N := by
    filter_upwards [hQ] with i hi
    exact ⟨Nat.cast_pos.mpr (m i).sample_pos, (m i).N_nonneg, hi, (m i).r_pos hi,
      (m i).r_le_one, (m i).r_le_N.trans (m i).N_le_L, (m i).Q_le_retention⟩
  have hr := variance_compatibility_expectation_covariance_limits (fun i => ((m i).n : ℝ))
    (fun i => (m i).L) (fun i => (m i).N) (fun i => (m i).Q) (fun i => (m i).r) A hrow hc
  exact ⟨hs.1, hr.1, hr.2.1, hr.2.2, hs.2.2⟩

/-- Every finite smallness condition for the actual covariance and good-risk
estimates follows from the original variance compatibility, uniformly on the
chosen filter. No additional inverse-sample or retention scale is assumed. -/
theorem triangular_eventually_small
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0)) :
    ∀ᶠ i in l, (m i).Q ≤ ((m i).n : ℝ) ∧
      ((m i).L + 1) / ((m i).n : ℝ) ≤ 1 / 8 ∧
      (m i).L * intrinsicDimensionLog (m i).N (m i).r / ((m i).n : ℝ) ≤ 1 / 65536 ∧
      Real.sqrt (m i).v * intrinsicDimensionLog (m i).N (m i).r / dimensionLog (m i).N ≤ 1 ∧
      A ^ 4 * (m i).compatibility ^ 2 ≤ 1 := by
  obtain ⟨_, hLn, hIL, hdel, hlin⟩ := triangular_variance_scale_limits m hQ hc
  have hqn := eventually_filterDimension_le_sample_of_le (fun i => (m i).Q)
    (fun i => (m i).L) (fun i => ((m i).n : ℝ)) (sq_nonneg A)
    (Eventually.of_forall fun i => (m i).Q_nonneg)
    (Eventually.of_forall fun i => Nat.cast_pos.mpr (m i).sample_pos)
    (Eventually.of_forall fun i => (m i).Q_le_L) hLn
  have hcs := (hc.pow 2).const_mul (A ^ 4)
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hcs
  filter_upwards [hqn, hdel.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    hIL.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 65536)),
    hlin.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hcs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with i hqi hdi hIi hli hci
  exact ⟨hqi, hdi.le, hIi.le, hli.le, hci.le⟩

theorem triangular_cutoff_limits [NeBot l]
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0))
    (hz : Tendsto (fun i => (m i).sourceBalance) l (𝓝 0)) :
    (∀ᶠ i in l, (m i).cutoff ∈ Set.Ioc (0 : ℝ) (originalBiasCutoffCap A)) ∧
      Tendsto (fun i => (m i).cutoff) l (𝓝 0) ∧
      Tendsto (fun i => (m i).v / (m i).cutoff ^ 2) l (𝓝 0) ∧
      Tendsto (fun i => (m i).sourceBalance / (m i).cutoff ^ 2) l (𝓝 0) := by
  obtain ⟨i₀, _⟩ := hQ.exists
  have hA : 0 ≤ A := (m i₀).A_nonneg
  have hv := (triangular_variance_scale_limits m hQ hc).1
  have hsn : ∀ᶠ i in l, 0 ≤ (m i).sourceBalance := hQ.mono fun i hi => (m i).sourceBalance_nonneg hi
  have hsp : ∀ᶠ i in l, 0 < (m i).v + (m i).sourceBalance := by
    filter_upwards [hQ, hsn] with i hi hsi
    exact add_pos_of_pos_of_nonneg ((m i).v_pos hi) hsi
  have h := localizationCutoff_limits (originalBiasCutoffCap_pos hA) hv hz
    (Eventually.of_forall fun i => (m i).v_nonneg) hsn hsp
  refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2⟩
  filter_upwards [h.1] with i hi
  exact ⟨hi, min_le_left _ _⟩

/-- All deterministic terms in the uniform good-event envelope vanish. -/
theorem triangular_good_scalar_limits [NeBot l]
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0))
    (hz : Tendsto (fun i => (m i).sourceBalance) l (𝓝 0)) :
    Tendsto (fun i => (m i).L / ((m i).n : ℝ) + (m i).cutoff ^ 2 +
      (m i).v / (m i).cutoff ^ 2) l (𝓝 0) ∧
      Tendsto (fun i => (m i).sourceBalance / (m i).cutoff ^ 2) l (𝓝 0) := by
  have hLn := (triangular_variance_scale_limits m hQ hc).2.1
  obtain ⟨_, ht, hv, hz'⟩ := triangular_cutoff_limits m hQ hc hz
  refine ⟨?_, hz'⟩
  simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero] using (hLn.add (ht.pow 2)).add hv

end
end KernelSeq
