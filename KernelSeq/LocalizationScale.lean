import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Localization cutoff scales

The localization cutoff and its asymptotic scale limits under `0 < v + ζ`.
-/

namespace KernelSeq

open Filter
open scoped Topology

/-- The auxiliary cutoff in the bias comparison proof. -/
noncomputable def localizationCutoff (τ₀ v ζ : ℝ) : ℝ :=
  min τ₀ ((v + ζ) ^ ((1 : ℝ) / 4))

/-- The real fourth root equals two successive square roots. -/
theorem fourthRoot_eq_sqrt_sqrt {s : ℝ} (hs : 0 ≤ s) :
    s ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt s) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hs]
  norm_num

/-- Positivity of the cutoff. -/
theorem localizationCutoff_pos {τ₀ v ζ : ℝ} (hτ₀ : 0 < τ₀) (hs : 0 < v + ζ) :
    0 < localizationCutoff τ₀ v ζ := by
  exact lt_min hτ₀ (Real.rpow_pos_of_pos hs _)

/-- On the fourth-root branch, the total scale divided by the squared cutoff
is exactly its square root. -/
theorem sum_div_localizationCutoff_sq {τ₀ v ζ : ℝ} (hs : 0 < v + ζ)
    (hbranch : (v + ζ) ^ ((1 : ℝ) / 4) ≤ τ₀) :
    (v + ζ) / (localizationCutoff τ₀ v ζ) ^ 2 = Real.sqrt (v + ζ) := by
  rw [localizationCutoff, min_eq_right hbranch, fourthRoot_eq_sqrt_sqrt hs.le,
    Real.sq_sqrt (Real.sqrt_nonneg _)]
  apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hs))).2
  nlinarith [Real.sq_sqrt hs.le]

/-- The cutoff tends to zero along any filter where both scales vanish. -/
theorem tendsto_localizationCutoff {ι : Type*} {l : Filter ι}
    {v ζ : ι → ℝ} {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hv : Tendsto v l (𝓝 0)) (hζ : Tendsto ζ l (𝓝 0)) :
    Tendsto (fun i => localizationCutoff τ₀ (v i) (ζ i)) l (𝓝 0) := by
  have hsum : Tendsto (fun i => v i + ζ i) l (𝓝 0) := by
    simpa using hv.add hζ
  have hroot := hsum.rpow_const_nhds_zero (by norm_num : 0 < (1 : ℝ) / 4)
  simpa [localizationCutoff, min_eq_right hτ₀.le] using
    (tendsto_const_nhds.min hroot :
      Tendsto (fun i => min τ₀ ((v i + ζ i) ^ ((1 : ℝ) / 4))) l (𝓝 (min τ₀ 0)))

/-- The two scales are negligible relative to the squared cutoff.
No lower bound on either scale separately is required. -/
theorem localizationCutoff_limits {ι : Type*} {l : Filter ι}
    {v ζ : ι → ℝ} {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hv : Tendsto v l (𝓝 0)) (hζ : Tendsto ζ l (𝓝 0))
    (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i) (hζ_nonneg : ∀ᶠ i in l, 0 ≤ ζ i)
    (hs_pos : ∀ᶠ i in l, 0 < v i + ζ i) :
    (∀ᶠ i in l, 0 < localizationCutoff τ₀ (v i) (ζ i)) ∧
    Tendsto (fun i => localizationCutoff τ₀ (v i) (ζ i)) l (𝓝 0) ∧
    Tendsto (fun i => v i / (localizationCutoff τ₀ (v i) (ζ i)) ^ 2) l (𝓝 0) ∧
    Tendsto (fun i => ζ i / (localizationCutoff τ₀ (v i) (ζ i)) ^ 2) l (𝓝 0) := by
  have hsum : Tendsto (fun i => v i + ζ i) l (𝓝 0) := by
    simpa using hv.add hζ
  have hroot := hsum.rpow_const_nhds_zero (by norm_num : 0 < (1 : ℝ) / 4)
  have hbranch : ∀ᶠ i in l, (v i + ζ i) ^ ((1 : ℝ) / 4) ≤ τ₀ :=
    (hroot.eventually (gt_mem_nhds hτ₀)).mono fun _ h => h.le
  have hsqrt : Tendsto (fun i => Real.sqrt (v i + ζ i)) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsum
  have hbound : ∀ᶠ i in l,
      (0 ≤ v i / (localizationCutoff τ₀ (v i) (ζ i)) ^ 2 ∧
       v i / (localizationCutoff τ₀ (v i) (ζ i)) ^ 2 ≤ Real.sqrt (v i + ζ i)) ∧
      (0 ≤ ζ i / (localizationCutoff τ₀ (v i) (ζ i)) ^ 2 ∧
       ζ i / (localizationCutoff τ₀ (v i) (ζ i)) ^ 2 ≤ Real.sqrt (v i + ζ i)) := by
    filter_upwards [hv_nonneg, hζ_nonneg, hs_pos, hbranch] with i hvi hζi hsi hbi
    have hden := sq_nonneg (localizationCutoff τ₀ (v i) (ζ i))
    have hsum_eq := sum_div_localizationCutoff_sq hsi hbi
    refine ⟨⟨div_nonneg hvi hden, ?_⟩, ⟨div_nonneg hζi hden, ?_⟩⟩
    · calc
        _ ≤ (v i + ζ i) / (localizationCutoff τ₀ (v i) (ζ i)) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) hden
        _ = _ := hsum_eq
    · calc
        _ ≤ (v i + ζ i) / (localizationCutoff τ₀ (v i) (ζ i)) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) hden
        _ = _ := hsum_eq
  refine ⟨hs_pos.mono (fun _ hi => localizationCutoff_pos hτ₀ hi),
    tendsto_localizationCutoff hτ₀ hv hζ, ?_, ?_⟩
  · exact squeeze_zero' (hbound.mono fun _ hi => hi.1.1)
      (hbound.mono fun _ hi => hi.1.2) hsqrt
  · exact squeeze_zero' (hbound.mono fun _ hi => hi.2.1)
      (hbound.mono fun _ hi => hi.2.2) hsqrt

end KernelSeq
