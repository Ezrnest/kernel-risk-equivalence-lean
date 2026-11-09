import KernelSeq.UniformFilters
import Mathlib.Tactic.FieldSimp

/-!
# Uniform relative risk control transfers to an actual supremum

A common benchmark upper envelope and a genuine maximizing member suffice.
The risk supremum is proved bounded from the uniform error itself; no
boundedness, measurability, countability or compactness of the parameter
family is postulated. Bounds need hold only eventually in the row.
-/

namespace KernelSeq

open Filter Topology Set
noncomputable section

/-- A finite-row supremum bound derived from pointwise relative errors.
The benchmark is actually attained; no boundedness certificate is assumed. -/
theorem sup_risk_relative_error_of_benchmark_attained {Θ : Type*}
    (R B : Θ → ℝ) (S ε : ℝ) (hε : 0 ≤ ε)
    (hB : ∀ θ, 0 < B θ) (hupper : ∀ θ, B θ ≤ S)
    (hattained : ∃ θ, B θ = S)
    (herr : ∀ θ, |R θ / B θ - 1| ≤ ε) :
    BddAbove (Set.range R) ∧ |sSup (Set.range R) / S - 1| ≤ ε := by
  obtain ⟨θ0, hθ0⟩ := hattained
  have hS : 0 < S := hθ0 ▸ hB θ0
  have hRupper (θ : Θ) : R θ ≤ (1 + ε) * S := by
    have hr : R θ / B θ ≤ 1 + ε := by linarith [(abs_le.mp (herr θ)).2]
    exact ((div_le_iff₀ (hB θ)).mp hr).trans
      (mul_le_mul_of_nonneg_left (hupper θ) (by linarith))
  have hbdd : BddAbove (Set.range R) := ⟨(1 + ε) * S, by
    rintro _ ⟨θ, rfl⟩
    exact hRupper θ⟩
  have hsupper : sSup (Set.range R) ≤ (1 + ε) * S := by
    apply csSup_le ⟨R θ0, Set.mem_range_self θ0⟩
    rintro _ ⟨θ, rfl⟩
    exact hRupper θ
  have hrl : (1 - ε) * S ≤ R θ0 := by
    have hr : 1 - ε ≤ R θ0 / B θ0 := by linarith [(abs_le.mp (herr θ0)).1]
    simpa only [hθ0] using (le_div_iff₀ (hB θ0)).mp hr
  have hslower : (1 - ε) * S ≤ sSup (Set.range R) :=
    hrl.trans (le_csSup hbdd (Set.mem_range_self θ0))
  have hu : sSup (Set.range R) / S ≤ 1 + ε := (div_le_iff₀ hS).2 hsupper
  have hl : 1 - ε ≤ sSup (Set.range R) / S := (le_div_iff₀ hS).2 hslower
  refine ⟨hbdd, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith

/-- True uniform relative convergence gives convergence of the genuine
supremum ratio. Early rows may be unbounded; eventual boundedness is a
conclusion derived from the error and the actual benchmark envelope. -/
theorem uniform_sup_risk_ratio_tendsto {I Θ : Type*} {l : Filter I}
    (R B : I → Θ → ℝ) (S : I → ℝ)
    (hB : ∀ᶠ i in l, ∀ θ, 0 < B i θ)
    (hupper : ∀ᶠ i in l, ∀ θ, B i θ ≤ S i)
    (hattained : ∀ᶠ i in l, ∃ θ, B i θ = S i)
    (hratio : Tendsto (fun p : I × Θ => R p.1 p.2 / B p.1 p.2)
      (uniformFamilyFilter l Θ) (𝓝 1)) :
    (∀ᶠ i in l, BddAbove (Set.range (R i))) ∧
      Tendsto (fun i => sSup (Set.range (R i)) / S i) l (𝓝 1) := by
  have herr (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in l, ∀ θ, |R i θ / B i θ - 1| < ε := by
    simpa only [Real.dist_eq] using
      (tendsto_uniformFamilyFilter_iff (fun i θ => R i θ / B i θ) 1).mp hratio ε hε
  have hbdd : ∀ᶠ i in l, BddAbove (Set.range (R i)) := by
    filter_upwards [hB, hupper, hattained, herr 1 (by norm_num)] with i hBi hUi hAi hEi
    exact (sup_risk_relative_error_of_benchmark_attained (R i) (B i) (S i) 1
      (by norm_num) hBi hUi hAi (fun θ => (hEi θ).le)).1
  refine ⟨hbdd, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  filter_upwards [hB, hupper, hattained, herr (ε / 2) (by linarith)]
    with i hBi hUi hAi hEi
  have hi := (sup_risk_relative_error_of_benchmark_attained (R i) (B i) (S i) (ε / 2)
    (by linarith) hBi hUi hAi (fun θ => (hEi θ).le)).2
  exact (show dist (sSup (Set.range (R i)) / S i) 1 ≤ ε / 2 by
    simpa only [Real.dist_eq] using hi).trans_lt (by linarith)

end
end KernelSeq
