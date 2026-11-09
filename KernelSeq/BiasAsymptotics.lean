import KernelSeq.BiasTransfer
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Deterministic asymptotic bias transfer

The limiting step for bias transfer under the operator-error bound
`u * ‖r‖ + c`. This file proves convergence
along arbitrary filters. It does not replace the manuscript's convergence in
probability or its upstream operator estimates.
-/

open Filter Topology

namespace KernelSeq

/-- The mixed error tends to zero whenever its squared variance-normalized
value does. Only eventual nonnegativity of `c` is needed; `V` may tend to zero. -/
theorem normalized_error_tendsto_zero {ι : Type*} {l : Filter ι}
    (c V : ι → ℝ) (hc : ∀ᶠ i in l, 0 ≤ c i)
    (hsmall : Tendsto (fun i => c i ^ 2 / V i) l (𝓝 0)) :
    Tendsto (fun i => c i / Real.sqrt (V i)) l (𝓝 0) := by
  have hs : Tendsto (fun i => Real.sqrt (c i ^ 2 / V i)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hsmall.sqrt
  apply hs.congr'
  filter_upwards [hc] with i hi
  rw [Real.sqrt_div (sq_nonneg (c i)), Real.sqrt_sq hi]

/-- Deterministic convergence of the full relative-risk error envelope.
The limiting calculation needs no boundedness assumptions on `c` or `V`. -/
theorem relativeRiskBound_tendsto_zero {ι : Type*} {l : Filter ι}
    (u c V : ι → ℝ) (hc : ∀ᶠ i in l, 0 ≤ c i)
    (hu : Tendsto u l (𝓝 0))
    (hsmall : Tendsto (fun i => c i ^ 2 / V i) l (𝓝 0)) :
    Tendsto (fun i => relativeRiskBound (u i) (c i) (V i)) l (𝓝 0) := by
  have hratio := normalized_error_tendsto_zero c V hc hsmall
  have hsum : Tendsto
      (fun i => 2 * u i + u i ^ 2 + (1 + u i) * (c i / Real.sqrt (V i)) +
        c i ^ 2 / V i) l (𝓝 (2 * 0 + 0 ^ 2 + (1 + 0) * 0 + 0)) :=
    (((tendsto_const_nhds.mul hu).add (hu.pow 2)).add
      ((tendsto_const_nhds.add hu).mul hratio)).add hsmall
  simpa [relativeRiskBound, mul_div_assoc] using hsum

/-- Total-risk normalized bias error vanishes under the manuscript's scalar
error balance, in the deterministic limit setting. The bias vectors may be
unbounded or zero; no division by their norms is used. -/
theorem deterministic_bias_transfer {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} (r e : ι → E) (u c V : ι → ℝ)
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i)
    (hc_nonneg : ∀ᶠ i in l, 0 ≤ c i)
    (hV : ∀ᶠ i in l, 0 < V i)
    (he : ∀ᶠ i in l, ‖e i‖ ≤ u i * ‖r i‖ + c i)
    (hu : Tendsto u l (𝓝 0))
    (hsmall : Tendsto (fun i => c i ^ 2 / V i) l (𝓝 0)) :
    Tendsto (fun i => |‖r i - e i‖ ^ 2 - ‖r i‖ ^ 2| /
      (‖r i‖ ^ 2 + V i)) l (𝓝 0) := by
  apply squeeze_zero' _ _ (relativeRiskBound_tendsto_zero u c V hc_nonneg hu hsmall)
  · filter_upwards [hV] with i hi
    exact div_nonneg (abs_nonneg _) (by positivity)
  · filter_upwards [hu_nonneg, hc_nonneg, hV, he] with i hui hci hVi hei
    exact bias_relative_risk_bound (r i) (e i) (u i) (c i) (V i) hui hci hVi hei

end KernelSeq
