import KernelSeq.FiniteSpectralCompression
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Passing actual finite compression tail bounds to the ambient operator

Countable directed compression limits transfer uniform tail bounds to the
strict tail of the limiting operator. The proof uses continuity from below of
outer measure and needs no new measurability certificate for the event.
There is no concentration inequality assumed or asserted by the limit lemma.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace KernelSeq

/-- A uniform eventual tail bound survives a pointwise directed limit.
The strict inequality in the limiting event is intentional. -/
theorem measure_gt_le_of_pointwise_tendsto {J Ω : Type*}
    [SemilatticeSup J] [Nonempty J] [Countable J] [MeasurableSpace Ω]
    (P : Measure Ω) (f : J → Ω → ℝ) (g : Ω → ℝ) (t : ℝ) (B : ℝ≥0∞)
    (hlim : ∀ ω, Tendsto (fun j => f j ω) atTop (𝓝 (g ω)))
    (hbound : ∀ᶠ j in atTop, P {ω | t ≤ f j ω} ≤ B) :
    P {ω | t < g ω} ≤ B := by
  let A : J → Set Ω := fun j => {ω | ∀ k, j ≤ k → t ≤ f k ω}
  have hmono : Monotone A := by
    intro j k hjk ω hω l hkl
    exact hω l (hjk.trans hkl)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hbound
  have hA (j : J) : P (A j) ≤ B := by
    apply (measure_mono (show A j ⊆ {ω | t ≤ f (j ⊔ j₀) ω} from
      fun ω hω => hω _ le_sup_left)).trans
    exact hj₀ _ le_sup_right
  have hsub : {ω | t < g ω} ⊆ ⋃ j, A j := by
    intro ω hω
    have he : ∀ᶠ j in atTop, t < f j ω :=
      (hlim ω).eventually (eventually_gt_nhds hω)
    obtain ⟨j, hj⟩ := eventually_atTop.mp he
    exact Set.mem_iUnion.mpr ⟨j, fun k hk => (hj k hk).le⟩
  calc
    P {ω | t < g ω} ≤ P (⋃ j, A j) := measure_mono hsub
    _ = ⨆ j, P (A j) := hmono.directed_le.measure_iUnion
    _ ≤ B := iSup_le hA

variable {ι H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace Ω]

/-- Actual two-sided finite compressions of genuine HS random operators give
the ambient strict tail. Countability is required only of the feature basis. -/
theorem measure_hs_norm_gt_le_of_compression_tails [Countable ι]
    (b : HilbertBasis ι ℝ H) (P : Measure Ω)
    (c : Ω → HilbertSchmidtColumns ι H) (t : ℝ) (B : ℝ≥0∞)
    (hbound : ∀ᶠ s : Finset ι in atTop,
      P {ω | t ≤ ‖finiteBasisProjection b s * hilbertSchmidtOperator b (c ω) *
        finiteBasisProjection b s‖} ≤ B) :
    P {ω | t < ‖hilbertSchmidtOperator b (c ω)‖} ≤ B := by
  classical
  apply measure_gt_le_of_pointwise_tendsto (J := Finset ι) P
    (fun s ω => ‖finiteBasisProjection b s * hilbertSchmidtOperator b (c ω) *
      finiteBasisProjection b s‖) _ t B _ hbound
  intro ω
  exact (hs_two_sided_compression_tendsto b (c ω)).norm

end KernelSeq
