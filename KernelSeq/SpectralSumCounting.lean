import KernelSeq.SpectralCounting
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Counting functions for exact spectral-sum asymptotics

The counting function is the actual counting measure of the eigenvalue
superlevel set. Exact polynomial counting gives a global power envelope;
no Potter estimate or spectral-sum limit is assumed.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

/-- The actual number of sequence entries at least `t`, with multiplicities.
All uses are at positive thresholds, where summability makes this finite. -/
def spectralCounting (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  (Measure.count {j : ℕ | t ≤ w j}).toReal

theorem spectralCounting_nonneg (w : ℕ → ℝ) (t : ℝ) : 0 ≤ spectralCounting w t :=
  ENNReal.toReal_nonneg

theorem measurable_spectralCounting (w : ℕ → ℝ) : Measurable (spectralCounting w) := by
  have hm : Antitone (fun t : ℝ => Measure.count {j : ℕ | t ≤ w j}) := by
    intro s t hst
    exact measure_mono (fun j hj => hst.trans hj)
  exact hm.measurable.ennreal_toReal

theorem finite_spectrum_above {w : ℕ → ℝ} (hs : Summable w) {t : ℝ} (ht : 0 < t) :
    {j | t ≤ w j}.Finite := by
  have he := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds ht)
  change {j | w j < t} ∈ cofinite at he
  simpa only [Set.compl_setOf, not_lt] using mem_cofinite.mp he

theorem spectralCounting_eq_ncard {w : ℕ → ℝ} (hs : Summable w) {t : ℝ} (ht : 0 < t) :
    spectralCounting w t = ({j | t ≤ w j}.ncard : ℝ) := by
  have hfin := finite_spectrum_above hs ht
  have hset : {j | t ≤ w j} = (hfin.toFinset : Set ℕ) := by ext j; simp
  change (Measure.count {j | t ≤ w j}).toReal = _
  calc
    _ = (Measure.count (hfin.toFinset : Set ℕ)).toReal := congrArg (fun s => (Measure.count s).toReal) hset
    _ = (hfin.toFinset.card : ℝ) := by rw [Measure.count_apply_finset, ENNReal.toReal_natCast]
    _ = _ := by exact_mod_cast (Set.ncard_eq_toFinset_card _ hfin).symm

theorem spectralCounting_antitone_pos {w : ℕ → ℝ} (hs : Summable w)
    {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) : spectralCounting w t ≤ spectralCounting w s := by
  rw [spectralCounting_eq_ncard hs (hs0.trans_le hst), spectralCounting_eq_ncard hs hs0]
  exact_mod_cast Set.ncard_le_ncard (fun j hj => hst.trans hj) (finite_spectrum_above hs hs0)

theorem spectralCounting_eq_zero_of_gt_tsum {w : ℕ → ℝ} (hs : Summable w)
    (hw : ∀ j, 0 ≤ w j) {t : ℝ} (ht : (∑' j, w j) < t) : spectralCounting w t = 0 := by
  have hset : {j | t ≤ w j} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro j hj
    exact (ht.trans_le hj).not_ge (hs.le_tsum j (fun i _ => hw i))
  simp [spectralCounting, hset]

/-- Exact power counting implies a global normalized-count envelope. This
uses the actual finite trace to cover thresholds away from zero. -/
theorem spectralCounting_global_power_bound {w : ℕ → ℝ} (hs : Summable w)
    (hw : ∀ j, 0 ≤ w j) {γ D : ℝ} (hγ : 0 ≤ γ)
    (hcount : Tendsto (fun t => t ^ γ * spectralCounting w t) (𝓝[>] 0) (𝓝 D)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t, 0 < t → t ^ γ * spectralCounting w t ≤ C := by
  have he := hcount.eventually (gt_mem_nhds (by linarith : D < D + 1))
  obtain ⟨δ, hδ, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  let M := (∑' j, w j) + 1
  have htrace0 : 0 ≤ ∑' j, w j := tsum_nonneg hw
  have hM : 0 < M := by dsimp only [M]; linarith
  let C := (|D| + 1) + M ^ γ * spectralCounting w δ + 1
  have hCN : 0 ≤ M ^ γ * spectralCounting w δ :=
    mul_nonneg (Real.rpow_nonneg hM.le _) (spectralCounting_nonneg _ _)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro t ht
  by_cases htδ : t < δ
  · have hl := hlocal ⟨ht, htδ⟩
    change t ^ γ * spectralCounting w t < D + 1 at hl
    dsimp only [C]
    linarith [le_abs_self D]
  · by_cases htM : M ≤ t
    · have hz := spectralCounting_eq_zero_of_gt_tsum hs hw
        (show (∑' j, w j) < t by dsimp only [M] at htM; linarith)
      rw [hz, mul_zero]
      dsimp only [C]
      positivity
    · have hN := spectralCounting_antitone_pos hs hδ (le_of_not_gt htδ)
      have hp := Real.rpow_le_rpow ht.le (le_of_not_ge htM) hγ
      have hb := mul_le_mul hp hN (spectralCounting_nonneg _ _) (Real.rpow_nonneg hM.le _)
      dsimp only [C]
      linarith [abs_nonneg D]

/-- Scaling the actual counting asymptotic is a pointwise limit on every
strictly positive spectral coordinate. -/
theorem spectralCounting_scaled_tendsto {w : ℕ → ℝ} {γ D u : ℝ} (hu : 0 < u)
    (hcount : Tendsto (fun t => t ^ γ * spectralCounting w t) (𝓝[>] 0) (𝓝 D)) :
    Tendsto (fun lam => lam ^ γ * spectralCounting w (lam * u)) (𝓝[>] 0)
      (𝓝 (D * u ^ (-γ))) := by
  have hmap : Tendsto (fun lam : ℝ => lam * u) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh : Tendsto (fun lam : ℝ => lam * u) (𝓝 0) (𝓝 (0 * u)) :=
        (continuousAt_id.mul continuousAt_const).tendsto
      simpa only [zero_mul] using hh.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact mul_pos hlam hu
  have hlim := (hcount.comp hmap).mul_const (u ^ (-γ))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  simp only [Function.comp_apply]
  rw [Real.mul_rpow hlam.le hu.le]
  have hpow : u ^ γ * u ^ (-γ) = 1 := by rw [← Real.rpow_add hu]; simp
  calc
    _ = lam ^ γ * spectralCounting w (lam * u) * (u ^ γ * u ^ (-γ)) := by ring
    _ = _ := by rw [hpow, mul_one]

section ActualSpectrum

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

theorem summable_enumerated_covariance_eigenvalues (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk)) :
    Summable (fun j => (e j).1.1) :=
  e.summable_iff.mpr (summable_positive_covariance_eigenvalues k hk)

/-- This counting function is exactly the count of the actual population
spectrum under a bijective multiplicity-preserving enumeration. -/
theorem spectralCounting_eq_featureSpectralCount (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk)) {t : ℝ} (ht : 0 < t) :
    spectralCounting (fun j => (e j).1.1) t = (featureSpectralCount k hk t : ℝ) := by
  rw [spectralCounting_eq_ncard (summable_enumerated_covariance_eigenvalues k hk e) ht]
  have he : {j : ℕ | t ≤ (e j).1.1} ≃
      {i : PredictionSingularIndex (featureEmbedding μ k hk) | t ≤ i.1.1} :=
    { toFun := fun j => ⟨e j, j.property⟩
      invFun := fun i => ⟨e.symm i, by
        change t ≤ (e (e.symm i.val)).1.1
        rw [e.apply_symm_apply]
        exact i.property⟩
      left_inv := fun j => Subtype.ext (e.symm_apply_apply j.val)
      right_inv := fun i => Subtype.ext (e.apply_symm_apply i.val) }
  exact_mod_cast Set.ncard_congr' he

end ActualSpectrum

end
end KernelSeq
