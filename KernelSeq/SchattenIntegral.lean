import KernelSeq.SchattenAdjoint
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Continuous actual Schatten seminorms and their Bochner integral bound

The actual `S_p` quantity, restricted to HS columns, is dominated by the HS
norm and is 1-Lipschitz in that complete Hilbert space. Hahn--Banach for a
continuous real seminorm gives its integral inequality on arbitrary measures.
No complete Schatten Banach space or integral Minkowski theorem is assumed.
-/

open MeasureTheory Submodule Filter

namespace KernelSeq

noncomputable section

variable {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual `S_p` quantity is dominated by the HS column norm for `p ≥ 2`. -/
theorem hsSchattenNorm_le_hsNorm (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) : hsSchattenNorm b c p ≤ ‖c‖ := by
  have hp0 : 0 < p := by linarith
  have hq : 0 ≤ 1 - 2 / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp)
  have ht : 0 ≤ 2 / p := div_nonneg (by norm_num) hp0.le
  calc
    _ ≤ ‖hilbertSchmidtOperator b c‖ ^ (1 - 2 / p) * ‖c‖ ^ (2 / p) :=
      hsSchattenNorm_le_opNorm_mul_hsNorm b c hp
    _ ≤ ‖c‖ ^ (1 - 2 / p) * ‖c‖ ^ (2 / p) := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hilbertSchmidtOperator_le b c) hq)
      (Real.rpow_nonneg (norm_nonneg _) _)
    _ = ‖c‖ := by
      rw [← Real.rpow_add_of_nonneg (norm_nonneg c) hq ht,
        show 1 - 2 / p + 2 / p = (1 : ℝ) by ring, Real.rpow_one]

/-- The proved actual quantity as a seminorm on the original HS Hilbert
space. This does not alter the HS norm or assert Schatten completeness. -/
def hsSchattenSeminorm (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p) :
    Seminorm ℝ (HilbertSchmidtColumns ι E) :=
  Seminorm.of (fun c => hsSchattenNorm b c p) (fun c d => hsSchattenNorm_add_le b c d hp)
    (fun a c => by simpa only [Real.norm_eq_abs] using hsSchattenNorm_smul b c a hp)

@[simp]
theorem hsSchattenSeminorm_apply (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p)
    (c : HilbertSchmidtColumns ι E) : hsSchattenSeminorm b hp c = hsSchattenNorm b c p := rfl

theorem hsSchattenNorm_sub_le (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p)
    (c d : HilbertSchmidtColumns ι E) : |hsSchattenNorm b c p - hsSchattenNorm b d p| ≤ ‖c - d‖ := by
  exact ((hsSchattenSeminorm b hp).norm_sub_map_le_sub c d).trans
    (hsSchattenNorm_le_hsNorm b (c - d) hp)

theorem hsSchattenNorm_lipschitz (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p) :
    LipschitzWith 1 (fun c : HilbertSchmidtColumns ι E => hsSchattenNorm b c p) := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using hsSchattenNorm_sub_le b hp c d

theorem hsSchattenNorm_continuous (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p) :
    Continuous (fun c : HilbertSchmidtColumns ι E => hsSchattenNorm b c p) :=
  (hsSchattenNorm_lipschitz b hp).continuous

theorem hsSchattenNorm_convex (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p) :
    ConvexOn ℝ Set.univ (fun c : HilbertSchmidtColumns ι E => hsSchattenNorm b c p) :=
  (hsSchattenSeminorm b hp).convexOn

section ContinuousSeminorm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuous seminorm has a continuous norming real functional at each
point, proved from Mathlib's seminorm Hahn--Banach extension theorem. -/
theorem continuousSeminorm_exists_norming_dual (s : Seminorm ℝ V) (hs : Continuous s) (x : V) :
    ∃ g : V →L[ℝ] ℝ, g x = s x ∧ ∀ y, |g y| ≤ s y := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, fun y => ?_⟩
    · simp only [hx, map_zero]
    · simpa only [_root_.zero_apply, abs_zero] using apply_nonneg s y
  · let S : Submodule ℝ V := ℝ ∙ x
    let coord : S ≃ₗ[ℝ] ℝ := LinearEquiv.coord ℝ V x hx
    let f : Module.Dual ℝ S := s x • coord.toLinearMap
    have hf (y : S) : f y ≤ s (y : V) := by
      have hy : coord y • x = (y : V) := LinearEquiv.coord_apply_smul ℝ V x hx y
      have hsval : s (y : V) = |coord y| * s x := by
        rw [← hy, map_smul_eq_mul, Real.norm_eq_abs]
      change s x * coord y ≤ s (y : V)
      rw [hsval]
      nlinarith [mul_le_mul_of_nonneg_right (le_abs_self (coord y)) (apply_nonneg s x)]
    obtain ⟨g, hg, hdom⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm_real S f hs hf
    refine ⟨g, ?_, hdom⟩
    calc
      g x = g (⟨x, Submodule.mem_span_singleton_self x⟩ : S) := rfl
      _ = f ⟨x, Submodule.mem_span_singleton_self x⟩ := hg _
      _ = s x := by
        change s x * coord ⟨x, Submodule.mem_span_singleton_self x⟩ = s x
        rw [LinearEquiv.coord_self, mul_one]

variable [CompleteSpace V]

/-- The integral inequality for a continuous real seminorm, on an arbitrary
measure. Integrability of the seminorm will be derived for actual `S_p` below. -/
theorem continuousSeminorm_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Seminorm ℝ V) (hs : Continuous s) (F : Ω → V) (hF : Integrable F μ)
    (hsF : Integrable (fun ω => s (F ω)) μ) : s (∫ ω, F ω ∂μ) ≤ ∫ ω, s (F ω) ∂μ := by
  obtain ⟨g, hg, hdom⟩ := continuousSeminorm_exists_norming_dual s hs (∫ ω, F ω ∂μ)
  calc
    _ = g (∫ ω, F ω ∂μ) := hg.symm
    _ = ∫ ω, g (F ω) ∂μ := (g.integral_comp_comm hF).symm
    _ ≤ _ := integral_mono (g.integrable_comp hF) hsF
      (fun ω => (le_abs_self _).trans (hdom (F ω)))

end ContinuousSeminorm

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- HS integrability itself supplies integrability of the actual Schatten
quantity; this is not an extra premise of the final integral inequality. -/
theorem integrable_hsSchattenNorm (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p)
    {F : Ω → HilbertSchmidtColumns ι E} (hF : Integrable F μ) :
    Integrable (fun ω => hsSchattenNorm b (F ω) p) μ := by
  apply hF.norm.mono' ((hsSchattenNorm_continuous b hp).comp_aestronglyMeasurable hF.aestronglyMeasurable)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hsSchattenNorm_nonneg b (F ω) p)]
    exact hsSchattenNorm_le_hsNorm b (F ω) hp

/-- The true actual Schatten integral bound for HS-Bochner-integrable
operator columns, over arbitrary measures, with no probability/finite-mass
assumption and no unproved integral Minkowski or Schatten-completeness premise. -/
theorem hsSchattenNorm_integral_le (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p)
    (F : Ω → HilbertSchmidtColumns ι E) (hF : Integrable F μ) :
    hsSchattenNorm b (∫ ω, F ω ∂μ) p ≤ ∫ ω, hsSchattenNorm b (F ω) p ∂μ :=
  continuousSeminorm_integral_le (hsSchattenSeminorm b hp) (hsSchattenNorm_continuous b hp)
    F hF (integrable_hsSchattenNorm b hp hF)

theorem hsSchattenNorm_integral_le_of_ae_bound (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p)
    (F : Ω → HilbertSchmidtColumns ι E) (hF : Integrable F μ)
    (a : Ω → ℝ) (ha : Integrable a μ)
    (hbound : ∀ᵐ ω ∂μ, hsSchattenNorm b (F ω) p ≤ a ω) :
    hsSchattenNorm b (∫ ω, F ω ∂μ) p ≤ ∫ ω, a ω ∂μ :=
  (hsSchattenNorm_integral_le b hp F hF).trans
    (integral_mono_ae (integrable_hsSchattenNorm b hp hF) ha hbound)

omit [CompleteSpace H] in
/-- Integration commutes with the actual operator reconstruction, so the
integrated columns represent the genuine Bochner-integrated bounded operator. -/
theorem hilbertSchmidtOperator_integral (b : HilbertBasis ι ℝ H)
    (F : Ω → HilbertSchmidtColumns ι E) (hF : Integrable F μ) :
    hilbertSchmidtOperator b (∫ ω, F ω ∂μ) = ∫ ω, hilbertSchmidtOperator b (F ω) ∂μ :=
  ((hilbertSchmidtOperator b).integral_comp_comm hF).symm

end Integral

end
end KernelSeq
