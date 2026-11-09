import KernelFoundations.SourceBall

/-!
# Actual source balls are positive-spectrum ellipsoids

The reverse implication synthesizes an actual vector in the supported
prediction Hilbert space from its square-summable coordinates. In particular,
the ellipsoid condition is not an assumed representation of the target.
-/

open MeasureTheory Submodule
open scoped ENNReal

namespace KernelFoundations
noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def predictionSourceCoordinate (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    (s : ℝ) (f : E) (i : PredictionSingularIndex S) : ℝ :=
  inner ℝ (predictionSingularBasis S hc i : E) f / i.1.1^(s/2)

/-- A finite-radius ellipsoid requires actual square summability, so the
totalized real `tsum` cannot admit a divergent coordinate sequence. -/
def predictionSourceEllipsoid (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s R : ℝ) : Set E :=
  {f | f ∈ PredictionRange S ∧
    Summable (fun i => predictionSourceCoordinate S hc s f i ^ 2) ∧
    (∑' i, predictionSourceCoordinate S hc s f i ^ 2) ≤ R^2}

theorem predictionSourceCoordinate_power (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    (g : E) (i : PredictionSingularIndex S) :
    predictionSourceCoordinate S hc s (predictionSourcePower S hc s hs g) i =
      inner ℝ (predictionSingularBasis S hc i : E) g := by
  rw [predictionSourceCoordinate, predictionSourcePower_coefficient]
  exact mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos i.2 _).ne'

theorem predictionSourceBall_subset_ellipsoid (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    {R : ℝ} (hR : 0 ≤ R) :
    predictionSourceBall S hc s hs R ⊆ predictionSourceEllipsoid S hc s R := by
  rintro f ⟨g, hg, hgR, rfl⟩
  refine ⟨predictionSourcePower_mem_predictionRange S hc s hs hg, ?_, ?_⟩
  · simpa only [predictionSourceCoordinate_power] using
      predictionSingularBasis_coefficients_summable S hc hg
  · simp_rw [predictionSourceCoordinate_power]
    rw [← predictionSingularBasis_parseval S hc hg]
    exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hgR

/-- Positive-spectrum square-summable inverse-power coefficients construct
the source vector in the actual closed prediction range. -/
theorem predictionSourceEllipsoid_subset_ball (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    {R : ℝ} (hR : 0 ≤ R) :
    predictionSourceEllipsoid S hc s R ⊆ predictionSourceBall S hc s hs R := by
  rintro f ⟨hf, hsum, hnorm⟩
  let b := predictionSingularBasis S hc
  let c : lp (fun _ : PredictionSingularIndex S => ℝ) 2 :=
    ⟨fun i => predictionSourceCoordinate S hc s f i,
      (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 (by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hsum)⟩
  let g : PredictionRange S := b.repr.symm c
  have hcg : b.repr g = c := b.repr.apply_symm_apply c
  have hgi (i : PredictionSingularIndex S) :
      inner ℝ (b i : E) (g : E) = predictionSourceCoordinate S hc s f i := by
    have he := congrArg (fun a : lp (fun _ : PredictionSingularIndex S => ℝ) 2 => a i) hcg
    simpa only [HilbertBasis.repr_apply_apply, Submodule.coe_inner, c] using he
  have hgnorm : ‖g‖^2 = ∑' i, predictionSourceCoordinate S hc s f i^2 := by
    calc
      ‖g‖ ^ 2 = ∑' i, inner ℝ (b i : E) (g : E) ^ 2 :=
        predictionSingularBasis_parseval S hc g.property
      _ = _ := tsum_congr fun i => congrArg (· ^ 2) (hgi i)
  have hgr : ‖(g : E)‖ ≤ R := by
    apply (sq_le_sq₀ (norm_nonneg _) hR).mp
    exact hgnorm.trans_le hnorm
  have hp := predictionSourcePower_mem_predictionRange S hc s hs g.property
  have he : predictionSourcePower S hc s hs (g : E) = f := by
    have hb : (⟨predictionSourcePower S hc s hs (g : E), hp⟩ : PredictionRange S) = ⟨f, hf⟩ := by
      apply b.repr.injective
      ext i
      simp only [HilbertBasis.repr_apply_apply, Submodule.coe_inner]
      change inner ℝ (b i : E) (predictionSourcePower S hc s hs (g : E)) = inner ℝ (b i : E) f
      rw [predictionSourcePower_coefficient, hgi, predictionSourceCoordinate]
      exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos i.2 _).ne'
    exact congrArg Subtype.val hb
  exact ⟨(g : E), g.property, hgr, he⟩

/-- The operator source ball and its positive-spectrum ellipsoid
are the same set, without countability or separability of the prediction space. -/
theorem predictionSourceBall_eq_ellipsoid (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    {R : ℝ} (hR : 0 ≤ R) :
    predictionSourceBall S hc s hs R = predictionSourceEllipsoid S hc s R :=
  Set.Subset.antisymm (predictionSourceBall_subset_ellipsoid S hc s hs hR)
    (predictionSourceEllipsoid_subset_ball S hc s hs hR)

end
end KernelFoundations
