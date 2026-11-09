import KernelSeq.FeatureEmbedding
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Linarith

/-!
# Canonical features of a scalar real RKHS

The feature is the actual evaluation representer from Mathlib's RKHS instance.
-/

open MeasureTheory TopologicalSpace Set

namespace KernelSeq

/-- A map into a second-countable metric space is measurable if its distances
to every point of its own range are measurable. This avoids a weak-measurability
assumption for canonical RKHS features. -/
theorem measurable_of_pairwise_dist {α β : Type*} [MeasurableSpace α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (f : α → β) (h : ∀ y, Measurable (fun x => dist (f x) (f y))) : Measurable f := by
  let g : α → Set.range f := fun x => ⟨f x, Set.mem_range_self x⟩
  have hgdist (y : Set.range f) : Measurable (fun x => dist (g x) y) := by
    rcases y.property with ⟨z, hz⟩
    simpa only [g, Subtype.dist_eq, hz] using h z
  let balls : Set (Set (Set.range f)) := {s | ∃ y r, s = Metric.ball y r}
  have hb : IsTopologicalBasis balls := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨y, r, rfl⟩
      exact Metric.isOpen_ball
    · intro y u hy hu
      rcases Metric.isOpen_iff.mp hu y hy with ⟨r, hr, hru⟩
      exact ⟨Metric.ball y r, ⟨y, r, rfl⟩, Metric.mem_ball_self hr, hru⟩
  have hg : Measurable g := by
    rw [(inferInstance : BorelSpace (Set.range f)).measurable_eq, hb.borel_eq_generateFrom]
    apply measurable_generateFrom
    rintro s ⟨y, r, rfl⟩
    exact measurableSet_lt (hgdist y) measurable_const
  exact measurable_subtype_coe.comp hg

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ]

/-- Canonical feature vector representing evaluation at `x`. -/
noncomputable def rkhsFeature (x : X) : H := RKHS.kerFun H x (1 : ℝ)

@[simp] theorem rkhsFeature_inner (x : X) (h : H) :
    inner ℝ (rkhsFeature (X := X) (H := H) x) h = h x := by
  simp [rkhsFeature]

@[simp] theorem inner_rkhsFeature (x : X) (h : H) :
    inner ℝ h (rkhsFeature (X := X) (H := H) x) = h x := by
  rw [real_inner_comm, rkhsFeature_inner]

/-- Scalar kernel associated to the actual RKHS. -/
noncomputable def rkhsKernel (x y : X) : ℝ := RKHS.kernel H x y (1 : ℝ)

@[simp] theorem rkhsFeature_apply (x y : X) :
    rkhsFeature (X := X) (H := H) y x = rkhsKernel (X := X) (H := H) x y :=
  RKHS.kerFun_apply H y 1 x

@[simp] theorem rkhsFeature_norm_sq (x : X) :
    ‖rkhsFeature (X := X) (H := H) x‖ ^ 2 = rkhsKernel (X := X) (H := H) x x := by
  rw [← real_inner_self_eq_norm_sq, rkhsFeature_inner, rkhsFeature_apply]

/-- Joint kernel measurability implies measurable diagonal and sections. -/
theorem rkhsKernel_measurable_diagonal [MeasurableSpace X]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2)) :
    Measurable (fun x : X => rkhsKernel (X := X) (H := H) x x) :=
  Measurable.comp (g := fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2)
    (f := fun x : X => (x, x)) hK (measurable_id.prodMk measurable_id)

theorem rkhsKernel_measurable_section [MeasurableSpace X]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2)) (y : X) :
    Measurable (fun x : X => rkhsKernel (X := X) (H := H) x y) :=
  Measurable.comp (g := fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2)
    (f := fun x : X => (x, y)) hK (measurable_id.prodMk measurable_const)

/-- The diagonal kernel bound controls canonical feature norms. -/
theorem rkhsFeature_norm_le (κ : ℝ) (hκ : 0 ≤ κ)
    (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2) (x : X) :
    ‖rkhsFeature (X := X) (H := H) x‖ ≤ κ := by
  have h := hdiag x
  rw [← rkhsFeature_norm_sq] at h
  nlinarith [norm_nonneg (rkhsFeature (X := X) (H := H) x)]

/-- Pairwise distances of feature vectors are measurable from the joint kernel. -/
theorem rkhsFeature_measurable_dist [MeasurableSpace X]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2)) (y : X) :
    Measurable (fun x => dist (rkhsFeature (X := X) (H := H) x) (rkhsFeature (X := X) (H := H) y)) := by
  have hm := ((rkhsKernel_measurable_diagonal hK).sub
    ((rkhsKernel_measurable_section hK y).const_mul 2)).add_const (rkhsKernel (X := X) (H := H) y y)
  convert hm.sqrt using 1
  funext x
  rw [dist_eq_norm, ← rkhsFeature_norm_sq, ← rkhsFeature_norm_sq,
    ← rkhsFeature_apply (X := X) (H := H) x y, ← rkhsFeature_inner x (rkhsFeature (X := X) (H := H) y),
    ← norm_sub_sq_real, Real.sqrt_sq (norm_nonneg _)]

/-- A jointly measurable scalar kernel in a separable RKHS has a strongly
measurable canonical feature map. No feature-measurability hypothesis is added. -/
theorem rkhsFeature_stronglyMeasurable [MeasurableSpace X] [SecondCountableTopology H]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2)) :
    StronglyMeasurable (rkhsFeature (X := X) (H := H)) := by
  letI : MeasurableSpace H := borel H
  letI : BorelSpace H := ⟨rfl⟩
  exact (measurable_of_pairwise_dist _ (rkhsFeature_measurable_dist hK)).stronglyMeasurable

/-- Every RKHS function is measurable under the same kernel assumptions. -/
theorem rkhsFunction_measurable [MeasurableSpace X] [SecondCountableTopology H]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2)) (h : H) :
    Measurable (fun x : X => h x) := by
  have hm := ((rkhsFeature_stronglyMeasurable hK).inner (𝕜 := ℝ)
    (stronglyMeasurable_const : StronglyMeasurable (fun _ : X => h))).measurable
  simpa only [rkhsFeature_inner] using hm

/-- The actual canonical feature belongs to `L²` on every finite measure space. -/
theorem rkhsFeature_memLp [MeasurableSpace X] [SecondCountableTopology H]
    (μ : Measure X) [IsFiniteMeasure μ]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2) :
    MemLp (rkhsFeature (X := X) (H := H)) 2 μ := by
  apply feature_memLp_of_bound μ _ (rkhsFeature_stronglyMeasurable hK).aestronglyMeasurable κ
  exact Filter.Eventually.of_forall (rkhsFeature_norm_le κ hκ hdiag)

/-- The actual canonical RKHS embedding, with measurability and integrability proved. -/
noncomputable def rkhsEmbedding [MeasurableSpace X] [SecondCountableTopology H]
    (μ : Measure X) [IsFiniteMeasure μ]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2) :
    H →L[ℝ] Lp ℝ 2 μ :=
  featureEmbedding μ (rkhsFeature (X := X) (H := H)) (rkhsFeature_memLp μ hK κ hκ hdiag)

/-- The embedding sends a RKHS function to precisely its almost-everywhere class. -/
theorem rkhsEmbedding_ae [MeasurableSpace X] [SecondCountableTopology H]
    (μ : Measure X) [IsFiniteMeasure μ]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2) (h : H) :
    rkhsEmbedding μ hK κ hκ hdiag h =ᵐ[μ] fun x => h x := by
  simpa only [rkhsEmbedding, rkhsFeature_inner] using
    featureEmbedding_ae μ (rkhsFeature (X := X) (H := H))
      (rkhsFeature_memLp μ hK κ hκ hdiag) h

/-- The standard `κ` bound for the canonical prediction embedding. -/
theorem rkhsEmbedding_norm_le [MeasurableSpace X] [SecondCountableTopology H]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2) :
    ‖rkhsEmbedding μ hK κ hκ hdiag‖ ≤ κ := by
  apply featureEmbedding_norm_le μ _ _ κ hκ
  exact Filter.Eventually.of_forall (rkhsFeature_norm_le κ hκ hdiag)

end KernelSeq
