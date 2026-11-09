import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Conditional noise moments and independent observation blocks

These are measure-theoretic bridges for the full observation-pair model.
No conditional probability kernels, disintegration, or standard Borel hypotheses
are used. Conditional expectations are with respect to explicit sub-sigma-algebras.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory ProbabilityTheory

namespace KernelSeq

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure Ω}

/-- Factor the integral on a rectangle from two independent sigma-algebras.
The integrand belongs to the first sigma-algebra. -/
theorem independent_setIntegral_inter {m₁ m₂ : MeasurableSpace Ω}
    (h₁ : m₁ ≤ m₀) (h₂ : m₂ ≤ m₀) (hind : Indep m₁ m₂ P)
    (f : Ω → ℝ) (hfm : StronglyMeasurable[m₁] f)
    {s t : Set Ω} (hs : MeasurableSet[m₁] s) (ht : MeasurableSet[m₂] t) :
    (∫ ω in s ∩ t, f ω ∂P) = (∫ ω in s, f ω ∂P) * P.real t := by
  let F := s.indicator f
  let G := t.indicator (fun _ : Ω => (1 : ℝ))
  have hF : Measurable[m₁] F := hfm.measurable.indicator hs
  have hG : Measurable[m₂] G := measurable_const.indicator ht
  have hFG : IndepFun F G P := by
    apply (IndepFun_iff _ _ _).2
    intro u v hu hv
    exact ((Indep_iff _ _ _).mp hind) _ _ (hF.comap_le _ hu) (hG.comap_le _ hv)
  have h := hFG.integral_fun_mul_eq_mul_integral
    (hF.mono h₁ le_rfl).aestronglyMeasurable (hG.mono h₂ le_rfl).aestronglyMeasurable
  have hid : (fun ω => F ω * G ω) = (s ∩ t).indicator f := by
    funext ω
    by_cases hsω : ω ∈ s <;> by_cases htω : ω ∈ t <;> simp [F, G, hsω, htω]
  rw [hid, integral_indicator ((h₁ _ hs).inter (h₂ _ ht)),
    show (∫ ω, F ω ∂P) = ∫ ω in s, f ω ∂P from integral_indicator (h₁ _ hs),
    show (∫ ω, G ω ∂P) = P.real t by simp [G, integral_indicator (h₂ _ ht)]] at h
  exact h

/-- Rectangle generators for the join of two sigma-algebras. -/
def sigmaRectangles (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ u v, MeasurableSet[m₁] u ∧ MeasurableSet[m₂] v ∧ s = u ∩ v}

theorem sigmaRectangles_isPiSystem (m₁ m₂ : MeasurableSpace Ω) :
    IsPiSystem (sigmaRectangles m₁ m₂) := by
  intro s hs t ht _
  obtain ⟨u, v, hu, hv, rfl⟩ := hs
  obtain ⟨u', v', hu', hv', rfl⟩ := ht
  refine ⟨u ∩ u', v ∩ v', hu.inter hu', hv.inter hv', ?_⟩
  ext ω
  simp only [mem_inter_iff]
  tauto

theorem generateFrom_sigmaRectangles (m₁ m₂ : MeasurableSpace Ω) :
    MeasurableSpace.generateFrom (sigmaRectangles m₁ m₂) = m₁ ⊔ m₂ := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨u, v, hu, hv, rfl⟩
    exact ((le_sup_left : m₁ ≤ m₁ ⊔ m₂) _ hu).inter ((le_sup_right : m₂ ≤ m₁ ⊔ m₂) _ hv)
  · apply sup_le
    · intro s hs
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨s, Set.univ, hs, MeasurableSet.univ, by simp⟩
    · intro s hs
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨Set.univ, s, MeasurableSet.univ, hs, by simp⟩

/-- If own-design conditional mean is zero, adding an independent observation
sigma-algebra does not change it. The noise need only be measurable with
respect to its full own observation block, not its own design. -/
theorem condExp_sup_eq_zero_of_indep [IsProbabilityMeasure P]
    {mD mPair mOther : MeasurableSpace Ω}
    (hDP : mD ≤ mPair) (hPair : mPair ≤ m₀) (hOther : mOther ≤ m₀)
    (f : Ω → ℝ) (hf : Integrable f P) (hfm : StronglyMeasurable[mPair] f)
    (hind : Indep mPair mOther P)
    (hown : P[f | mD] =ᵐ[P] (fun _ => 0)) :
    P[f | mD ⊔ mOther] =ᵐ[P] (fun _ => 0) := by
  have hD : mD ≤ m₀ := hDP.trans hPair
  have hsup : mD ⊔ mOther ≤ m₀ := sup_le hD hOther
  have hownInt (s : Set Ω) (hs : MeasurableSet[mD] s) :
      (∫ ω in s, f ω ∂P) = 0 := by
    rw [← setIntegral_condExp hD hf hs]
    exact (integral_congr_ae (ae_restrict_of_ae hown)).trans (by simp)
  have htotal : (∫ ω, f ω ∂P) = 0 := by
    simpa only [setIntegral_univ] using hownInt Set.univ MeasurableSet.univ
  have hrect (s : Set Ω) (hs : s ∈ sigmaRectangles mD mOther) :
      (∫ ω in s, f ω ∂P) = 0 := by
    obtain ⟨u, v, hu, hv, rfl⟩ := hs
    rw [independent_setIntegral_inter hPair hOther hind f hfm (hDP _ hu) hv,
      hownInt u hu, zero_mul]
  have hall (s : Set Ω) (hs : MeasurableSet[mD ⊔ mOther] s) :
      (∫ ω in s, f ω ∂P) = 0 := by
    induction s, hs using MeasurableSpace.induction_on_inter
      (generateFrom_sigmaRectangles mD mOther).symm (sigmaRectangles_isPiSystem mD mOther) with
    | empty => simp
    | basic s hs => exact hrect s hs
    | compl s hs ih => rw [setIntegral_compl (hsup _ hs) hf, htotal, ih, sub_self]
    | iUnion s hdisj hs ih =>
      rw [integral_iUnion (fun i => hsup _ (hs i)) hdisj hf.integrableOn]
      simp only [ih, tsum_zero]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hsup hf
    (fun s _ _ => integrableOn_zero) (fun s hs _ => ?_)
    stronglyMeasurable_const.aestronglyMeasurable).symm
  simpa only [integral_zero] using (hall s hs).symm

/-- A zero conditional expectation remains zero after reducing the conditioning
sigma-algebra (the tower property). -/
theorem condExp_zero_of_condExp_zero_of_le [IsProbabilityMeasure P]
    {mSmall mLarge : MeasurableSpace Ω} (hSL : mSmall ≤ mLarge) (hLarge : mLarge ≤ m₀)
    (f : Ω → ℝ) (hzero : P[f | mLarge] =ᵐ[P] (fun _ => 0)) :
    P[f | mSmall] =ᵐ[P] (fun _ => 0) := by
  have htower := condExp_condExp_of_le (μ := P) (f := f) hSL hLarge
  have hcongr := condExp_congr_ae (m := mSmall) hzero
  exact htower.symm.trans (hcongr.trans (by simp))

/-- One independent observation block is independent of the join of all other
observation blocks. No finite index or identical-distribution hypothesis is used. -/
theorem independent_block_rest {ι : Type*} {mPair : ι → MeasurableSpace Ω}
    (hm : ∀ j, mPair j ≤ m₀) (hind : iIndep mPair P) (i : ι) :
    Indep (mPair i) (⨆ j, ⨆ (_ : j ≠ i), mPair j) P := by
  classical
  have hd : Disjoint ({i} : Set ι) {j | j ≠ i} := by
    rw [Set.disjoint_left]
    intro j hj hj'
    exact hj' (Set.mem_singleton_iff.mp hj)
  have h := indep_iSup_of_disjoint hm hind hd
  simpa only [Set.mem_singleton_iff, Set.mem_setOf_eq, iSup_iSup_eq_left] using h

/-- The full design sigma-algebra is contained in own design together with the
other full observation blocks. -/
theorem allDesigns_le_ownDesign_sup_rest {ι : Type*}
    (mD mPair : ι → MeasurableSpace Ω) (hDP : ∀ j, mD j ≤ mPair j) (i : ι) :
    (⨆ j, mD j) ≤ mD i ⊔ (⨆ j, ⨆ (_ : j ≠ i), mPair j) := by
  apply iSup_le
  intro j
  by_cases hji : j = i
  · simpa only [hji] using (le_sup_left : mD i ≤ mD i ⊔ (⨆ j, ⨆ (_ : j ≠ i), mPair j))
  · calc
      mD j ≤ mPair j := hDP j
      _ ≤ ⨆ (_ : j ≠ i), mPair j := le_iSup (fun _ : j ≠ i => mPair j) hji
      _ ≤ ⨆ j, ⨆ (_ : j ≠ i), mPair j :=
        le_iSup (fun k => ⨆ (_ : k ≠ i), mPair k) j
      _ ≤ _ := le_sup_right

/-- Own-design zero conditional moments lift to conditioning on all designs,
using independence of the actual full observation sigma-algebras. -/
theorem condExp_allDesigns_eq_zero_of_independent_blocks [IsProbabilityMeasure P]
    {ι : Type*} (mD mPair : ι → MeasurableSpace Ω)
    (hDP : ∀ j, mD j ≤ mPair j) (hm : ∀ j, mPair j ≤ m₀)
    (hind : iIndep mPair P) (i : ι) (f : Ω → ℝ)
    (hf : Integrable f P) (hfm : StronglyMeasurable[mPair i] f)
    (hown : P[f | mD i] =ᵐ[P] (fun _ => 0)) :
    P[f | ⨆ j, mD j] =ᵐ[P] (fun _ => 0) := by
  have hrest : (⨆ j, ⨆ (_ : j ≠ i), mPair j) ≤ m₀ :=
    iSup_le fun j => iSup_le fun _ => hm j
  have hlarge := condExp_sup_eq_zero_of_indep (hDP i) (hm i) hrest f hf hfm
    (independent_block_rest hm hind i) hown
  exact condExp_zero_of_condExp_zero_of_le
    (allDesigns_le_ownDesign_sup_rest mD mPair hDP i) (sup_le ((hDP i).trans (hm i)) hrest)
    f hlarge

/-- Constant own-design conditional moments also lift to all designs. -/
theorem condExp_allDesigns_eq_const_of_independent_blocks [IsProbabilityMeasure P]
    {ι : Type*} (mD mPair : ι → MeasurableSpace Ω)
    (hDP : ∀ j, mD j ≤ mPair j) (hm : ∀ j, mPair j ≤ m₀)
    (hind : iIndep mPair P) (i : ι) (f : Ω → ℝ) (c : ℝ)
    (hf : Integrable f P) (hfm : StronglyMeasurable[mPair i] f)
    (hown : P[f | mD i] =ᵐ[P] (fun _ => c)) :
    P[f | ⨆ j, mD j] =ᵐ[P] (fun _ => c) := by
  have hD : mD i ≤ m₀ := (hDP i).trans (hm i)
  have hAll : (⨆ j, mD j) ≤ m₀ := iSup_le fun j => (hDP j).trans (hm j)
  have hcenter : P[(fun ω => f ω - c) | mD i] =ᵐ[P] (fun _ => 0) := by
    have hsub := condExp_sub hf (integrable_const c) (mD i)
    filter_upwards [hsub, hown] with ω hs ho
    simpa only [Pi.sub_def, ho, condExp_const hD, sub_self] using hs
  have hlarge := condExp_allDesigns_eq_zero_of_independent_blocks mD mPair hDP hm hind i
    (fun ω => f ω - c) (hf.sub (integrable_const c)) (hfm.sub stronglyMeasurable_const) hcenter
  have hsub := condExp_sub hf (integrable_const c) (⨆ j, mD j)
  filter_upwards [hlarge, hsub] with ω hz hs
  simp only [Pi.sub_def, condExp_const hAll] at hs
  linarith

/-- Cross moments vanish conditionally on all designs. The proof first
conditions on own design and all other full observation blocks, then pulls out
the other noise coordinate and applies the tower property. -/
theorem condExp_cross_allDesigns_eq_zero [IsProbabilityMeasure P]
    {ι : Type*} (mD mPair : ι → MeasurableSpace Ω)
    (hDP : ∀ j, mD j ≤ mPair j) (hm : ∀ j, mPair j ≤ m₀)
    (hind : iIndep mPair P) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, MemLp (ξ i) 2 P)
    (hξm : ∀ i, StronglyMeasurable[mPair i] (ξ i))
    (hmean : ∀ i, P[ξ i | mD i] =ᵐ[P] (fun _ => 0))
    (i j : ι) (hji : j ≠ i) :
    P[(fun ω => ξ i ω * ξ j ω) | ⨆ k, mD k] =ᵐ[P] (fun _ => 0) := by
  let rest := ⨆ k, ⨆ (_ : k ≠ i), mPair k
  let large := mD i ⊔ rest
  have hrest : rest ≤ m₀ := iSup_le fun k => iSup_le fun _ => hm k
  have hlarge : large ≤ m₀ := sup_le ((hDP i).trans (hm i)) hrest
  have hξint : Integrable (ξ i) P := (hξ i).integrable (by norm_num)
  have hzero : P[ξ i | large] =ᵐ[P] (fun _ => 0) :=
    condExp_sup_eq_zero_of_indep (hDP i) (hm i) hrest (ξ i) hξint (hξm i)
      (independent_block_rest hm hind i) (hmean i)
  have hjrest : mPair j ≤ rest :=
    (le_iSup (fun _ : j ≠ i => mPair j) hji).trans
      (le_iSup (fun k => ⨆ (_ : k ≠ i), mPair k) j)
  have hjlarge : StronglyMeasurable[large] (ξ j) :=
    (hξm j).mono (hjrest.trans le_sup_right)
  have hpull := condExp_mul_of_stronglyMeasurable_right hjlarge
    ((hξ i).integrable_mul (hξ j)) hξint
  have hprod : P[(fun ω => ξ i ω * ξ j ω) | large] =ᵐ[P] (fun _ => 0) := by
    filter_upwards [hpull, hzero] with ω hp hz
    simpa only [Pi.mul_def, hz, zero_mul] using hp
  exact condExp_zero_of_condExp_zero_of_le
    (allDesigns_le_ownDesign_sup_rest mD mPair hDP i) hlarge _ hprod

/-- Conditional diagonal covariance, derived from own-design noise moments and
independence of full observation blocks. No all-design moments are assumed. -/
theorem condExp_noise_covariance_allDesigns [IsProbabilityMeasure P]
    {ι : Type*} [DecidableEq ι] (mD mPair : ι → MeasurableSpace Ω)
    (hDP : ∀ j, mD j ≤ mPair j) (hm : ∀ j, mPair j ≤ m₀)
    (hind : iIndep mPair P) (ξ : ι → Ω → ℝ) (σ : ℝ)
    (hξ : ∀ i, MemLp (ξ i) 2 P)
    (hξm : ∀ i, StronglyMeasurable[mPair i] (ξ i))
    (hmean : ∀ i, P[ξ i | mD i] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => ξ i ω ^ 2) | mD i] =ᵐ[P] (fun _ => σ ^ 2))
    (i j : ι) :
    P[(fun ω => ξ i ω * ξ j ω) | ⨆ k, mD k] =ᵐ[P]
      (fun _ => if i = j then σ ^ 2 else 0) := by
  by_cases hij : i = j
  · subst j
    have hsquare : Integrable (fun ω => ξ i ω ^ 2) P := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (hξ i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    have hmeas : StronglyMeasurable[mPair i] (fun ω => ξ i ω ^ 2) := (hξm i).pow 2
    simpa only [ite_true, ← pow_two] using
      condExp_allDesigns_eq_const_of_independent_blocks mD mPair hDP hm hind i
        (fun ω => ξ i ω ^ 2) (σ ^ 2) hsquare hmeas (hsecond i)
  · simpa only [if_neg hij] using
      condExp_cross_allDesigns_eq_zero mD mPair hDP hm hind ξ hξ hξm hmean i j (Ne.symm hij)

/-- Sigma-algebra generated by a full design/response observation pair. -/
abbrev observationPairSigma {X : Type*} [MeasurableSpace X] (Z : Ω → X × ℝ) :
    MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance

/-- Sigma-algebra generated by the design coordinate of an observation pair. -/
abbrev observationDesignSigma {X : Type*} [MeasurableSpace X] (Z : Ω → X × ℝ) :
    MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (Z ω).1) inferInstance

/-- The actual scalar regression residual of an observation pair. -/
def observationNoise {X : Type*} (Z : Ω → X × ℝ) (f : X → ℝ) (ω : Ω) : ℝ :=
  (Z ω).2 - f (Z ω).1

/-- Full independent observation pairs and own-design first/second moments
imply the all-design noise moments used in the conditional risk decomposition.
Identical distribution is unnecessary for this implication. Measurability of f
is stated for its chosen representative; no standard Borel structure on X is
required. -/
theorem observation_pair_conditional_noise_moments [IsProbabilityMeasure P]
    {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (Z : ι → Ω → X × ℝ) (f : X → ℝ) (σ : ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hf : Measurable f)
    (hind : iIndepFun Z P)
    (hε : ∀ i, MemLp (observationNoise (Z i) f) 2 P)
    (hmean : ∀ i, P[observationNoise (Z i) f | observationDesignSigma (Z i)] =ᵐ[P]
      (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => observationNoise (Z i) f ω ^ 2) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => σ ^ 2)) :
    (∀ i, P[observationNoise (Z i) f | ⨆ j, observationDesignSigma (Z j)] =ᵐ[P]
      (fun _ => 0)) ∧
    (∀ i j, P[(fun ω => observationNoise (Z i) f ω * observationNoise (Z j) f ω) |
      ⨆ k, observationDesignSigma (Z k)] =ᵐ[P]
      (fun _ => if i = j then σ ^ 2 else 0)) := by
  have hm : ∀ i, observationPairSigma (Z i) ≤ m₀ := fun i => (hZ i).comap_le
  have hDP : ∀ i, observationDesignSigma (Z i) ≤ observationPairSigma (Z i) := by
    intro i
    have hZi : Measurable[observationPairSigma (Z i)] (Z i) := Measurable.of_comap_le le_rfl
    exact hZi.fst.comap_le
  have hnoise : ∀ i, StronglyMeasurable[observationPairSigma (Z i)]
      (observationNoise (Z i) f) := by
    intro i
    have hZi : Measurable[observationPairSigma (Z i)] (Z i) := Measurable.of_comap_le le_rfl
    exact (hZi.snd.sub (hf.comp hZi.fst)).stronglyMeasurable
  constructor
  · intro i
    exact condExp_allDesigns_eq_zero_of_independent_blocks _ _ hDP hm hind.iIndep i _
      ((hε i).integrable (by norm_num)) (hnoise i) (hmean i)
  · intro i j
    exact condExp_noise_covariance_allDesigns _ _ hDP hm hind.iIndep _ σ hε hnoise
      hmean hsecond i j

/-- A finite strictly positive own-design second conditional moment forces the
actual residual into L². The positivity excludes Lean's default zero value for
conditional expectation of a nonintegrable function. -/
theorem memLp_observationNoise_of_positive_conditional_second_moment
    [IsProbabilityMeasure P] {X : Type*} [MeasurableSpace X]
    (Z : Ω → X × ℝ) (f : X → ℝ) (σ : ℝ)
    (hZ : Measurable Z) (hf : Measurable f) (hσ : 0 < σ)
    (hsecond : P[(fun ω => observationNoise Z f ω ^ 2) | observationDesignSigma Z]
      =ᵐ[P] (fun _ => σ ^ 2)) : MemLp (observationNoise Z f) 2 P := by
  have hm : Measurable (observationNoise Z f) := hZ.snd.sub (hf.comp hZ.fst)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  by_contra hnot
  rw [condExp_of_not_integrable hnot] at hsecond
  obtain ⟨ω, hω⟩ := hsecond.exists
  have hpos : 0 < σ ^ 2 := sq_pos_of_pos hσ
  exact hpos.ne' hω.symm

/-- The source-model wrapper: the strictly positive own-design noise variance
already supplies square integrability, so no separate L²-noise premise remains.
Only independence of full observation pairs and their own-design conditional
moments are used to derive the all-design moments. -/
theorem observation_pair_conditional_noise_moments_of_positive_variance
    [IsProbabilityMeasure P] {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (Z : ι → Ω → X × ℝ) (f : X → ℝ) (σ : ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hf : Measurable f) (hσ : 0 < σ)
    (hind : iIndepFun Z P)
    (hmean : ∀ i, P[observationNoise (Z i) f | observationDesignSigma (Z i)] =ᵐ[P]
      (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => observationNoise (Z i) f ω ^ 2) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => σ ^ 2)) :
    (∀ i, P[observationNoise (Z i) f | ⨆ j, observationDesignSigma (Z j)] =ᵐ[P]
      (fun _ => 0)) ∧
    (∀ i j, P[(fun ω => observationNoise (Z i) f ω * observationNoise (Z j) f ω) |
      ⨆ k, observationDesignSigma (Z k)] =ᵐ[P]
      (fun _ => if i = j then σ ^ 2 else 0)) := by
  apply observation_pair_conditional_noise_moments Z f σ hZ hf hind _ hmean hsecond
  intro i
  exact memLp_observationNoise_of_positive_conditional_second_moment
    (Z i) f σ (hZ i) hf hσ (hsecond i)

end KernelSeq
