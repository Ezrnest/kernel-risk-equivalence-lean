import KernelSeq.EmpiricalSpectral
import KernelSeq.FilterDimension
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Polynomial approximation for the actual compact real spectral calculus

The operator is the constructed eigenbasis multiplier from `CompactCalculus`.
Polynomial agreement and approximation are proved for that operator, without
postulating a real continuous-functional-calculus instance.
-/

open MeasureTheory Filter Topology LinearMap Module.End
open scoped Polynomial

namespace KernelSeq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private def clmToEnd : (H →L[ℝ] H) →ₐ[ℝ] Module.End ℝ H :=
  { ContinuousLinearMap.toLinearMapRingHom with commutes' := fun _ => rfl }

/-- Polynomial evaluation on actual continuous linear maps respects eigenvectors. -/
theorem clm_aeval_eigen (T : H →L[ℝ] H) (p : ℝ[X]) {v : H} {t : ℝ}
    (hv : T v = t • v) : Polynomial.aeval T p v = p.eval t • v := by
  change clmToEnd (Polynomial.aeval T p) v = p.eval t • v
  rw [← Polynomial.aeval_algHom_apply]
  exact Module.End.aeval_apply_of_mem_apply_eq_smul hv

/-- A diagonal multiplier acts by its displayed weight on each basis vector. -/
theorem hilbertDiagonal_eigen {ι : Type*} (b : HilbertBasis ι ℝ H)
    (w : ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hw : ∀ i, ‖w i‖ ≤ K) (j : ι) :
    hilbertDiagonal b w K hK hw (b j) = w j • b j := by
  apply b.repr.injective
  ext i
  simp only [hilbertDiagonal_repr, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · rw [hij]
  · rw [b.repr_apply_apply, b.orthonormal.inner_eq_zero hij]
    simp only [mul_zero]

variable [CompleteSpace H]

/-- The actual spectral multiplier of a polynomial is `Polynomial.aeval T p`. -/
theorem compactSpectralMultiplier_polynomial_eq (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (p : ℝ[X]) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |p.eval t| ≤ K) :
    compactSpectralMultiplier T hc hp p.eval K hK hb = Polynomial.aeval T p := by
  apply continuousLinearMap_eq_of_hilbertBasis (compactEigenbasis T hc hp.isSymmetric)
  intro i
  rw [compactSpectralMultiplier_eigen T hc hp p.eval K hK hb
    (compactEigenbasis_eigen T hc hp.isSymmetric i)]
  exact (clm_aeval_eigen T p (compactEigenbasis_eigen T hc hp.isSymmetric i)).symm

/-- Uniform scalar approximation gives operator-norm approximation of the
actual compact multiplier, with exactly the same error constant. -/
theorem compactSpectralMultiplier_polynomial_error_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) (p : ℝ[X])
    {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |p.eval t - φ t| ≤ ε) :
    ‖Polynomial.aeval T p - compactSpectralMultiplier T hc hp φ K hK hb‖ ≤ ε := by
  let b := compactEigenbasis T hc hp.isSymmetric
  let w : CompactSpectralIndex T → ℝ := fun i => p.eval i.1 - φ i.1
  have hw : ∀ i, ‖w i‖ ≤ ε := by
    intro i
    apply he
    exact ⟨compactEigenvalue_nonneg T hc hp i,
      (le_abs_self i.1).trans (compactEigenvalue_norm_le T hc hp.isSymmetric i)⟩
  have hd : Polynomial.aeval T p - compactSpectralMultiplier T hc hp φ K hK hb =
      hilbertDiagonal b w ε hε hw := by
    apply continuousLinearMap_eq_of_hilbertBasis b
    intro i
    rw [_root_.sub_apply, clm_aeval_eigen T p (compactEigenbasis_eigen T hc hp.isSymmetric i),
      compactSpectralMultiplier_eigen T hc hp φ K hK hb
        (compactEigenbasis_eigen T hc hp.isSymmetric i), hilbertDiagonal_eigen]
    exact (sub_smul _ _ _).symm
  rw [hd]
  exact hilbertDiagonal_norm_le b w ε hε hw

/-- A continuous spectral profile of a strongly measurable compact positive
operator family is strongly measurable in operator norm. -/
theorem stronglyMeasurable_compactSpectralMultiplier
    {Ω : Type*} [MeasurableSpace Ω] (T : Ω → H →L[ℝ] H)
    (hT : StronglyMeasurable T) (hc : ∀ ω, IsCompactOperator (T ω))
    (hp : ∀ ω, (T ω).IsPositive) (M : ℝ) (hM : ∀ ω, ‖T ω‖ ≤ M)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc (0 : ℝ) M))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t ∈ Set.Icc (0 : ℝ) M, |φ t| ≤ K) :
    StronglyMeasurable (fun ω => compactSpectralMultiplier (T ω) (hc ω) (hp ω) φ K hK
      (fun t ht => hb t ⟨ht.1, ht.2.trans (hM ω)⟩)) := by
  choose p he using fun n : ℕ => exists_polynomial_near_of_continuousOn 0 M φ hφ
    (1 / ((n : ℝ) + 1)) (by positivity)
  apply stronglyMeasurable_of_tendsto atTop
    (fun n => (p n).continuous_aeval.comp_stronglyMeasurable hT)
  apply tendsto_pi_nhds.mpr
  intro ω
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    exact norm_nonneg _
  · intro n
    apply compactSpectralMultiplier_polynomial_error_le _ _ _ _ _ _ _ _ (by positivity)
    intro t ht
    exact (he n t ⟨ht.1, ht.2.trans (hM ω)⟩).le

namespace ResidualFilter

/-- The original residual-only contract makes shrinkage continuous on the
closed spectral interval, without imposing continuity of the inverse profile. -/
theorem Contract.shrinkage_continuousOn {lam M ρ A : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) :
    ContinuousOn (shrinkage φ) (Set.Icc (0 : ℝ) M) := by
  have hlip : LipschitzOnWith (Real.toNNReal (A * (1 + ρ)))
      (fun u => shrinkage φ (spectralCoordinate lam u)) (logDomain lam M) := by
    apply LipschitzOnWith.of_dist_le'
    intro u hu v hv
    simpa only [Real.dist_eq] using h.shrinkage_lipschitz hlam hu hv
  have hlog : ContinuousOn (fun t : ℝ => Real.log (1 + t / lam)) (Set.Icc (0 : ℝ) M) := by
    apply (continuousOn_const.add (continuousOn_id.div_const lam)).log
    intro t ht
    exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg ht.1 hlam.le))
  have hcomp := hlip.continuousOn.comp hlog (fun t ht => log_coordinate_mem hlam ht)
  apply hcomp.congr
  intro t ht
  simp only [Function.comp_apply, spectralCoordinate_log hlam ht.1]

end ResidualFilter

@[simp]
theorem compactShrinkageOperator_repr (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {M : ℝ} (hM : ‖T‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ)
    (v : H) (i : CompactSpectralIndex T) :
    (compactEigenbasis T hc hp.isSymmetric).repr
      (compactShrinkageOperator T hc hp φ hM hf v) i =
        ResidualFilter.shrinkage φ i.1 * (compactEigenbasis T hc hp.isSymmetric).repr v i :=
  compactSpectralMultiplier_repr _ _ _ _ _ _ _ _ _

/-- Shrinkage is strongly measurable for the original residual-only contract;
continuity of the inverse profile is not a premise. -/
theorem stronglyMeasurable_compactShrinkageOperator
    {Ω : Type*} [MeasurableSpace Ω] (T : Ω → H →L[ℝ] H)
    (hT : StronglyMeasurable T) (hc : ∀ ω, IsCompactOperator (T ω))
    (hp : ∀ ω, (T ω).IsPositive) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ∀ ω, ‖T ω‖ ≤ M) (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    StronglyMeasurable (fun ω => compactShrinkageOperator (T ω) (hc ω) (hp ω) φ (hM ω) hf) := by
  apply stronglyMeasurable_compactSpectralMultiplier T hT hc hp M hM (ResidualFilter.shrinkage φ)
    (h.shrinkage_continuousOn hlam) 1 zero_le_one
  intro t ht
  rw [abs_of_nonneg (hf.shrinkage_mem t ht).1]
  exact (hf.shrinkage_mem t ht).2

/-- Inversion preserves strong measurability on an actually unit-valued operator
family, even when the entire operator space is nonseparable. -/
theorem stronglyMeasurable_ringInverse_of_isUnit
    {Ω : Type*} [MeasurableSpace Ω] (T : Ω → H →L[ℝ] H)
    (hT : StronglyMeasurable T) (hu : ∀ ω, IsUnit (T ω)) :
    StronglyMeasurable (fun ω => Ring.inverse (T ω)) := by
  letI : MeasurableSpace (H →L[ℝ] H) := borel _
  letI : BorelSpace (H →L[ℝ] H) := ⟨rfl⟩
  letI : SecondCountableTopology (Set.range T) := hT.isSeparable_range.secondCountableTopology
  have hg : StronglyMeasurable (Set.rangeFactorization T) :=
    hT.measurable.subtype_mk.stronglyMeasurable
  have hc : Continuous (fun a : Set.range T => Ring.inverse (a : H →L[ℝ] H)) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    have hua : IsUnit (a : H →L[ℝ] H) := by
      obtain ⟨ω, hω⟩ := a.property
      exact hω ▸ hu ω
    obtain ⟨u, huval⟩ := hua
    have hi : ContinuousAt Ring.inverse (a : H →L[ℝ] H) :=
      huval ▸ NormedRing.inverse_continuousAt u
    exact hi.comp continuous_subtype_val.continuousAt
  exact hc.comp_stronglyMeasurable hg

/-- In particular every positively regularized covariance has a strongly
measurable actual operator-ring inverse. -/
theorem stronglyMeasurable_regularizedInverse
    {Ω : Type*} [MeasurableSpace Ω] (T : Ω → H →L[ℝ] H)
    (hT : StronglyMeasurable T) (hp : ∀ ω, (T ω).IsPositive) (ε : ℝ) (hε : 0 < ε) :
    StronglyMeasurable (fun ω => Ring.inverse (T ω + ε • (1 : H →L[ℝ] H))) := by
  apply stronglyMeasurable_ringInverse_of_isUnit _ (hT.add stronglyMeasurable_const)
  intro ω
  exact regularized_isUnit_real (T ω) ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (hp ω)) ε hε

omit [CompleteSpace H] in
/-- Random bounded operators can be applied to random vectors without a
separability assumption on the entire operator space. -/
theorem stronglyMeasurable_operator_apply
    {Ω : Type*} [MeasurableSpace Ω] (T : Ω → H →L[ℝ] H)
    (hT : StronglyMeasurable T) (v : Ω → H) (hv : StronglyMeasurable v) :
    StronglyMeasurable (fun ω => T ω (v ω)) :=
  (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hT.prodMk hv)

/-- The actual regularized operator-ring inverse has the expected spectral
coordinate action. This is derived from cancellation, not postulated. -/
theorem compact_regularizedInverse_repr (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (ε : ℝ) (hε : 0 < ε)
    (v : H) (i : CompactSpectralIndex T) :
    (compactEigenbasis T hc hp.isSymmetric).repr
      (Ring.inverse (T + ε • (1 : H →L[ℝ] H)) v) i =
        (i.1 + ε)⁻¹ * (compactEigenbasis T hc hp.isSymmetric).repr v i := by
  have hu := regularized_isUnit_real T ((ContinuousLinearMap.nonneg_iff_isPositive T).mpr hp) ε hε
  have hy : (T + ε • (1 : H →L[ℝ] H)) (Ring.inverse (T + ε • (1 : H →L[ℝ] H)) v) = v :=
    congrArg (fun F : H →L[ℝ] H => F v) (Ring.mul_inverse_cancel _ hu)
  have he : (i.1 + ε) * (compactEigenbasis T hc hp.isSymmetric).repr
      (Ring.inverse (T + ε • (1 : H →L[ℝ] H)) v) i =
        (compactEigenbasis T hc hp.isSymmetric).repr v i := by
    have he' := congrArg (fun z : H => (compactEigenbasis T hc hp.isSymmetric).repr z i) hy
    simpa only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self, map_add, map_smul,
      lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      compactEigenbasis_repr_apply, add_mul] using he'
  have hn : i.1 + ε ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos
    (compactEigenvalue_nonneg T hc hp i) hε)
  calc
    _ = (i.1 + ε)⁻¹ * ((i.1 + ε) * (compactEigenbasis T hc hp.isSymmetric).repr
        (Ring.inverse (T + ε • (1 : H →L[ℝ] H)) v) i) := by
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = _ := by rw [he]

@[simp]
theorem compactFilterOperator_repr (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) (v : H) (i : CompactSpectralIndex T) :
    (compactEigenbasis T hc hp.isSymmetric).repr (compactFilterOperator T hc hp φ hlam hM h v) i =
      φ i.1 * (compactEigenbasis T hc hp.isSymmetric).repr v i :=
  compactSpectralMultiplier_repr _ _ _ _ _ _ _ _ _

end KernelSeq
