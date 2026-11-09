import KernelSeq.MatrixBernsteinExp
import KernelSeq.FiniteOperatorTrace
import KernelSeq.TopEigenCompression
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The actual trace Laplace potential of a selfadjoint finite operator

The trace of exp(θY)+exp(-θY)-2I vanishes at the zero operator and detects
the operator-norm tail. This potential is the deterministic bridge needed for
intrinsic-dimension concentration; it does not assume a matrix-sum tail bound.
-/

open MeasureTheory Filter LinearMap Module.End
open scoped BigOperators

namespace KernelSeq
noncomputable section

theorem exp_symmetric_remainder_nonneg (z : ℝ) :
    0 ≤ Real.exp z + Real.exp (-z) - 2 := by
  have h := Real.one_le_cosh z
  rw [Real.cosh_eq] at h
  linarith

theorem exp_symmetric_remainder_mono {θ t y : ℝ}
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (hty : t ≤ |y|) :
    Real.exp (θ * t) + Real.exp (-(θ * t)) - 2 ≤
      Real.exp (θ * y) + Real.exp (-(θ * y)) - 2 := by
  have hh : |θ * t| ≤ |θ * y| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hθ, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left hty hθ
  have h := Real.cosh_le_cosh.mpr hh
  rw [Real.cosh_eq, Real.cosh_eq] at h
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An actual basis eigenvalue has absolute value equal to the true operator
norm. This handles both signs of a compact symmetric operator. -/
theorem exists_compactEigenvalue_abs_eq_norm (Y : H →L[ℝ] H)
    (hc : IsCompactOperator Y) (hY : Y.IsSymmetric) (hn : 0 < ‖Y‖) :
    ∃ j : CompactSpectralIndex Y, |j.1| = ‖Y‖ := by
  have hne : Y ≠ 0 := by simpa only [norm_pos_iff] using hn
  have hex : ∃ μ : ℝ, HasEigenvalue (Y : Module.End ℝ H) μ ∧ μ ≠ 0 := by
    by_contra! h
    exact hne ((Y.eq_zero_of_forall_hasEigenvalue_eq_zero hc hY).mp h)
  obtain ⟨μ, hμ, hμ0⟩ := hex
  have hspec : (spectrum ℝ Y).Nonempty := ⟨μ, (hc.hasEigenvalue_iff_mem_spectrum hμ0).mp hμ⟩
  have hr := Real.spectralRadius_mem_spectrum_or hspec
  rw [Y.spectralRadius_eq_nnnorm hY.isSelfAdjoint, ENNReal.coe_toReal] at hr
  have hev : ∃ r : ℝ, HasEigenvalue (Y : Module.End ℝ H) r ∧ |r| = ‖Y‖ := by
    rcases hr with hp | hm
    · exact ⟨‖Y‖, (hc.hasEigenvalue_iff_mem_spectrum hn.ne').mpr hp, abs_of_pos hn⟩
    · exact ⟨-‖Y‖, (hc.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hn.ne')).mpr hm,
        by rw [abs_neg, abs_of_pos hn]⟩
  obtain ⟨r, hrv, hrabs⟩ := hev
  let b := compactEigenbasis Y hc hY
  obtain ⟨x, hx, hx0⟩ := hrv.exists_hasEigenvector
  have hYx : Y x = r • x := mem_eigenspace_iff.mp
    (show x ∈ eigenspace (Y : Module.End ℝ H) r by simpa only [mem_genEigenspace_one] using hx)
  have hcoord : ∃ j, b.repr x j ≠ 0 := by
    by_contra! hz
    apply hx0
    apply b.repr.injective
    ext j
    simpa using hz j
  obtain ⟨j, hj⟩ := hcoord
  refine ⟨j, ?_⟩
  have he := congrArg (fun y => b.repr y j) hYx
  change b.repr (Y x) j = b.repr (r • x) j at he
  rw [compactEigenbasis_repr_apply, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at he
  exact (congrArg abs (mul_right_cancel₀ hj he)).trans hrabs

variable {ι : Type*} [Fintype ι]

def matrixLaplacePotential (b : HilbertBasis ι ℝ H) (θ : ℝ) (Y : H →L[ℝ] H) : ℝ :=
  basisTrace b (NormedSpace.exp (θ • Y) + NormedSpace.exp ((-θ) • Y) - (2 : ℝ) • 1)

theorem matrixLaplacePotential_eq_eigen_sum (b : HilbertBasis ι ℝ H) (Y : H →L[ℝ] H)
    (hc : IsCompactOperator Y) (hY : Y.IsSymmetric) (θ : ℝ) :
    matrixLaplacePotential b θ Y =
      ∑' j : CompactSpectralIndex Y, (Real.exp (θ * j.1) + Real.exp (-(θ * j.1)) - 2) := by
  letI : FiniteDimensional ℝ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  let e := compactEigenbasis Y hc hY
  letI : Finite (CompactSpectralIndex Y) := e.orthonormal.linearIndependent.finite
  letI : Fintype (CompactSpectralIndex Y) := Fintype.ofFinite _
  rw [matrixLaplacePotential, finiteBasisTrace_basis_independent b e]
  apply tsum_congr
  intro j
  have hplus : NormedSpace.exp (θ • Y) (e j) = Real.exp (θ * j.1) • e j :=
    compact_operator_exp_eigen Y hc hY θ j
  have hminus : NormedSpace.exp ((-θ) • Y) (e j) = Real.exp ((-θ) * j.1) • e j :=
    compact_operator_exp_eigen Y hc hY (-θ) j
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply,
    one_apply_eq_self, inner_sub_right, inner_add_right, hplus, hminus, inner_smul_right,
    real_inner_self_eq_norm_sq,
    e.orthonormal.norm_eq_one, one_pow, mul_one, neg_mul]

theorem matrixLaplacePotential_nonneg (b : HilbertBasis ι ℝ H) (Y : H →L[ℝ] H)
    (hc : IsCompactOperator Y) (hY : Y.IsSymmetric) (θ : ℝ) :
    0 ≤ matrixLaplacePotential b θ Y := by
  rw [matrixLaplacePotential_eq_eigen_sum b Y hc hY θ]
  exact tsum_nonneg (fun j => exp_symmetric_remainder_nonneg (θ * j.1))

/-- The actual norm-tail event forces a large trace potential, without a
dimension factor or an assumed norm/spectral correspondence. -/
theorem matrixLaplacePotential_of_norm_ge (b : HilbertBasis ι ℝ H) (Y : H →L[ℝ] H)
    (hc : IsCompactOperator Y) (hY : Y.IsSymmetric) {θ t : ℝ}
    (hθ : 0 ≤ θ) (ht : 0 < t) (htY : t ≤ ‖Y‖) :
    Real.exp (θ * t) + Real.exp (-(θ * t)) - 2 ≤ matrixLaplacePotential b θ Y := by
  letI : FiniteDimensional ℝ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  let e := compactEigenbasis Y hc hY
  letI : Finite (CompactSpectralIndex Y) := e.orthonormal.linearIndependent.finite
  letI : Fintype (CompactSpectralIndex Y) := Fintype.ofFinite _
  obtain ⟨j, hj⟩ := exists_compactEigenvalue_abs_eq_norm Y hc hY (ht.trans_le htY)
  rw [matrixLaplacePotential_eq_eigen_sum b Y hc hY θ, tsum_fintype]
  exact (exp_symmetric_remainder_mono hθ ht.le (htY.trans_eq hj.symm)).trans
    (Finset.single_le_sum (fun k _ => exp_symmetric_remainder_nonneg (θ * k.1)) (Finset.mem_univ j))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace H] in
/-- The scalar potential is integrable when the two actual operator
exponentials have genuine Bochner integrals. -/
theorem integrable_matrixLaplacePotential (b : HilbertBasis ι ℝ H) (Y : Ω → H →L[ℝ] H)
    (θ : ℝ) (hplus : Integrable (fun ω => NormedSpace.exp (θ • Y ω)) P)
    (hminus : Integrable (fun ω => NormedSpace.exp ((-θ) • Y ω)) P) :
    Integrable (fun ω => matrixLaplacePotential b θ (Y ω)) P := by
  exact integrable_finiteBasisTrace b _ ((hplus.add hminus).sub (integrable_const _))

/-- The deterministic spectral bridge and scalar Markov inequality bound the
actual matrix-norm tail by the integral of its actual trace potential. -/
theorem matrixLaplace_norm_tail (b : HilbertBasis ι ℝ H) (Y : Ω → H →L[ℝ] H)
    (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω)) {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t)
    (hplus : Integrable (fun ω => NormedSpace.exp (θ • Y ω)) P)
    (hminus : Integrable (fun ω => NormedSpace.exp ((-θ) • Y ω)) P) :
    P {ω | t ≤ ‖Y ω‖} ≤ ENNReal.ofReal
      ((∫ ω, matrixLaplacePotential b θ (Y ω) ∂P) /
        (Real.exp (θ * t) + Real.exp (-(θ * t)) - 2)) := by
  letI : FiniteDimensional ℝ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  let C := Real.exp (θ * t) + Real.exp (-(θ * t)) - 2
  have hC : 0 < C := by
    have hh := Real.one_lt_cosh.mpr (mul_ne_zero hθ.ne' ht.ne')
    rw [Real.cosh_eq] at hh
    dsimp only [C]
    linarith
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ matrixLaplacePotential b θ (Y ω) := by
    filter_upwards [hY] with ω hω
    exact matrixLaplacePotential_nonneg b (Y ω)
      (isCompactOperator_of_locallyCompactSpace_dom _) hω.isSymmetric θ
  have hi := integrable_matrixLaplacePotential b Y θ hplus hminus
  have hinc : P {ω | t ≤ ‖Y ω‖} ≤ P {ω | C ≤ matrixLaplacePotential b θ (Y ω)} := by
    apply measure_mono_ae
    filter_upwards [hY] with ω hω hnorm
    exact matrixLaplacePotential_of_norm_ge b (Y ω)
      (isCompactOperator_of_locallyCompactSpace_dom _) hω.isSymmetric hθ.le ht hnorm
  have hincR : P.real {ω | t ≤ ‖Y ω‖} ≤ P.real {ω | C ≤ matrixLaplacePotential b θ (Y ω)} :=
    ENNReal.toReal_mono (measure_ne_top _ _) hinc
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hi C
  have hreal : P.real {ω | t ≤ ‖Y ω‖} ≤ (∫ ω, matrixLaplacePotential b θ (Y ω) ∂P) / C := by
    apply (le_div_iff₀ hC).mpr
    calc
      _ = C * P.real {ω | t ≤ ‖Y ω‖} := mul_comm _ _
      _ ≤ C * P.real {ω | C ≤ matrixLaplacePotential b θ (Y ω)} :=
        mul_le_mul_of_nonneg_left hincR hC.le
      _ ≤ _ := hmark
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (div_nonneg (integral_nonneg_of_ae hnonneg) hC.le)]
  exact hreal

end
end KernelSeq
