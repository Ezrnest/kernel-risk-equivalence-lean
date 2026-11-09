import KernelSeq.WalshRieszWalk
import KernelSeq.WalshStoppedEnergy
import KernelSeq.FiniteFieldMarcinkiewicz
import KernelSeq.LipschitzFourierLpTransference
import KernelSeq.FinitePolynomialLpContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Actual Walsh-prefix representation and matching-exponent Riesz bounds

This modular layer keeps the finite Walsh martingale transform estimate
explicit on actual prefix differences, with matching outer and Schatten
exponents. `finiteWalshLpTransformBound_proved` in `WalshZeroStart` supplies
its actual constructor. The initial prefix mean is omitted explicitly.
No Fourier estimate, prefix identification, or torus norm certificate is an
input to that estimate.
-/

open Set Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate

namespace KernelSeq
noncomputable section

/-- Actual deterministic transform of all prefix differences. The initial
mean is omitted, also when the cube has zero coordinates. -/
def walshCenteredTransform {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (σ : Fin n → ℝ) (F : WalshCube n → E) (ω : WalshCube n) : E :=
  ∑ j : Fin n, σ j • (walshPrefixAverage (j.val + 1) F ω - walshPrefixAverage j.val F ω)

universe uι uH

/-- The explicit modular martingale interface, with actual constructor
`finiteWalshLpTransformBound_proved` in `WalshZeroStart`. It has no Fourier
conclusion. Every transform is the actual prefix-difference sum above,
without its mean. -/
structure FiniteWalshLpTransformBound (C : ℝ) : Prop where
  constant_nonneg : 0 ≤ C
  bound : ∀ {ι : Type uι} [Fintype ι] {H : Type uH}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (n m : ℕ) (σ : Fin n → ℝ)
    (_hσ : ∀ j, |σ j| = 1) (F : WalshCube n → H →L[ℝ] H),
    finiteFieldSchattenMoment b (walshCenteredTransform σ F) (dyadicSchattenExponent m) ≤
      (C * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        finiteFieldSchattenMoment b F (dyadicSchattenExponent m)

section PrefixProduct

variable {n : ℕ}

/-- Actual normalized complex average on the existing finite Walsh cube. -/
def walshComplexMean (f : WalshCube n → ℂ) : ℂ :=
  (Fintype.card (WalshCube n) : ℂ)⁻¹ * ∑ ω, f ω

theorem walshComplexMean_add (f g : WalshCube n → ℂ) :
    walshComplexMean (fun ω => f ω + g ω) = walshComplexMean f + walshComplexMean g := by
  simp only [walshComplexMean, Finset.sum_add_distrib, mul_add]

theorem walshComplexMean_sub (f g : WalshCube n → ℂ) :
    walshComplexMean (fun ω => f ω - g ω) = walshComplexMean f - walshComplexMean g := by
  simp only [walshComplexMean, Finset.sum_sub_distrib, mul_sub]

theorem walshComplexMean_const_mul (z : ℂ) (f : WalshCube n → ℂ) :
    walshComplexMean (fun ω => z * f ω) = z * walshComplexMean f := by
  simp only [walshComplexMean, ← Finset.mul_sum]
  ring

theorem walshComplexMean_fun_sum {J : Type*} [Fintype J] (f : J → WalshCube n → ℂ) :
    walshComplexMean (fun ω => ∑ j, f j ω) = ∑ j, walshComplexMean (f j) := by
  unfold walshComplexMean
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Actual independence of all Boolean coordinates, proved by finite
product-of-sums expansion and the true cube cardinality. -/
theorem walshComplexMean_product (f : Fin n → Bool → ℂ) :
    walshComplexMean (fun ω => ∏ j : Fin n, f j (ω j)) = ∏ j : Fin n, walkBoolAverage (f j) := by
  classical
  have hc : (Fintype.card (WalshCube n) : ℂ) = (2 : ℂ) ^ n := by
    simp [WalshCube]
  unfold walshComplexMean
  rw [hc, ← Fintype.prod_sum]
  simp only [walkBoolAverage, ← Fintype.sum_bool, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [div_eq_mul_inv, mul_comm]

def walshPhaseProduct (α : Fin n → ℝ) (ω : WalshCube n) : ℂ :=
  ∏ j : Fin n, walkSignedPhase (α j) (ω j)

/-- Explicit actual conditional phase product at every prefix level. -/
def walshPhasePrefix (α : Fin n → ℝ) (l : ℕ) (ω : WalshCube n) : ℂ :=
  ∏ j : Fin n, if (j : ℕ) < l then walkSignedPhase (α j) (ω j) else (Real.cos (α j) : ℂ)

/-- Every intermediate prefix is identified from actual finite averaging;
this includes zero, terminal, and over-terminal prefix levels. -/
theorem walshPrefixAverage_phase_product (α : Fin n → ℝ) (l : ℕ) (ω : WalshCube n) :
    walshPrefixAverage l (walshPhaseProduct α) ω = walshPhasePrefix α l ω := by
  classical
  change (Fintype.card (WalshCube n) : ℝ)⁻¹ •
      (∑ η : WalshCube n, ∏ j : Fin n, walkSignedPhase (α j) (walshMerge l ω η j)) = _
  have hmean : (Fintype.card (WalshCube n) : ℝ)⁻¹ •
      (∑ η : WalshCube n, ∏ j : Fin n, walkSignedPhase (α j) (walshMerge l ω η j)) =
      walshComplexMean (fun η => ∏ j : Fin n,
        if (j : ℕ) < l then walkSignedPhase (α j) (ω j) else walkSignedPhase (α j) (η j)) := by
    simp only [walshComplexMean, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
      walshMerge]
    congr 2
    funext η
    apply Finset.prod_congr rfl
    intro j _
    split_ifs <;> rfl
  rw [hmean, walshComplexMean_product (fun j e =>
    if (j : ℕ) < l then walkSignedPhase (α j) (ω j) else walkSignedPhase (α j) e)]
  unfold walshPhasePrefix
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : (j : ℕ) < l
  · simp only [if_pos hj, walkBoolAverage_const]
  · simp only [if_neg hj, walkBoolAverage_phase]

/-- Actual remaining squared Markov eigenvalue at a prefix. -/
def walshPhaseEnergy (α : Fin n → ℝ) (l : ℕ) : ℝ :=
  ∏ j : Fin n, if (j : ℕ) < l then 1 else Real.cos (α j) ^ 2

/-- Actual endpoint pullback of every conditional prefix. -/
theorem walshComplexMean_endpoint_prefix (α : Fin n → ℝ) (l : ℕ) :
    walshComplexMean (fun ω => conj (walshPhaseProduct α ω) *
      walshPrefixAverage l (walshPhaseProduct α) ω) = (walshPhaseEnergy α l : ℂ) := by
  classical
  simp only [walshPrefixAverage_phase_product, walshPhaseProduct, walshPhasePrefix,
    map_prod, ← Finset.prod_mul_distrib]
  rw [walshComplexMean_product (fun j e => conj (walkSignedPhase (α j) e) *
    if (j : ℕ) < l then walkSignedPhase (α j) e else (Real.cos (α j) : ℂ))]
  simp only [walshPhaseEnergy, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : (j : ℕ) < l
  · simp only [if_pos hj, walkSignedPhase_conj_mul, walkBoolAverage_const, Complex.ofReal_one]
  · simp only [if_neg hj, walkBoolAverage_mul_const, walkBoolAverage_conj_phase, Complex.ofReal_pow]
    ring

/-- The explicit symbol induced by the actual deterministic prefix transform. -/
def walshFiniteRieszSymbol (α : Fin n → ℝ) (σ : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, σ j * (walshPhaseEnergy α (j.val + 1) - walshPhaseEnergy α j.val)

/-- No prefix or Fourier identification premise: the actual transformed
terminal mode, pulled back by its endpoint, has this genuine finite symbol. -/
theorem walshComplexMean_endpoint_transform (α : Fin n → ℝ) (σ : Fin n → ℝ) :
    walshComplexMean (fun ω => conj (walshPhaseProduct α ω) *
      walshCenteredTransform σ (walshPhaseProduct α) ω) = (walshFiniteRieszSymbol α σ : ℂ) := by
  classical
  simp only [walshCenteredTransform, Finset.mul_sum]
  rw [walshComplexMean_fun_sum]
  simp only [walshFiniteRieszSymbol, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub]
  apply Finset.sum_congr rfl
  intro j _
  have heq : (fun ω => conj (walshPhaseProduct α ω) *
      (σ j • (walshPrefixAverage (j.val + 1) (walshPhaseProduct α) ω -
        walshPrefixAverage j.val (walshPhaseProduct α) ω))) =
      (fun ω => (σ j : ℂ) *
        (conj (walshPhaseProduct α ω) * walshPrefixAverage (j.val + 1) (walshPhaseProduct α) ω -
          conj (walshPhaseProduct α ω) * walshPrefixAverage j.val (walshPhaseProduct α) ω)) := by
    funext ω
    simp only [Complex.real_smul]
    ring
  rw [heq, walshComplexMean_const_mul, walshComplexMean_sub,
    walshComplexMean_endpoint_prefix, walshComplexMean_endpoint_prefix]

end PrefixProduct

section ActualJensen

variable {Ω ι H : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Jensen's inequality for a true normalized finite average of actual
operators in the original finite Hilbert basis. -/
theorem finiteSchatten_mean_rpow_le (b : HilbertBasis ι ℝ H) (F : Ω → H →L[ℝ] H)
    {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteOperatorColumns b
      ((Fintype.card Ω : ℝ)⁻¹ • ∑ ω, F ω)) p ^ p ≤
      (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, hsSchattenNorm b (finiteOperatorColumns b (F ω)) p ^ p := by
  classical
  let w : ℝ := (Fintype.card Ω : ℝ)⁻¹
  have hw : 0 ≤ w := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (∑ ω : Ω, w) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc
  have heq : finiteOperatorColumns b (w • ∑ ω, F ω) =
      ∑ ω, w • finiteOperatorColumns b (F ω) := by
    ext j
    simp only [finiteOperatorColumns_apply, _root_.smul_apply, _root_.sum_apply,
      lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, Finset.smul_sum]
  have hJ := (hsSchattenNorm_convex b hp).map_sum_le
    (t := Finset.univ) (w := fun _ : Ω => w) (p := fun ω => finiteOperatorColumns b (F ω))
    (fun _ _ => hw) hsum (fun _ _ => mem_univ _)
  have hpow := Real.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ)
    (fun _ : Ω => w) (fun ω => hsSchattenNorm b (finiteOperatorColumns b (F ω)) p)
    (fun _ _ => hw) hsum (fun _ _ => hsSchattenNorm_nonneg b _ p) (by linarith : 1 ≤ p)
  change hsSchattenNorm b (finiteOperatorColumns b (w • ∑ ω, F ω)) p ^ p ≤ _
  rw [heq]
  exact (Real.rpow_le_rpow (hsSchattenNorm_nonneg b _ p) hJ (by linarith : 0 ≤ p)).trans
    (hpow.trans_eq (by rw [← Finset.mul_sum]))

theorem walshPrefixAverage_schatten_rpow_le {n : ℕ} (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (l : ℕ) (ω : WalshCube n) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteOperatorColumns b (walshPrefixAverage l F ω)) p ^ p ≤
      walshPrefixAverage l (fun η => hsSchattenNorm b (finiteOperatorColumns b (F η)) p ^ p) ω := by
  simpa only [walshPrefixAverage, smul_eq_mul] using
    finiteSchatten_mean_rpow_le b (fun η => F (walshMerge l ω η)) hp

/-- Actual matching-Lp contraction of every prefix conditional average. -/
theorem finiteFieldSchattenMoment_walshPrefixAverage_le {n : ℕ} (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (l : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    finiteFieldSchattenMoment b (walshPrefixAverage l F) p ≤ finiteFieldSchattenMoment b F p := by
  unfold finiteFieldSchattenMoment
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ ω : WalshCube n,
        walshPrefixAverage l (fun η => hsSchattenNorm b (finiteOperatorColumns b (F η)) p ^ p) ω :=
      Finset.sum_le_sum (fun ω _ => walshPrefixAverage_schatten_rpow_le b F l ω hp)
    _ = _ := sum_walshPrefixAverage l _

end ActualJensen

section TorusTranslation

theorem integrable_fourierSquare_of_continuous {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Integrable f fourierSquareMeasure := by
  rw [fourierSquareMeasure, Measure.prod_restrict]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem fourierSquare_integral_iterated {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    (∫ θ, f θ ∂fourierSquareMeasure) =
      ∫ x in Icc (0 : ℝ) 1, ∫ y in Icc (0 : ℝ) 1, f (x, y) := by
  exact integral_prod f (integrable_fourierSquare_of_continuous hf)

/-- Actual translation invariance of a unit-period set integral. -/
theorem integral_Icc_translate_of_periodic {f : ℝ → ℝ} (hf : Function.Periodic f 1) (s : ℝ) :
    (∫ x in Icc (0 : ℝ) 1, f (x + s)) = ∫ x in Icc (0 : ℝ) 1, f x := by
  calc
    _ = ∫ x in (0 : ℝ)..1, f (x + s) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Icc_eq_integral_Ioc]
    _ = ∫ x in s..s + 1, f x := by
      rw [intervalIntegral.integral_comp_add_right]
      congr 1 <;> ring
    _ = ∫ x in (0 : ℝ)..1, f x := by
      simpa only [zero_add] using hf.intervalIntegral_add_eq s 0
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Icc_eq_integral_Ioc]

/-- True normalized torus stationarity, proved on the actual parameter square
by Fubini and the two periodic interval identities. -/
theorem fourierSquare_integral_translate {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hx : ∀ y, Function.Periodic (fun x => f (x, y)) 1)
    (hy : ∀ x, Function.Periodic (fun y => f (x, y)) 1) (s : ℝ × ℝ) :
    (∫ θ, f (θ + s) ∂fourierSquareMeasure) = ∫ θ, f θ ∂fourierSquareMeasure := by
  have hshift : Continuous (fun θ : ℝ × ℝ => f (θ + s)) :=
    hf.comp (continuous_id.add continuous_const)
  rw [fourierSquare_integral_iterated hshift,
    fourierSquare_integral_iterated hf]
  change (∫ x in Icc (0 : ℝ) 1, ∫ y in Icc (0 : ℝ) 1, f (x + s.1, y + s.2)) = _
  have hrow (x : ℝ) : (∫ y in Icc (0 : ℝ) 1, f (x + s.1, y + s.2)) =
      ∫ y in Icc (0 : ℝ) 1, f (x + s.1, y) := integral_Icc_translate_of_periodic (hy _) _
  have hg : Function.Periodic (fun x => ∫ y in Icc (0 : ℝ) 1, f (x, y)) 1 := by
    intro x
    apply integral_congr_ae
    exact Eventually.of_forall fun y => hx y x
  calc
    _ = ∫ x in Icc (0 : ℝ) 1, ∫ y in Icc (0 : ℝ) 1, f (x + s.1, y) := by
      apply integral_congr_ae
      exact Eventually.of_forall hrow
    _ = _ := integral_Icc_translate_of_periodic hg s.1

end TorusTranslation

section FiniteContinuity

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private def walshLpColumnsLinear (b : HilbertBasis ι ℝ H) :
    (H →L[ℝ] H) →ₗ[ℝ] HilbertSchmidtColumns ι H where
  toFun := finiteOperatorColumns b
  map_add' := finiteOperatorColumns_add b
  map_smul' r A := by
    ext j
    simp only [finiteOperatorColumns_apply, _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply,
      RingHom.id_apply]

omit [CompleteSpace H] in
theorem continuous_finiteOperatorColumns (b : HilbertBasis ι ℝ H) :
    Continuous (finiteOperatorColumns b) := by
  letI : FiniteDimensional ℝ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  exact (walshLpColumnsLinear b).continuous_of_finiteDimensional

theorem continuous_finiteSchattenPower (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p)
    {f : ℝ × ℝ → H →L[ℝ] H} (hf : Continuous f) :
    Continuous (fun θ => hsSchattenNorm b (finiteOperatorColumns b (f θ)) p ^ p) :=
  ((hsSchattenNorm_continuous b hp).comp ((continuous_finiteOperatorColumns b).comp hf)).rpow_const
    (fun _ => Or.inr (by linarith))

end FiniteContinuity

section PolynomialPeriodicity

variable {J H : Type*} [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem realMatrixTrigPolynomial_continuous (k : J → ℤ × ℤ) (X Y : J → H →L[ℝ] H) :
    Continuous (realMatrixTrigPolynomial k X Y) := by
  unfold realMatrixTrigPolynomial integerPlanePhase
  fun_prop

private theorem integerPlanePhase_add_one_fst (k : ℤ × ℤ) (x y : ℝ) :
    integerPlanePhase k (x + 1, y) = integerPlanePhase k (x, y) + (k.1 : ℝ) * (2 * Real.pi) := by
  unfold integerPlanePhase
  ring

private theorem integerPlanePhase_add_one_snd (k : ℤ × ℤ) (x y : ℝ) :
    integerPlanePhase k (x, y + 1) = integerPlanePhase k (x, y) + (k.2 : ℝ) * (2 * Real.pi) := by
  unfold integerPlanePhase
  ring

theorem realMatrixTrigPolynomial_periodic_fst (k : J → ℤ × ℤ) (X Y : J → H →L[ℝ] H) (y : ℝ) :
    Function.Periodic (fun x => realMatrixTrigPolynomial k X Y (x, y)) 1 := by
  intro x
  simp only [realMatrixTrigPolynomial, integerPlanePhase_add_one_fst,
    Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem realMatrixTrigPolynomial_periodic_snd (k : J → ℤ × ℤ) (X Y : J → H →L[ℝ] H) (x : ℝ) :
    Function.Periodic (fun y => realMatrixTrigPolynomial k X Y (x, y)) 1 := by
  intro y
  simp only [realMatrixTrigPolynomial, integerPlanePhase_add_one_snd,
    Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

end PolynomialPeriodicity

section AlgebraicTransport

variable {n : ℕ} {E F J : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [Fintype J]

def walshVectorMean (f : WalshCube n → E) : E :=
  (Fintype.card (WalshCube n) : ℝ)⁻¹ • ∑ ω, f ω

theorem walshVectorMean_complex (f : WalshCube n → ℂ) : walshVectorMean f = walshComplexMean f := by
  simp only [walshVectorMean, walshComplexMean, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast]

theorem walshVectorMean_map (L : E →ₗ[ℝ] F) (f : WalshCube n → E) :
    walshVectorMean (fun ω => L (f ω)) = L (walshVectorMean f) := by
  simp only [walshVectorMean, map_sum, map_smul]

theorem walshVectorMean_sum (f : J → WalshCube n → E) :
    walshVectorMean (fun ω => ∑ j, f j ω) = ∑ j, walshVectorMean (f j) := by
  unfold walshVectorMean
  rw [Finset.sum_comm, Finset.smul_sum]

theorem walshPrefixAverage_sum (l : ℕ) (f : J → WalshCube n → E) (ω : WalshCube n) :
    walshPrefixAverage l (fun η => ∑ j, f j η) ω = ∑ j, walshPrefixAverage l (f j) ω := by
  unfold walshPrefixAverage
  rw [Finset.sum_comm, Finset.smul_sum]

theorem walshCenteredTransform_map (L : E →ₗ[ℝ] F) (σ : Fin n → ℝ) (f : WalshCube n → E)
    (ω : WalshCube n) :
    walshCenteredTransform σ (fun η => L (f η)) ω = L (walshCenteredTransform σ f ω) := by
  simp only [walshCenteredTransform, walshPrefixAverage_map, map_sum, map_smul, map_sub]

theorem walshCenteredTransform_sum (σ : Fin n → ℝ) (f : J → WalshCube n → E) (ω : WalshCube n) :
    walshCenteredTransform σ (fun η => ∑ j, f j η) ω = ∑ j, walshCenteredTransform σ (f j) ω := by
  simp only [walshCenteredTransform, walshPrefixAverage_sum, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  rw [Finset.sum_comm]

def walshComplexMulLinear (z : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun w := z * w
  map_add' := mul_add z
  map_smul' r w := by simp only [Complex.real_smul, RingHom.id_apply]; ring

def walshPairLinear (X Y : E) : ℂ →ₗ[ℝ] E :=
  Complex.reLm.smulRight X + Complex.imLm.smulRight Y

@[simp] theorem walshPairLinear_apply (X Y : E) (z : ℂ) :
    walshPairLinear X Y z = z.re • X + z.im • Y := rfl

theorem walshCenteredTransform_const_mul (z : ℂ) (σ : Fin n → ℝ) (f : WalshCube n → ℂ)
    (ω : WalshCube n) :
    walshCenteredTransform σ (fun η => z * f η) ω = z * walshCenteredTransform σ f ω :=
  walshCenteredTransform_map (walshComplexMulLinear z) σ f ω

end AlgebraicTransport

private def integerPlanePhaseLinear (k : ℤ × ℤ) : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun := integerPlanePhase k
  map_add' x y := by simp only [integerPlanePhase, Prod.fst_add, Prod.snd_add]; ring
  map_smul' r x := by
    simp only [integerPlanePhase, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

private theorem walkComplexPhase_sum {J : Type*} [Fintype J] (f : J → ℝ) :
    walkComplexPhase (∑ j, f j) = ∏ j, walkComplexPhase (f j) := by
  classical
  have hh (s : Finset J) : walkComplexPhase (∑ j ∈ s, f j) = ∏ j ∈ s, walkComplexPhase (f j) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, walkComplexPhase_zero, Finset.prod_empty]
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj, Finset.prod_insert hj, walkComplexPhase_add, ih]
  exact hh Finset.univ

section SpatialProjection

variable {n : ℕ}

/-- Actual common displacement of all frequencies on the n-sign cube. -/
def walshSpatialDisplacement (v : Fin n → ℝ × ℝ) (ω : WalshCube n) : ℝ × ℝ :=
  ∑ j, walshSign (ω j) • v j

def walshFrequencyAngles (k : ℤ × ℤ) (v : Fin n → ℝ × ℝ) : Fin n → ℝ :=
  fun j => integerPlanePhase k (v j)

theorem walshPhaseProduct_displacement (k : ℤ × ℤ) (v : Fin n → ℝ × ℝ) (ω : WalshCube n) :
    walshPhaseProduct (walshFrequencyAngles k v) ω =
      walkComplexPhase (integerPlanePhase k (walshSpatialDisplacement v ω)) := by
  have hs : integerPlanePhase k (walshSpatialDisplacement v ω) =
      ∑ j, walshSign (ω j) * integerPlanePhase k (v j) := by
    change integerPlanePhaseLinear k (∑ j, walshSign (ω j) • v j) = _
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  rw [hs, walkComplexPhase_sum]
  rfl

private theorem walshMode_translate (k : ℤ × ℤ) (v : Fin n → ℝ × ℝ) (θ : ℝ × ℝ) (ω : WalshCube n) :
    walkComplexPhase (integerPlanePhase k (θ + walshSpatialDisplacement v ω)) =
      walkComplexPhase (integerPlanePhase k θ) * walshPhaseProduct (walshFrequencyAngles k v) ω := by
  rw [walshPhaseProduct_displacement, ← walkComplexPhase_add]
  congr 1
  exact (integerPlanePhaseLinear k).map_add _ _

private theorem walshMode_inverse_translate (k : ℤ × ℤ) (v : Fin n → ℝ × ℝ)
    (θ : ℝ × ℝ) (ω : WalshCube n) :
    walkComplexPhase (integerPlanePhase k (θ - walshSpatialDisplacement v ω)) =
      walkComplexPhase (integerPlanePhase k θ) * conj (walshPhaseProduct (walshFrequencyAngles k v) ω) := by
  rw [walshPhaseProduct_displacement, ← walkComplexPhase_neg, ← walkComplexPhase_add]
  congr 1
  exact (integerPlanePhaseLinear k).map_sub θ (walshSpatialDisplacement v ω)

variable {J H : Type*} [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual translated terminal matrix polynomial on the finite cube. -/
def walshTerminalPolynomial (k : J → ℤ × ℤ) (v : Fin n → ℝ × ℝ)
    (X Y : J → H →L[ℝ] H) (θ : ℝ × ℝ) (ω : WalshCube n) : H →L[ℝ] H :=
  realMatrixTrigPolynomial k X Y (θ + walshSpatialDisplacement v ω)

theorem walshTerminalPolynomial_mode_eq (k : J → ℤ × ℤ) (v : Fin n → ℝ × ℝ)
    (X Y : J → H →L[ℝ] H) (θ : ℝ × ℝ) (ω : WalshCube n) :
    walshTerminalPolynomial k v X Y θ ω = ∑ j,
      walshPairLinear (X j) (Y j) (walkComplexPhase (integerPlanePhase (k j) θ) *
        walshPhaseProduct (walshFrequencyAngles (k j) v) ω) := by
  unfold walshTerminalPolynomial realMatrixTrigPolynomial
  apply Finset.sum_congr rfl
  intro j _
  rw [← walshMode_translate]
  simp only [walshPairLinear_apply, walkComplexPhase_re, walkComplexPhase_im]

/-- All intermediate prefixes in the actual matrix polynomial are transported
by the proved linearity and the genuine phase-prefix computation. -/
theorem walshCenteredTransform_polynomial_eq (k : J → ℤ × ℤ) (v : Fin n → ℝ × ℝ)
    (X Y : J → H →L[ℝ] H) (θ : ℝ × ℝ) (σ : Fin n → ℝ) (ω : WalshCube n) :
    walshCenteredTransform σ (walshTerminalPolynomial k v X Y θ) ω = ∑ j,
      walshPairLinear (X j) (Y j) (walkComplexPhase (integerPlanePhase (k j) θ) *
        walshCenteredTransform σ (walshPhaseProduct (walshFrequencyAngles (k j) v)) ω) := by
  have heq : walshTerminalPolynomial k v X Y θ = fun η => ∑ j,
      walshPairLinear (X j) (Y j) (walkComplexPhase (integerPlanePhase (k j) θ) *
        walshPhaseProduct (walshFrequencyAngles (k j) v) η) := by
    funext η
    exact walshTerminalPolynomial_mode_eq k v X Y θ η
  rw [heq, walshCenteredTransform_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [walshCenteredTransform_map, walshCenteredTransform_const_mul]

def walshProjectedPolynomial (k : J → ℤ × ℤ) (v : Fin n → ℝ × ℝ)
    (X Y : J → H →L[ℝ] H) (σ : Fin n → ℝ) (θ : ℝ × ℝ) : H →L[ℝ] H :=
  walshVectorMean (fun ω => walshCenteredTransform σ
    (walshTerminalPolynomial k v X Y (θ - walshSpatialDisplacement v ω)) ω)

/-- Actual endpoint projection gives the exact finite real Fourier action of
the symbol derived from the actual prefix martingale. -/
theorem walshProjectedPolynomial_eq (k : J → ℤ × ℤ) (v : Fin n → ℝ × ℝ)
    (X Y : J → H →L[ℝ] H) (σ : Fin n → ℝ) (θ : ℝ × ℝ) :
    walshProjectedPolynomial k v X Y σ θ = realMatrixTrigPolynomial k
      (fun j => walshFiniteRieszSymbol (walshFrequencyAngles (k j) v) σ • X j)
      (fun j => walshFiniteRieszSymbol (walshFrequencyAngles (k j) v) σ • Y j) θ := by
  unfold walshProjectedPolynomial
  simp only [walshCenteredTransform_polynomial_eq, walshMode_inverse_translate, mul_assoc]
  rw [walshVectorMean_sum]
  unfold realMatrixTrigPolynomial
  apply Finset.sum_congr rfl
  intro j _
  rw [walshVectorMean_map]
  have hz : walshVectorMean (fun ω => walkComplexPhase (integerPlanePhase (k j) θ) *
      (conj (walshPhaseProduct (walshFrequencyAngles (k j) v) ω) *
        walshCenteredTransform σ (walshPhaseProduct (walshFrequencyAngles (k j) v)) ω)) =
      walkComplexPhase (integerPlanePhase (k j) θ) *
        (walshFiniteRieszSymbol (walshFrequencyAngles (k j) v) σ : ℂ) := by
    rw [walshVectorMean_complex, walshComplexMean_const_mul, walshComplexMean_endpoint_transform]
  rw [hz]
  simp only [walshPairLinear_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, walkComplexPhase_re, walkComplexPhase_im, zero_mul,
    sub_zero, zero_add, smul_smul, mul_comm]

end SpatialProjection

section ParameterNorm

variable {n : ℕ} {ι : Type uι} {H : Type uH} {Ω : Type*} [Fintype ι] [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem continuous_walshPrefixAverage_parameter
    {F : (ℝ × ℝ) → WalshCube n → H →L[ℝ] H}
    (hF : ∀ ω, Continuous (fun θ => F θ ω)) (l : ℕ) (ω : WalshCube n) :
    Continuous (fun θ => walshPrefixAverage l (F θ) ω) := by
  unfold walshPrefixAverage
  exact (continuous_finsetSum _ (fun η _ => hF _)).const_smul _

omit [CompleteSpace H] in
theorem continuous_walshCenteredTransform_parameter
    {F : (ℝ × ℝ) → WalshCube n → H →L[ℝ] H}
    (hF : ∀ ω, Continuous (fun θ => F θ ω)) (σ : Fin n → ℝ) (ω : WalshCube n) :
    Continuous (fun θ => walshCenteredTransform σ (F θ) ω) := by
  unfold walshCenteredTransform
  apply continuous_finsetSum
  intro j _
  exact ((continuous_walshPrefixAverage_parameter hF _ ω).sub
    (continuous_walshPrefixAverage_parameter hF _ ω)).const_smul _

theorem continuous_finiteFieldSchattenMoment (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p)
    {F : (ℝ × ℝ) → Ω → H →L[ℝ] H}
    (hF : ∀ ω, Continuous (fun θ => F θ ω)) :
    Continuous (fun θ => finiteFieldSchattenMoment b (F θ) p) := by
  unfold finiteFieldSchattenMoment
  exact continuous_const.mul (continuous_finsetSum _
    (fun ω _ => continuous_finiteSchattenPower b hp (hF ω)))

theorem integral_finiteFieldSchattenMoment (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p)
    {F : (ℝ × ℝ) → Ω → H →L[ℝ] H}
    (hF : ∀ ω, Continuous (fun θ => F θ ω)) :
    (∫ θ, finiteFieldSchattenMoment b (F θ) p ∂fourierSquareMeasure) =
      (Fintype.card Ω : ℝ)⁻¹ * ∑ ω,
        ∫ θ, hsSchattenNorm b (finiteOperatorColumns b (F θ ω)) p ^ p ∂fourierSquareMeasure := by
  simp only [finiteFieldSchattenMoment]
  rw [integral_const_mul, integral_finsetSum _ (fun ω _ =>
    integrable_fourierSquare_of_continuous (continuous_finiteSchattenPower b hp (hF ω)))]

set_option maxHeartbeats 800000 in
/-- The matching-Lp cost of a genuine finite deterministic martingale walk.
The translated terminal field, all its intermediate prefixes, the endpoint
projection and torus stationarity are derived here rather than assumed. -/
theorem walshProjectedPolynomial_schattenMoment_le {C : ℝ}
    (hU : FiniteWalshLpTransformBound.{uι,uH} C) (b : HilbertBasis ι ℝ H)
    {J : Type*} [Fintype J] (k : J → ℤ × ℤ) (v : Fin n → ℝ × ℝ)
    (X Y : J → H →L[ℝ] H) (σ : Fin n → ℝ) (hσ : ∀ j, |σ j| = 1) (m : ℕ) :
    (∫ θ, hsSchattenNorm b (finiteOperatorColumns b
      (walshProjectedPolynomial k v X Y σ θ)) (dyadicSchattenExponent m) ^
        (dyadicSchattenExponent m) ∂fourierSquareMeasure) ≤
      (C * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        ∫ θ, hsSchattenNorm b (finiteOperatorColumns b
          (realMatrixTrigPolynomial k X Y θ)) (dyadicSchattenExponent m) ^
            (dyadicSchattenExponent m) ∂fourierSquareMeasure := by
  classical
  let p := dyadicSchattenExponent m
  have hp : 2 ≤ p := dyadicSchattenExponent_ge_two m
  let F (θ : ℝ × ℝ) := walshTerminalPolynomial k v X Y θ
  let T (θ : ℝ × ℝ) (ω : WalshCube n) := walshCenteredTransform σ (F θ) ω
  let pow (A : H →L[ℝ] H) := hsSchattenNorm b (finiteOperatorColumns b A) p ^ p
  have hF (ω : WalshCube n) : Continuous (fun θ => F θ ω) :=
    (realMatrixTrigPolynomial_continuous k X Y).comp (continuous_id.add continuous_const)
  have hT (ω : WalshCube n) : Continuous (fun θ => T θ ω) :=
    continuous_walshCenteredTransform_parameter hF σ ω
  have hTx (ω : WalshCube n) (y : ℝ) :
      Function.Periodic (fun x => T (x,y) ω) 1 := by
    intro x
    apply congrArg (fun f : WalshCube n → H →L[ℝ] H => walshCenteredTransform σ f ω)
    funext η
    change realMatrixTrigPolynomial k X Y (x+1+(walshSpatialDisplacement v η).1,
      y+(walshSpatialDisplacement v η).2) = realMatrixTrigPolynomial k X Y
        (x+(walshSpatialDisplacement v η).1,y+(walshSpatialDisplacement v η).2)
    simpa only [add_assoc, add_comm, add_left_comm] using
      realMatrixTrigPolynomial_periodic_fst k X Y
        (y+(walshSpatialDisplacement v η).2) (x+(walshSpatialDisplacement v η).1)
  have hTy (ω : WalshCube n) (x : ℝ) :
      Function.Periodic (fun y => T (x,y) ω) 1 := by
    intro y
    apply congrArg (fun f : WalshCube n → H →L[ℝ] H => walshCenteredTransform σ f ω)
    funext η
    change realMatrixTrigPolynomial k X Y (x+(walshSpatialDisplacement v η).1,
      y+1+(walshSpatialDisplacement v η).2) = realMatrixTrigPolynomial k X Y
        (x+(walshSpatialDisplacement v η).1,y+(walshSpatialDisplacement v η).2)
    simpa only [add_assoc, add_comm, add_left_comm] using
      realMatrixTrigPolynomial_periodic_snd k X Y
        (x+(walshSpatialDisplacement v η).1) (y+(walshSpatialDisplacement v η).2)
  have hshift (ω : WalshCube n) :
      (∫ θ, pow (T (θ - walshSpatialDisplacement v ω) ω) ∂fourierSquareMeasure) =
        ∫ θ, pow (T θ ω) ∂fourierSquareMeasure := by
    simpa only [sub_eq_add_neg] using fourierSquare_integral_translate
      (continuous_finiteSchattenPower b hp (hT ω))
      (fun y x => congrArg pow (hTx ω y x))
      (fun x y => congrArg pow (hTy ω x y)) (-walshSpatialDisplacement v ω)
  have hshiftCont (ω : WalshCube n) :
      Continuous (fun θ => T (θ - walshSpatialDisplacement v ω) ω) :=
    (hT ω).comp (continuous_id.sub continuous_const)
  have hP : Continuous (fun θ => walshProjectedPolynomial k v X Y σ θ) := by
    simp only [walshProjectedPolynomial, walshVectorMean]
    exact (continuous_finsetSum _ (fun ω _ => hshiftCont ω)).const_smul _
  have hJ : (∫ θ, pow (walshProjectedPolynomial k v X Y σ θ) ∂fourierSquareMeasure) ≤
      ∫ θ, finiteFieldSchattenMoment b (fun ω => T (θ - walshSpatialDisplacement v ω) ω) p
        ∂fourierSquareMeasure := by
    apply integral_mono
      (integrable_fourierSquare_of_continuous (continuous_finiteSchattenPower b hp hP))
      (integrable_fourierSquare_of_continuous (continuous_finiteFieldSchattenMoment b hp hshiftCont))
    intro θ
    exact finiteSchatten_mean_rpow_le b (fun ω => T (θ - walshSpatialDisplacement v ω) ω) hp
  have havg : (∫ θ, finiteFieldSchattenMoment b
      (fun ω => T (θ - walshSpatialDisplacement v ω) ω) p ∂fourierSquareMeasure) =
      ∫ θ, finiteFieldSchattenMoment b (T θ) p ∂fourierSquareMeasure := by
    rw [integral_finiteFieldSchattenMoment b hp hshiftCont,
      integral_finiteFieldSchattenMoment b hp hT]
    exact congrArg (fun t : ℝ => (Fintype.card (WalshCube n) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl (fun ω _ => hshift ω))
  have hbound : (∫ θ, finiteFieldSchattenMoment b (T θ) p ∂fourierSquareMeasure) ≤
      (C*p)^p * ∫ θ, finiteFieldSchattenMoment b (F θ) p ∂fourierSquareMeasure := by
    rw [← integral_const_mul]
    apply integral_mono
      (integrable_fourierSquare_of_continuous (continuous_finiteFieldSchattenMoment b hp hT))
      ((integrable_fourierSquare_of_continuous
        (continuous_finiteFieldSchattenMoment b hp hF)).const_mul _)
    intro θ
    dsimp only [T, p]
    exact @FiniteWalshLpTransformBound.bound C hU ι _ H _ _ _ b n m σ hσ (F θ)
  have hstat : (∫ θ, finiteFieldSchattenMoment b (F θ) p ∂fourierSquareMeasure) =
      ∫ θ, pow (realMatrixTrigPolynomial k X Y θ) ∂fourierSquareMeasure := by
    rw [integral_finiteFieldSchattenMoment b hp hF]
    change (Fintype.card (WalshCube n) : ℝ)⁻¹ * (∑ ω : WalshCube n,
      ∫ θ, pow (F θ ω) ∂fourierSquareMeasure) = _
    have he (ω : WalshCube n) : (∫ θ, pow (F θ ω) ∂fourierSquareMeasure) =
        ∫ θ, pow (realMatrixTrigPolynomial k X Y θ) ∂fourierSquareMeasure :=
      fourierSquare_integral_translate
        (continuous_finiteSchattenPower b hp (realMatrixTrigPolynomial_continuous k X Y))
        (fun y x => congrArg pow (realMatrixTrigPolynomial_periodic_fst k X Y y x))
        (fun x y => congrArg pow (realMatrixTrigPolynomial_periodic_snd k X Y x y))
        (walshSpatialDisplacement v ω)
    simp_rw [he]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  exact (hJ.trans_eq havg).trans (hbound.trans_eq (by rw [hstat]))

end ParameterNorm


theorem walshPhaseEnergy_cons_zero {n : ℕ} (a : ℝ) (α : Fin n → ℝ) :
    walshPhaseEnergy (Fin.cons a α) 0 = Real.cos a ^ 2 * walshPhaseEnergy α 0 := by
  simp only [walshPhaseEnergy, Fin.prod_univ_succ, Fin.cons_zero,
    Nat.not_lt_zero, if_false, Fin.cons_succ]

theorem walshPhaseEnergy_cons_succ {n : ℕ} (a : ℝ) (α : Fin n → ℝ) (l : ℕ) :
    walshPhaseEnergy (Fin.cons a α) (l+1) = walshPhaseEnergy α l := by
  simp only [walshPhaseEnergy, Fin.prod_univ_succ, Fin.cons_zero, Fin.val_zero,
    Nat.zero_lt_succ, if_true, one_mul, Fin.cons_succ, Fin.val_succ,
    Nat.succ_lt_succ_iff]

theorem walshFiniteRieszSymbol_cons {n : ℕ} (a s : ℝ) (α σ : Fin n → ℝ) :
    walshFiniteRieszSymbol (Fin.cons a α) (Fin.cons s σ) =
      s * (1 - Real.cos a ^ 2) * walshPhaseEnergy α 0 + walshFiniteRieszSymbol α σ := by
  simp only [walshFiniteRieszSymbol, Fin.sum_univ_succ, Fin.cons_zero, Fin.val_zero,
    walshPhaseEnergy_cons_zero, walshPhaseEnergy_cons_succ,
    Fin.cons_succ, Fin.val_succ]
  ring

/-- Two successive signs per cycle, kept as a recursive actual finite cube size. -/
def walshCycleLength : ℕ → ℕ
  | 0 => 0
  | N+1 => walshCycleLength N + 1 + 1

def walshAlternatingAngles (a b : ℝ) : (N : ℕ) → Fin (walshCycleLength N) → ℝ
  | 0 => Fin.elim0
  | N+1 => Fin.cons a (Fin.cons b (walshAlternatingAngles a b N))

def walshAlternatingSigns : (N : ℕ) → Fin (walshCycleLength N) → ℝ
  | 0 => Fin.elim0
  | N+1 => Fin.cons 1 (Fin.cons (-1) (walshAlternatingSigns N))

def walshAlternatingDirections (u v : ℝ × ℝ) :
    (N : ℕ) → Fin (walshCycleLength N) → ℝ × ℝ
  | 0 => Fin.elim0
  | N+1 => Fin.cons u (Fin.cons v (walshAlternatingDirections u v N))

theorem walshAlternatingSigns_abs (N : ℕ) : ∀ j, |walshAlternatingSigns N j| = 1 := by
  induction N with
  | zero => intro j; exact Fin.elim0 j
  | succ N ih =>
    intro j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ih j) j) j <;> norm_num [walshAlternatingSigns]

theorem walshAlternatingAngles_energy (a b : ℝ) (N : ℕ) :
    walshPhaseEnergy (walshAlternatingAngles a b N) 0 = (walkCycleMultiplier a b ^ 2) ^ N := by
  induction N with
  | zero => simp [walshAlternatingAngles, walshPhaseEnergy, walshCycleLength]
  | succ N ih =>
    change walshPhaseEnergy (Fin.cons a (Fin.cons b (walshAlternatingAngles a b N))) 0 = _
    rw [walshPhaseEnergy_cons_zero, walshPhaseEnergy_cons_zero, ih]
    simp only [walkCycleMultiplier, pow_succ, mul_pow]
    ring

theorem walshAlternating_symbol (a b : ℝ) (N : ℕ) :
    walshFiniteRieszSymbol (walshAlternatingAngles a b N) (walshAlternatingSigns N) =
      walkRieszFiniteCoefficient a b N := by
  induction N with
  | zero => simp [walshAlternatingAngles, walshFiniteRieszSymbol, walkRieszFiniteCoefficient,
      walshCycleLength]
  | succ N ih =>
    change walshFiniteRieszSymbol (Fin.cons a (Fin.cons b (walshAlternatingAngles a b N)))
      (Fin.cons 1 (Fin.cons (-1) (walshAlternatingSigns N))) = _
    rw [walshFiniteRieszSymbol_cons, walshFiniteRieszSymbol_cons,
      walshPhaseEnergy_cons_zero, walshAlternatingAngles_energy, ih]
    simp only [
      walkRieszFiniteCoefficient, Finset.sum_range_succ]
    have ha : 1 - Real.cos a ^ 2 = Real.sin a ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq a]
    have hb : 1 - Real.cos b ^ 2 = Real.sin b ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq b]
    rw [ha, hb]
    unfold walkRieszNumerator
    ring

/-- The horizon limit is also valid at resonant steps: both numerator and
all finite coefficients then vanish exactly. -/
theorem walkRieszFiniteCoefficient_tendsto_all (a b : ℝ) :
    Tendsto (walkRieszFiniteCoefficient a b) atTop (𝓝 (walkRieszInfiniteCoefficient a b)) := by
  have hcle : |walkCycleMultiplier a b| ≤ 1 := by
    unfold walkCycleMultiplier
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one a) (Real.abs_cos_le_one b)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  by_cases hc : |walkCycleMultiplier a b| < 1
  · exact walkRieszFiniteCoefficient_tendsto a b hc
  have habs : |walkCycleMultiplier a b| = 1 := le_antisymm hcle (le_of_not_gt hc)
  have hsq : walkCycleMultiplier a b ^ 2 = 1 := by nlinarith [sq_abs (walkCycleMultiplier a b)]
  have hzero : walkRieszNumerator a b = 0 := by
    have hd := walkRieszDenominator a b
    rw [hsq] at hd
    unfold walkRieszNumerator
    nlinarith [mul_nonneg (sq_nonneg (Real.sin a)) (sq_nonneg (Real.cos b)),
      sq_nonneg (Real.sin b)]
  have he (N : ℕ) : walkRieszFiniteCoefficient a b N = 0 := by
    rw [walkRieszFiniteCoefficient, hzero, zero_mul]
  rw [show walkRieszFiniteCoefficient a b = (fun _ : ℕ => (0:ℝ)) by
    funext N; exact he N]
  simpa only [walkRieszInfiniteCoefficient, hzero, zero_div] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

/-- The small-step limit has the correct zero-frequency convention even for
singular translation directions. -/
theorem walkRieszInfiniteCoefficient_small_step_tendsto_all (a b : ℝ) :
    Tendsto (fun h => walkRieszInfiniteCoefficient (h*a) (h*b)) (𝓝[≠] (0:ℝ))
      (𝓝 (planarRieszSymbol planarReflectionMatrix (a,b))) := by
  by_cases hab : (a,b) = 0
  · have ha : a = 0 := congrArg Prod.fst hab
    have hb : b = 0 := congrArg Prod.snd hab
    simpa only [ha, hb, mul_zero, walkRieszInfiniteCoefficient, walkRieszNumerator,
      Real.sin_zero, Real.cos_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
      sub_self, zero_div, planarRieszSymbol, planarQuadraticForm, planarFrequencySq,
      planarReflectionMatrix, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[≠] (0:ℝ)) (𝓝 0))
  · exact walkRieszInfiniteCoefficient_small_step_tendsto a b hab

theorem walshFrequencyAngles_alternating (k : ℤ × ℤ) (u v : ℝ × ℝ) (N : ℕ) :
    walshFrequencyAngles k (walshAlternatingDirections u v N) =
      walshAlternatingAngles (integerPlanePhase k u) (integerPlanePhase k v) N := by
  induction N with
  | zero => funext j; exact Fin.elim0 j
  | succ N ih =>
    funext j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => congrFun ih j) j) j <;> rfl

section RieszLpLimits

variable {ι : Type uι} {H : Type uH} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : Type*} [Fintype J]

/-- Uniform matching-Lp estimate for the actual finite alternating walk in
arbitrary real directions. No independence of the directions is required. -/
theorem walkRieszFinite_schattenMoment_le_of_walsh {C : ℝ}
    (hU : FiniteWalshLpTransformBound.{uι,uH} C) (b : HilbertBasis ι ℝ H)
    (k : J → ℤ × ℤ) (X Y : J → H →L[ℝ] H) (u v : ℝ × ℝ) (N m : ℕ) :
    (∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k
      (fun j => walkRieszFiniteCoefficient (integerPlanePhase (k j) u)
        (integerPlanePhase (k j) v) N • X j)
      (fun j => walkRieszFiniteCoefficient (integerPlanePhase (k j) u)
        (integerPlanePhase (k j) v) N • Y j) θ)) (dyadicSchattenExponent m) ^
          (dyadicSchattenExponent m) ∂fourierSquareMeasure) ≤
      (C * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        ∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k X Y θ))
          (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure := by
  have ht := walshProjectedPolynomial_schattenMoment_le hU b k
    (walshAlternatingDirections u v N) X Y (walshAlternatingSigns N)
    (walshAlternatingSigns_abs N) m
  simpa only [walshProjectedPolynomial_eq, walshFrequencyAngles_alternating,
    walshAlternating_symbol] using ht

/-- The actual infinite-horizon coefficient bound follows from the proved
finite-walk estimate and genuine polynomial moment convergence. -/
theorem walkRieszInfinite_schattenMoment_le_of_walsh {C : ℝ}
    (hU : FiniteWalshLpTransformBound.{uι,uH} C) (b : HilbertBasis ι ℝ H)
    (k : J → ℤ × ℤ) (X Y : J → H →L[ℝ] H) (u v : ℝ × ℝ) (m : ℕ) :
    (∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k
      (fun j => walkRieszInfiniteCoefficient (integerPlanePhase (k j) u)
        (integerPlanePhase (k j) v) • X j)
      (fun j => walkRieszInfiniteCoefficient (integerPlanePhase (k j) u)
        (integerPlanePhase (k j) v) • Y j) θ)) (dyadicSchattenExponent m) ^
          (dyadicSchattenExponent m) ∂fourierSquareMeasure) ≤
      (C * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        ∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k X Y θ))
          (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure := by
  exact le_of_tendsto
    (weightedTrigPolynomial_schattenMoment_tendsto b k X Y
      (fun N j => walkRieszFiniteCoefficient (integerPlanePhase (k j) u)
        (integerPlanePhase (k j) v) N)
      (fun j => walkRieszInfiniteCoefficient (integerPlanePhase (k j) u)
        (integerPlanePhase (k j) v))
      (fun j => walkRieszFiniteCoefficient_tendsto_all _ _)
      (dyadicSchattenExponent_ge_two m))
    (Eventually.of_forall (fun N => walkRieszFinite_schattenMoment_le_of_walsh hU b k X Y u v N m))

/-- Full actual anisotropic Riesz multiplier bound, with the same martingale
constant. The two directions may be singular; joint zero frequencies have
the exact zero-symbol convention. This theorem uses no Fourier bound input. -/
theorem anisotropicRiesz_phase_schattenMoment_le_of_walsh {C : ℝ}
    (hU : FiniteWalshLpTransformBound.{uι,uH} C) (b : HilbertBasis ι ℝ H)
    (k : J → ℤ × ℤ) (X Y : J → H →L[ℝ] H) (u v : ℝ × ℝ) (m : ℕ) :
    (∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k
      (fun j => planarRieszSymbol planarReflectionMatrix
        (integerPlanePhase (k j) u, integerPlanePhase (k j) v) • X j)
      (fun j => planarRieszSymbol planarReflectionMatrix
        (integerPlanePhase (k j) u, integerPlanePhase (k j) v) • Y j) θ))
          (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure) ≤
      (C * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        ∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k X Y θ))
          (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure := by
  have hphase (k : ℤ × ℤ) (u : ℝ × ℝ) (h : ℝ) :
      integerPlanePhase k (h • u) = h * integerPlanePhase k u :=
    (integerPlanePhaseLinear k).map_smul h u
  have ht := weightedTrigPolynomial_schattenMoment_tendsto
    (l := 𝓝[≠] (0 : ℝ)) b k X Y
    (fun h j => walkRieszInfiniteCoefficient (h * integerPlanePhase (k j) u)
      (h * integerPlanePhase (k j) v))
    (fun j => planarRieszSymbol planarReflectionMatrix
      (integerPlanePhase (k j) u, integerPlanePhase (k j) v))
    (fun j => walkRieszInfiniteCoefficient_small_step_tendsto_all _ _)
    (dyadicSchattenExponent_ge_two m)
  apply le_of_tendsto ht
  filter_upwards [] with h
  simpa only [hphase] using
    walkRieszInfinite_schattenMoment_le_of_walsh hU b k X Y (h • u) (h • v) m

private theorem walshRiesz_phase_eq_dot (k : ℤ × ℤ) (u v : ℝ × ℝ) :
    planarRieszSymbol planarReflectionMatrix (integerPlanePhase k u, integerPlanePhase k v) =
      planarRieszSymbol planarReflectionMatrix
        ((k.1:ℝ)*u.1+(k.2:ℝ)*u.2, (k.1:ℝ)*v.1+(k.2:ℝ)*v.2) := by
  let s := (k.1:ℝ)*u.1+(k.2:ℝ)*u.2
  let t := (k.1:ℝ)*v.1+(k.2:ℝ)*v.2
  have hn : planarQuadraticForm planarReflectionMatrix
      ((2*Real.pi)*s,(2*Real.pi)*t) =
      (2*Real.pi)^2 * planarQuadraticForm planarReflectionMatrix (s,t) := by
    unfold planarQuadraticForm
    ring
  have hd : planarFrequencySq ((2*Real.pi)*s,(2*Real.pi)*t) =
      (2*Real.pi)^2 * planarFrequencySq (s,t) := by
    unfold planarFrequencySq
    ring
  change planarRieszSymbol planarReflectionMatrix ((2*Real.pi)*s,(2*Real.pi)*t) =
    planarRieszSymbol planarReflectionMatrix (s,t)
  rw [planarRieszSymbol, hn, hd,
    mul_div_mul_left _ _ (pow_ne_zero 2 (mul_ne_zero (by norm_num) Real.pi_ne_zero))]
  rfl

/-- Genuine dimension-free anisotropic second-order Riesz bound on actual
finite real matrix trigonometric polynomials. The only displayed input is
the generic finite Walsh martingale theorem, not a multiplier conclusion.
Both directions are arbitrary, and the zero denominator gives symbol zero. -/
theorem anisotropicRiesz_schattenMoment_le_of_walsh {C : ℝ}
    (hU : FiniteWalshLpTransformBound.{uι,uH} C) (b : HilbertBasis ι ℝ H)
    (k : J → ℤ × ℤ) (X Y : J → H →L[ℝ] H) (u v : ℝ × ℝ) (m : ℕ) :
    (∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k
      (fun j => planarRieszSymbol planarReflectionMatrix
        (((k j).1:ℝ)*u.1+((k j).2:ℝ)*u.2,
          ((k j).1:ℝ)*v.1+((k j).2:ℝ)*v.2) • X j)
      (fun j => planarRieszSymbol planarReflectionMatrix
        (((k j).1:ℝ)*u.1+((k j).2:ℝ)*u.2,
          ((k j).1:ℝ)*v.1+((k j).2:ℝ)*v.2) • Y j) θ))
          (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure) ≤
      (C * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        ∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k X Y θ))
          (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure := by
  simpa only [walshRiesz_phase_eq_dot] using
    anisotropicRiesz_phase_schattenMoment_le_of_walsh hU b k X Y u v m

end RieszLpLimits


end
end KernelSeq
