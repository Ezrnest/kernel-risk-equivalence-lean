import KernelSeq.LipschitzFourierTransference
import KernelSeq.FiniteDyadicLipschitz
import KernelSeq.RectangularSchurCompression

/-!
# Fixed-symbol transference with matching outer and Schatten exponents

The matching Lp(S_p) input aligns with the noncommutative weak-type
interpolation route. All phase and polynomial identities are reused from the
proved L2 transference; no exponent extrapolation theorem is assumed. The
Fourier bound remains an explicit input to this modular transference layer;
`FixedSymbolFourierLpBound` supplies `fixedEvenFourierLpBound_proved` and
`finiteDyadicLipschitzSchur_proved` as actual constructors.
-/

open MeasureTheory

namespace KernelSeq
noncomputable section

universe uν uι uH

/-- The modular Fourier interface with matching outer exponent. Its actual
constructor `fixedEvenFourierLpBound_proved` is proved separately in
`FixedSymbolFourierLpBound`. -/
structure FixedEvenFourierLpBound (C : ℝ) : Prop where
  constant_nonneg : 0 ≤ C
  bound : ∀ {ν : Type uν} {ι : Type uι} [Fintype ν] [Fintype ι]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ) (X Y : ν → H →L[ℝ] H) (n : ℕ),
    (∫ θ, hsSchattenNorm b
      (finiteOperatorColumns b (fixedEvenFourierPolynomial k X Y θ)) ((2 : ℝ) ^ (n + 1)) ^
        ((2 : ℝ) ^ (n + 1)) ∂fourierSquareMeasure) ≤
      (C * (2 : ℝ) ^ (n + 1)) ^ ((2 : ℝ) ^ (n + 1)) *
        (∫ θ, hsSchattenNorm b
          (finiteOperatorColumns b (realMatrixTrigPolynomial k X Y θ)) ((2 : ℝ) ^ (n + 1)) ^
            ((2 : ℝ) ^ (n + 1)) ∂fourierSquareMeasure)

variable {ι : Type uι} {H : Type uH} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Actual integer transference at matching exponents. No passage from
Lp(S_p) martingales to L2(S_p) is needed or asserted. -/
theorem integerFixedEvenSchur_dyadic_le_of_lp {C : ℝ}
    (hF : FixedEvenFourierLpBound.{uι, uι, uH} C)
    (b : HilbertBasis ι ℝ H) (k : ι → ℤ × ℤ) (n : ℕ) (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b (finiteSchurOperator b (integerFixedEvenKernel k) A))
        (dyadicSchattenExponent n) ≤
      (2 * C * dyadicSchattenExponent n) *
        hsSchattenNorm b (finiteOperatorColumns b A) (dyadicSchattenExponent n) := by
  let p := dyadicSchattenExponent n
  have hp : 2 ≤ p := dyadicSchattenExponent_ge_two n
  let d := realProdBasis b b
  let B := finiteSchurOperator b (integerFixedEvenKernel k) A
  have hfourier := hF.bound d (fun ij : ι × ι => k ij.1 - k ij.2)
    (phaseCosCoefficient b A) (phaseSinCoefficient b A) n
  simp only [realMatrixTrigPolynomial_phase_eq, fixedEvenFourierPolynomial_phase_eq] at hfourier
  change (∫ θ, hsSchattenNorm d
      (finiteOperatorColumns d (realPhaseConjugate b (fun i => integerPlanePhase (k i) θ)
        (realDoubleOperator B))) p ^ p ∂fourierSquareMeasure) ≤
    (C * p) ^ p * (∫ θ, hsSchattenNorm d
      (finiteOperatorColumns d (realPhaseConjugate b (fun i => integerPlanePhase (k i) θ)
        (realDoubleOperator A))) p ^ p ∂fourierSquareMeasure) at hfourier
  dsimp only [d] at hfourier
  simp only [realPhaseConjugate_schatten_eq b _ _ hp, integral_const,
    probReal_univ, smul_eq_mul, one_mul] at hfourier
  have hC : 0 ≤ C * p := mul_nonneg hF.constant_nonneg (by linarith)
  have hD : hsSchattenNorm d (finiteOperatorColumns d (realDoubleOperator B)) p ≤
      (C * p) * hsSchattenNorm d (finiteOperatorColumns d (realDoubleOperator A)) p := by
    have hA := hsSchattenNorm_nonneg d (finiteOperatorColumns d (realDoubleOperator A)) p
    apply (Real.rpow_le_rpow_iff (hsSchattenNorm_nonneg d _ p)
      (mul_nonneg hC hA) (by linarith : 0 < p)).mp
    simpa only [Real.mul_rpow hC hA] using hfourier
  calc
    _ ≤ hsSchattenNorm d (finiteOperatorColumns d (realDoubleOperator B)) p :=
      schatten_le_realDoubleOperator b B hp
    _ ≤ (C * p) * hsSchattenNorm d (finiteOperatorColumns d (realDoubleOperator A)) p := hD
    _ ≤ (C * p) * (2 * hsSchattenNorm b (finiteOperatorColumns b A) p) :=
      mul_le_mul_of_nonneg_left (realDoubleOperator_schatten_le b A hp) hC
    _ = _ := by ring

theorem integerFixedEvenSchurColumns_dyadic_le_of_lp {C : ℝ}
    (hF : FixedEvenFourierLpBound.{uι, uι, uH} C)
    (b : HilbertBasis ι ℝ H) (k : ι → ℤ × ℤ) (n : ℕ) (c : HilbertSchmidtColumns ι H) :
    hsSchattenNorm b (finiteMatrixSchurColumns b (integerFixedEvenKernel k) c)
        (dyadicSchattenExponent n) ≤
      (2 * C * dyadicSchattenExponent n) * hsSchattenNorm b c (dyadicSchattenExponent n) := by
  have ht := integerFixedEvenSchur_dyadic_le_of_lp hF b k n (hilbertSchmidtOperator b c)
  rw [finiteOperatorColumns_hilbertSchmidtOperator] at ht
  have heq : finiteOperatorColumns b
      (finiteSchurOperator b (integerFixedEvenKernel k) (hilbertSchmidtOperator b c)) =
        finiteMatrixSchurColumns b (integerFixedEvenKernel k) c := by
    apply hilbertSchmidtOperator_injective b
    rw [hilbertSchmidtOperator_finiteOperatorColumns]
    simp only [finiteSchurOperator, finiteOperatorColumns_hilbertSchmidtOperator]
  rwa [heq] at ht

universe u

/-- The matching-exponent Fourier estimate suffices for the actual dyadic
Lipschitz input, with every restriction and approximation proved. -/
theorem finiteDyadicLipschitzSchur_of_fixedEvenFourierLp {C : ℝ}
    (hF : FixedEvenFourierLpBound.{u, u, u} C) :
    FiniteDyadicLipschitzSchur.{u, u, u, u} (2 * C) where
  constant_nonneg := mul_nonneg (by norm_num) hF.constant_nonneg
  bound := by
    intro ι κ _ _ H E _ _ _ _ _ _ b a x y f L hL hf m c
    apply finiteDyadicLipschitz_grid_le_of_integer
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hF.constant_nonneg) b a ?_ x y f L hL hf m c
    intro x y m c
    apply rectangularFixedEvenSchur_dyadic_le b a x y m c
    have ht := integerFixedEvenSchurColumns_dyadic_le_of_lp hF (realProdBasis b a)
      (Sum.elim y x) m (realOffDiagonalColumns b a c)
    have hker : integerFixedEvenKernel (Sum.elim y x) = fun i j => lipschitzEvenSymbol
        (((Sum.elim y x) i).1 - ((Sum.elim y x) j).1)
        (((Sum.elim y x) i).2 - ((Sum.elim y x) j).2) := by
      funext i j
      simp only [integerFixedEvenKernel, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    rw [hker] at ht
    exact ht

end
end KernelSeq
