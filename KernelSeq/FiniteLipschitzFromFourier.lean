import KernelSeq.FiniteDyadicLipschitz
import KernelSeq.RectangularSchurCompression
import KernelSeq.LipschitzFourierTransference

/-!
# The finite dyadic Lipschitz leaf from one fixed Fourier multiplier

Actual real phase transference gives the square integer-grid estimate.
The proved real block lift gives independent rectangular grids, and genuine
integer approximation yields the original real divided differences. No
general HMS or Lipschitz multiplier bound is an input to this reduction.
The displayed fixed-symbol Fourier norm estimate remains unproved.
-/

namespace KernelSeq
noncomputable section

universe u

/-- The one fixed smooth even Fourier estimate suffices for every genuine
finite rectangular Lipschitz grid at the required dyadic exponents. All
transference, real restriction, approximation and scaling are proved. -/
theorem finiteDyadicLipschitzSchur_of_fixedEvenFourier {C : ℝ}
    (hF : FixedEvenFourierL2Bound.{u, u, u} C) :
    FiniteDyadicLipschitzSchur.{u, u, u, u} (2 * C) where
  constant_nonneg := mul_nonneg (by norm_num) hF.constant_nonneg
  bound := by
    intro ι κ _ _ H E _ _ _ _ _ _ b a x y f L hL hf m c
    apply finiteDyadicLipschitz_grid_le_of_integer
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hF.constant_nonneg) b a ?_ x y f L hL hf m c
    intro x y m c
    apply rectangularFixedEvenSchur_dyadic_le b a x y m c
    have ht := integerFixedEvenSchurColumns_dyadic_le hF (realProdBasis b a)
      (Sum.elim y x) m (realOffDiagonalColumns b a c)
    have hker : integerFixedEvenKernel (Sum.elim y x) = fun i j => lipschitzEvenSymbol
        (((Sum.elim y x) i).1 - ((Sum.elim y x) j).1)
        (((Sum.elim y x) i).2 - ((Sum.elim y x) j).2) := by
      funext i j
      simp only [integerFixedEvenKernel, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    rw [hker] at ht
    simpa only [dyadicSchattenExponent] using ht

end
end KernelSeq
