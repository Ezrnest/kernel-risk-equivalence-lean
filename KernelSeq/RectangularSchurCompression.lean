import KernelSeq.RectangularTriangularSchur
import KernelSeq.LipschitzEvenSymbol
import KernelSeq.DyadicSchattenEndpoint

/-!
# Actual rectangular restriction of square Schur matrices

Real off-diagonal lifting and coordinate compression transfer a square
fixed-symbol estimate to two independent rectangular grids. All column
identities and Schatten contraction factors are proved locally.
-/

namespace KernelSeq
noncomputable section

variable {ι κ H E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem finiteMatrixSchurColumns_eq_rectangular_compression
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (M : κ → ι → ℝ) (N : (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (hN : ∀ i j, N (Sum.inr i) (Sum.inl j) = M i j)
    (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a M c =
      hsCompressionColumns (realProdBasis b a) b (realProdBasis b a) (realProdInl (E := E))
        (WithLp.sndL 2 ℝ H E)
        (finiteMatrixSchurColumns (realProdBasis b a) N (realOffDiagonalColumns b a c)) := by
  apply hilbertSchmidtOperator_injective b
  rw [hilbertSchmidtOperator_compression]
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro j
  apply a.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [finiteMatrixSchurColumns_coefficient]
  change _ = inner ℝ (a i) ((WithLp.sndL 2 ℝ H E)
    (hilbertSchmidtOperator (realProdBasis b a)
      (finiteMatrixSchurColumns (realProdBasis b a) N (realOffDiagonalColumns b a c))
        (realProdInl (E := E) (b j))))
  rw [realProd_compression_coefficient, finiteBasisEntry,
    finiteMatrixSchurColumns_coefficient, hN,
    ← hilbertSchmidtOperator_basis (realProdBasis b a) (realOffDiagonalColumns b a c) (Sum.inl j),
    ← finiteBasisEntry, hilbertSchmidtOperator_realOffDiagonalColumns,
    realOffDiagonalLift_coefficient]
  rw [hilbertSchmidtOperator_basis]

/-- A genuine square integer-frequency estimate gives the rectangular one
with the same constant. The square estimate remains explicitly an input. -/
theorem rectangularFixedEvenSchur_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    {C : ℝ} (x : κ → ℤ × ℤ) (y : ι → ℤ × ℤ) (m : ℕ)
    (c : HilbertSchmidtColumns ι E)
    (hsquare : hsSchattenNorm (realProdBasis b a)
      (finiteMatrixSchurColumns (realProdBasis b a)
        (fun i j => lipschitzEvenSymbol
          (((Sum.elim y x) i).1 - ((Sum.elim y x) j).1)
          (((Sum.elim y x) i).2 - ((Sum.elim y x) j).2))
        (realOffDiagonalColumns b a c)) (dyadicSchattenExponent m) ≤
      C * dyadicSchattenExponent m *
        hsSchattenNorm (realProdBasis b a) (realOffDiagonalColumns b a c)
          (dyadicSchattenExponent m)) :
    hsSchattenNorm b (finiteMatrixSchurColumns a
      (fun i j => lipschitzEvenSymbol ((x i).1 - (y j).1) ((x i).2 - (y j).2)) c)
        (dyadicSchattenExponent m) ≤
      C * dyadicSchattenExponent m * hsSchattenNorm b c (dyadicSchattenExponent m) := by
  have hp := dyadicSchattenExponent_ge_two m
  have heq := finiteMatrixSchurColumns_eq_rectangular_compression b a
    (fun i j => lipschitzEvenSymbol ((x i).1 - (y j).1) ((x i).2 - (y j).2))
    (fun i j => lipschitzEvenSymbol
      (((Sum.elim y x) i).1 - ((Sum.elim y x) j).1)
      (((Sum.elim y x) i).2 - ((Sum.elim y x) j).2)) (fun _ _ => rfl) c
  rw [heq]
  refine (hsSchattenNorm_compression_le (realProdBasis b a) b (realProdBasis b a)
    (realProdInl (E := E)) (WithLp.sndL 2 ℝ H E)
      (realProd_snd_norm_le (H := H) (E := E)) _ hp).trans ?_
  simpa only [realOffDiagonalColumns_schatten_eq b a c hp] using hsquare

end
end KernelSeq
