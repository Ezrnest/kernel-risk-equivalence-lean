import KernelSeq.SpherePolynomialLayers
import KernelSeq.SpherePolynomialOrthogonality
import KernelSeq.SphereDimensionAsymptotics

/-!
# Sharp dimensions of the actual orthogonal polynomial layers

The original d^m/m! normalization is squeezed between true squarefree and
symmetric-word counts. No exact harmonic multiplicity is an assumption.
-/

namespace KernelSeq
open MeasureTheory Submodule Filter
open scoped Topology
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem squarefreeSphereBlock_le_polynomialLayer (m : ℕ) :
    squarefreeSphereBlock ι m ≤ spherePolynomialLayer ι m := by
  cases m with
  | zero =>
    exact (squarefreeSphereBlock_le_homogeneous (ι := ι) 0).trans
      (homogeneousSpherePolynomialSpace_le_filtration le_rfl)
  | succ m => exact squarefreeSphereBlock_le_degree_layer m

theorem spherePolynomialLayer_finrank_lower (m : ℕ) :
    (Fintype.card ι).choose m ≤ Module.finrank ℝ (spherePolynomialLayer ι m) := by
  rw [← squarefreeSphereBlock_finrank (ι := ι) m]
  exact Submodule.finrank_mono (squarefreeSphereBlock_le_polynomialLayer m)

theorem spherePolynomialLayer_finrank_upper (m : ℕ) :
    Module.finrank ℝ (spherePolynomialLayer ι m) ≤ (Fintype.card ι+m-1).choose m := by
  cases m with
  | zero =>
    change Module.finrank ℝ (spherePolynomialSpace ι 0) ≤ _
    rw [Nat.choose_zero_right]
    refine (spherePolynomialSpace_finrank_upper (ι := ι) 0).trans ?_
    have hz (j : Fin (0+1)) : (j : ℕ) = 0 := by omega
    simp only [hz, Nat.choose_zero_right, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  | succ m =>
    have hsum := Submodule.finrank_add_le_finrank_add_finrank
      (spherePolynomialSpace ι m) (homogeneousSpherePolynomialSpace ι (m+1))
    rw [← spherePolynomialSpace_eq_sup_predecessor] at hsum
    have hdim := spherePolynomialLayer_finrank_add (ι := ι) m
    have hle : Module.finrank ℝ (spherePolynomialLayer ι (m+1)) ≤
        Module.finrank ℝ (homogeneousSpherePolynomialSpace ι (m+1)) := by omega
    exact hle.trans (homogeneousSpherePolynomialSpace_finrank_upper (m+1))

theorem spherePolynomialLayer_dimension_ratio_tendsto
    {I : Type*} {l : Filter I} (ι : I → Type*)
    [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (m : ℕ) (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => (Module.finrank ℝ (spherePolynomialLayer (ι i) m) : ℝ) /
      ((Fintype.card (ι i) : ℝ)^m/(m.factorial : ℝ))) l (𝓝 1) := by
  have hlo := (choose_shift_dimension_ratio_tendsto 0 m).comp hd
  simp only [Nat.add_zero, Function.comp_def] at hlo
  have hhi := (symmetric_degree_dimension_ratio_tendsto m).comp hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro i
    exact div_le_div_of_nonneg_right
      (show ((Fintype.card (ι i)).choose m : ℝ) ≤ (Module.finrank ℝ (spherePolynomialLayer (ι i) m) : ℝ) by
        exact_mod_cast spherePolynomialLayer_finrank_lower (ι := ι i) m) (by positivity)
  · intro i
    exact div_le_div_of_nonneg_right
      (show (Module.finrank ℝ (spherePolynomialLayer (ι i) m) : ℝ) ≤
        ((Fintype.card (ι i)+m-1).choose m : ℝ) by
          exact_mod_cast spherePolynomialLayer_finrank_upper (ι := ι i) m) (by positivity)

end
end KernelSeq
