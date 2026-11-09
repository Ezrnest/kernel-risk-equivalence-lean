import KernelSeq.SpherePolynomialSpace
import KernelSeq.SphereDimensionAsymptotics

/-!
# The sharp leading dimension of the actual spherical polynomial space

True squarefree and symmetric-word dimensions squeeze the actual L2 span.
The result is a statement about the constructed subspace, not a prescribed
harmonic multiplicity or an abstract dimension certificate.
-/

namespace KernelSeq
open Filter
open scoped Topology
noncomputable section

theorem homogeneousSpherePolynomialSpace_dimension_ratio_tendsto
    {I : Type*} {l : Filter I} (ι : I → Type*)
    [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (m : ℕ) (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => (Module.finrank ℝ (homogeneousSpherePolynomialSpace (ι i) m) : ℝ) /
      ((Fintype.card (ι i) : ℝ)^m/(m.factorial : ℝ))) l (𝓝 1) := by
  have hlo := (choose_shift_dimension_ratio_tendsto 0 m).comp hd
  simp only [Nat.add_zero, Function.comp_def] at hlo
  have hhi := (symmetric_degree_dimension_ratio_tendsto m).comp hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro i
    exact div_le_div_of_nonneg_right
      (show ((Fintype.card (ι i)).choose m : ℝ) ≤
        (Module.finrank ℝ (homogeneousSpherePolynomialSpace (ι i) m) : ℝ) by
          exact_mod_cast homogeneousSpherePolynomialSpace_finrank_lower (ι := ι i) m) (by positivity)
  · intro i
    exact div_le_div_of_nonneg_right
      (show (Module.finrank ℝ (homogeneousSpherePolynomialSpace (ι i) m) : ℝ) ≤
        ((Fintype.card (ι i)+m-1).choose m : ℝ) by
          exact_mod_cast homogeneousSpherePolynomialSpace_finrank_upper (ι := ι i) m) (by positivity)

end
end KernelSeq
