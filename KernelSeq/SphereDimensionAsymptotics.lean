import KernelSeq.SphereMonomialBlock
import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Exact fixed-degree spherical dimension normalizations

The squarefree block dimension is the actual finite-span dimension already
proved from the monomial Gram matrix. Binomial coefficient asymptotics and
the genuine spherical product moments yield the sharp fixed-degree leading
constants, including empty degree blocks at early dimensions.
-/

namespace KernelSeq

open Filter Asymptotics
open scoped Topology BigOperators
noncomputable section

theorem choose_shift_dimension_ratio_tendsto (c m : ℕ) :
    Tendsto (fun d : ℕ => ((d+c).choose m : ℝ)/((d:ℝ)^m/(m.factorial : ℝ))) atTop (𝓝 1) := by
  have hne : ∀ᶠ d : ℕ in atTop, (d : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with d hd
    exact ne_of_gt (by exact_mod_cast hd : (0 : ℝ) < d)
  have hshift : (fun d : ℕ => ((d+c : ℕ) : ℝ)) ~[atTop] (fun d : ℕ => (d : ℝ)) := by
    apply (isEquivalent_iff_tendsto_one hne).mpr
    change Tendsto (fun d : ℕ => ((d+c : ℕ) : ℝ)/(d:ℝ)) atTop (𝓝 1)
    have hh := (tendsto_natCast_div_add_atTop (c : ℝ)).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [Nat.cast_add, inv_div, inv_one] using hh
  have hchoose := (isEquivalent_choose m).comp_tendsto
    ((tendsto_add_atTop_iff_nat c).mpr (tendsto_id : Tendsto (fun d : ℕ => d) atTop atTop))
  have heq : (fun d : ℕ => ((d+c).choose m : ℝ)) ~[atTop]
      (fun d : ℕ => (d:ℝ)^m/(m.factorial : ℝ)) :=
    hchoose.trans ((hshift.pow m).div IsEquivalent.refl)
  apply (isEquivalent_iff_tendsto_one ?_).mp heq
  filter_upwards [hne] with d hd
  exact div_ne_zero (pow_ne_zero _ hd) (by exact_mod_cast m.factorial_ne_zero)

theorem symmetric_degree_dimension_ratio_tendsto (m : ℕ) :
    Tendsto (fun d : ℕ => ((d+m-1).choose m : ℝ)/((d:ℝ)^m/(m.factorial : ℝ))) atTop (𝓝 1) := by
  by_cases hm : m = 0
  · subst m
    simpa only [Nat.choose_zero_right, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one] using
      (tendsto_const_nhds (x := (1 : ℝ)))
  · have h := choose_shift_dimension_ratio_tendsto (m-1) m
    simpa only [Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr hm)] using h

/-- The actual degree moment, normalized by the ambient dimension, is the
finite product of genuine scalar ratios. -/
theorem degreeSphereMoment_dimension_product
    {ι : Type*} [Fintype ι] (m : ℕ) :
    degreeSphereMoment ι m*(Fintype.card ι : ℝ)^m =
      ∏ j ∈ Finset.range m, (Fintype.card ι : ℝ)/((Fintype.card ι : ℝ)+2*(j:ℝ)) := by
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_range, degreeSphereMoment]
  ring

theorem fixed_degreeMoment_dimension_ratio_tendsto (m : ℕ) :
    Tendsto (fun d : ℕ =>
      (∏ j ∈ Finset.range m, ((d:ℝ)+2*(j:ℝ)))⁻¹*(d:ℝ)^m) atTop (𝓝 1) := by
  have hh : Tendsto (fun d : ℕ => ∏ j ∈ Finset.range m,
      (d:ℝ)/((d:ℝ)+2*(j:ℝ))) atTop (𝓝 1) := by
    have hp := tendsto_finsetProd (Finset.range m)
      (fun j _ => tendsto_natCast_div_add_atTop (2*(j:ℝ)))
    simpa only [Finset.prod_const_one] using hp
  apply hh.congr
  intro d
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_range]
  ring

section ActualDimensionFamilies

variable {I : Type*} {l : Filter I}

theorem squarefreeSphereBlock_dimension_ratio_tendsto
    (ι : I → Type*) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (m : ℕ) (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => (Module.finrank ℝ (squarefreeSphereBlock (ι i) m) : ℝ)/
      ((Fintype.card (ι i) : ℝ)^m/(m.factorial : ℝ))) l (𝓝 1) := by
  have hh := (choose_shift_dimension_ratio_tendsto 0 m).comp hd
  simpa only [Nat.add_zero, squarefreeSphereBlock_finrank, Function.comp_def] using hh

theorem degreeSphereMoment_dimension_ratio_tendsto
    (ι : I → Type*) [∀ i, Fintype (ι i)] (m : ℕ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => degreeSphereMoment (ι i) m*(Fintype.card (ι i) : ℝ)^m) l (𝓝 1) := by
  exact (fixed_degreeMoment_dimension_ratio_tendsto m).comp hd

end ActualDimensionFamilies
end
end KernelSeq
