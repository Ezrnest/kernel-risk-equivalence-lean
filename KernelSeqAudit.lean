import KernelSeq

/-!
# Transitive foundation audit

Theorems, definitions, opaque constants, and axioms from `KernelFoundations`
and `KernelSeq` may depend only on the three standard foundations below.
Module provenance includes private declarations.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := env.allImportedModuleNames
  let mut checked := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let origin := modules[idx.toNat]!
    if (`KernelSeq).isPrefixOf origin || (`KernelFoundations).isPrefixOf origin then
      match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        checked := checked + 1
      | _ => pure ()
  logInfo m!"Audited {checked} declarations across KernelFoundations and KernelSeq: only propext, Classical.choice, Quot.sound allowed."

/- The complete main statement must not reintroduce one of the named
analytic proof interfaces as a public assumption. Source correspondence and
other possible hypotheses still require the separate statement review. -/
open Lean Elab Command in
run_cmd do
  let prohibited : Array Name := #[``KernelSeq.FiniteHMS, ``KernelSeq.FiniteLipschitzSchur,
    ``KernelSeq.FiniteDyadicLipschitzSchur, ``KernelSeq.FiniteIntrinsicBernstein,
    ``KernelSeq.FiniteUniformIntrinsicBernstein, ``KernelSeq.FiniteSpectralBernstein,
    ``KernelSeq.FixedEvenFourierL2Bound, ``KernelSeq.FixedEvenFourierLpBound,
    ``KernelSeq.FiniteWalshLpTransformBound]
  for mainName in #[``KernelSeq.rkhs_conditional_risk_equivalence,
      ``KernelSeq.rkhs_expectation_risk_equivalence,
      ``KernelSeq.triangular_conditional_risk_equivalence,
      ``KernelSeq.triangular_expectation_risk_equivalence,
      ``KernelSeq.uniform_conditional_risk_equivalence,
      ``KernelSeq.uniform_expectation_risk_equivalence,
      ``KernelSeq.uniform_risk_equivalence_diagonal,
      ``KernelSeq.uniform_expectation_risk_equivalence_diagonal] do
    let info ← getConstInfo mainName
    for name in prohibited do
      if (info.type.find? (fun e => e.isConstOf name)).isSome then
        throwError "External analytic interface {name} occurs in {mainName}"

/- The changing-model and uniform conditional statements retain just the
two original scales. The extra expectation scale belongs only to the
expectation statements. This syntactic guard supplements source review. -/
open Lean Elab Command in
run_cmd do
  for mainName in #[``KernelSeq.triangular_conditional_risk_equivalence,
      ``KernelSeq.uniform_conditional_risk_equivalence,
      ``KernelSeq.uniform_risk_equivalence_diagonal] do
    let info ← getConstInfo mainName
    if (info.type.find? (fun e =>
        e.isConstOf ``KernelSeq.TriangularRiskModel.expectationScale)).isSome then
      throwError "Extra expectation scale occurs in conditional statement {mainName}"

/- Concrete applications must derive the three scale and dimension estimates
from their primitive spectrum/source assumptions. The regularization IsTheta
assumption is original; a direct Big-O or scale hypothesis is not an application
input. This guard checks explicit binder domains and supplements source review. -/
open Lean Elab Command in
run_cmd do
  let prohibited : Array Name := #[``Asymptotics.IsBigO,
    ``KernelSeq.SpectralScaleModel.compatibility, ``KernelSeq.SpectralScaleModel.sourceBalance,
    ``KernelSeq.SpectralScaleModel.expectationScale,
    ``KernelSeq.TriangularRiskModel.compatibility, ``KernelSeq.TriangularRiskModel.sourceBalance,
    ``KernelSeq.TriangularRiskModel.expectationScale]
  for mainName in #[``KernelSeq.rkhs_gaussian_pinsker_minimax,
      ``KernelSeq.rkhs_gaussian_pinsker_upper_bound,
      ``KernelSeq.pinsker_minimax_constant,
      ``KernelSeq.pinsker_minimax_attainment,
      ``KernelSeq.pinsker_sourceBall_upper_bound,
      ``KernelSeq.canonical_gaussian_pinsker_sourceBall_upper_bound,
      ``KernelSeq.spherical_sourceBall_original_scales,
      ``KernelSeq.spherical_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_spherical_sourceBall_risk_equivalence,
      ``KernelSeq.spherical_retained_sourceBall_original_scales,
      ``KernelSeq.spherical_retained_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_spherical_retained_sourceBall_risk_equivalence,
      ``KernelSeq.spherical_highDimensionalRidge_original_scales,
      ``KernelSeq.spherical_phaseCutoff_expected_limit,
      ``KernelSeq.rkhs_spherical_minimax_normalized_lower,
      ``KernelSeq.rkhs_spherical_highDimensional_pinsker,
      ``KernelSeq.rkhs_spherical_highDimensional_pinsker_halfLine,
      ``KernelSeq.rkhs_spherical_highDimensional_krr,
      ``KernelSeq.exact_counting_universal_sourceBall_original_scales,
      ``KernelSeq.polynomial_sourceBall_original_scales_of_spectral_threshold,
      ``KernelSeq.polynomial_universal_sourceBall_original_scales_of_spectral_threshold,
      ``KernelSeq.exponential_sourceBall_original_scales,
      ``KernelSeq.polynomial_sourceBall_risk_equivalence,
      ``KernelSeq.polynomial_universal_sourceBall_risk_equivalence,
      ``KernelSeq.exponential_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_polynomial_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_polynomial_universal_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_exponential_sourceBall_risk_equivalence] do
    let info ← getConstInfo mainName
    let mut current := info.type
    while current.isForall do
      let domain := current.bindingDomain!
      for name in prohibited do
        if (domain.find? (fun e => e.isConstOf name)).isSome then
          throwError "Extra analytic or scale input {name} in application {mainName}"
      current := current.bindingBody!
