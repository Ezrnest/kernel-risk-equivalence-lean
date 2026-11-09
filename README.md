# KSeqProof

KSeqProof is a Lean 4 companion to the work of Yicheng Li, Yuqian Cheng, Zhuo Chen, and Qian Lin on risk equivalence for kernel spectral algorithms. The [arXiv record](https://arxiv.org/abs/2609.08817) provides the preprint and its revision history.

The development relates the prediction risk of spectral estimators in reproducing kernel Hilbert space (RKHS) regression to the risk of the corresponding Gaussian sequence estimator. It also formalizes Pinsker minimax risk and high-dimensional spherical applications.

## Build

Install [Lean via Elan](https://lean-lang.org/install/manual/) and run the build from the repository root.

```sh
lake exe cache get
lake build
```

The toolchain file selects Lean 4.31.0. Lake uses the dependency revisions in `lake-manifest.json`.

## Main results

Import `KernelSeq` to load the development. The declarations in the table are in the `KernelSeq` namespace. Their Lean statements specify the precise hypotheses and conclusions.

| Result | Declaration | Source |
| --- | --- | --- |
| Conditional prediction-risk equivalence in probability | `rkhs_conditional_risk_equivalence` | [ConditionalRiskEquivalenceComplete.lean](KernelSeq/ConditionalRiskEquivalenceComplete.lean) |
| Expected prediction-risk equivalence and normalized conditional-risk convergence in L¹ | `rkhs_expectation_risk_equivalence` | [ExpectationRiskEquivalenceComplete.lean](KernelSeq/ExpectationRiskEquivalenceComplete.lean) |
| Conditional and expected risk equivalence along changing models | `triangular_conditional_risk_equivalence`, `triangular_expectation_risk_equivalence` | [TriangularRiskConvergence.lean](KernelSeq/TriangularRiskConvergence.lean) |
| Uniform conditional and expected risk equivalence over model families | `uniform_conditional_risk_equivalence`, `uniform_expectation_risk_equivalence` | [UniformRiskEquivalence.lean](KernelSeq/UniformRiskEquivalence.lean) |
| Exact Pinsker minimax constant and its attainment in Gaussian RKHS regression under an exact eigenvalue counting law | `rkhs_gaussian_pinsker_minimax` | [PinskerMinimax.lean](KernelSeq/PinskerMinimax.lean) |
| High-dimensional spherical Pinsker constant and kernel ridge regression risk rates | `rkhs_spherical_highDimensional_pinsker_halfLine`, `rkhs_spherical_highDimensional_krr` | [SphericalHighDimensionalApplications.lean](KernelSeq/SphericalHighDimensionalApplications.lean) |

## Proof audit

The default build runs [KernelSeqAudit.lean](KernelSeqAudit.lean). The audit checks that theorem and definition dependencies in the `KernelSeq` namespace use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. It also checks selected theorem signatures for external analytic premises.
