import Lake

open Lake DSL

package KSeqProof where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"

@[default_target]
lean_lib KernelFoundations where
  globs := #[`KernelFoundations.*]

@[default_target]
lean_lib KernelSeq where
  globs := #[`KernelSeq.*]

/-- Check the umbrella against the source tree even when the audit is up to date. -/
target checkAuditCoverage : Unit := do
  let some lib ← findLeanLib? `KernelSeq | error "Missing KernelSeq library"
  let some foundations ← findLeanLib? `KernelFoundations | error "Missing KernelFoundations library"
  let some foundationRoot := foundations.findModule? `KernelFoundations
    | error "Missing KernelFoundations umbrella"
  let some audit ← findModule? `KernelSeqAudit | error "Missing KernelSeqAudit module"
  let directImports ← (← audit.imports.fetch).await
  let some root := directImports.find? (·.name == `KernelSeq)
    | error "KernelSeqAudit must import KernelSeq"
  let modules ← lib.getModuleArray
  let foundationModules ← foundations.getModuleArray
  let foundationImports ← (← foundationRoot.transImports.fetch).await
  if foundationImports.any (fun mod => mod.lib.name == lib.name) then
    error "KernelFoundations must not depend on KernelSeq"
  let foundationSet := Std.HashSet.ofArray foundationImports
  let missingFoundations := foundationModules.filter fun mod =>
    mod != foundationRoot && !foundationSet.contains mod
  unless missingFoundations.isEmpty do
    let names := String.intercalate ", " (missingFoundations.toList.map (·.name.toString))
    error s!"Modules missing from the KernelFoundations umbrella: {names}"
  (← root.transImports.fetch).mapM fun imports => do
    let imported := Std.HashSet.ofArray imports
    let missing := (modules ++ foundationModules).filter fun mod =>
      mod != root && !imported.contains mod
    unless missing.isEmpty do
      let names := String.intercalate ", " (missing.toList.map (·.name.toString))
      error s!"Modules missing from the KernelSeq umbrella and audit: {names}"

@[default_target]
lean_lib KernelSeqAudit where
  needs := #[checkAuditCoverage]
