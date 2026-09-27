import FastConfirmation
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.Old
import Lean.Data.Json
import Lean.DeclarationRange
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.Path
import Lean.Util.Sorry

/-!
# Project trust audit

This file is run with `lake env lean scripts/Audit.lean` after the project has
been built. It is deliberately outside the library import graph.

The audit first resolves the object file of every loaded module on the Lean
search path, with the rule that Lean uses for an import: the first search path
entry that holds the root name of the module. The resolved file decides the
owner of each declaration:

* a module in the project build folder must have a project name and a project
  source file; the audit checks all of its declarations;
* every other module must resolve to the toolchain library or to a package that
  `lake-manifest.json` pins, at the pinned Git revision, with a tracked and
  unchanged source file.

A second search path entry that holds the same root name is a shadow, and the
audit fails. In Model and Statements, the audit also rejects each authored
proof that is not in `allowedModelProofs`.
-/

open Lean Elab Command Meta

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def publicWitnesses : Array Name :=
  #[
    ``FastConfirmation.Spec.review_claims,
    ``FastConfirmation.Spec.confirmed_root_safe_from_next_slot,
    ``FastConfirmation.Spec.NextSlotPremiseWitness.finite_execution_satisfies_premises,
    ``FastConfirmation.Spec.NextSlotPremiseWitness.next_slot_premises_nonempty,
    ``FastConfirmation.Spec.NextSlotPremiseWitness.ffg_interpretation_fidelity,
    ``FastConfirmation.Spec.GenesisStubPremiseWitness.genesis_stub_full_bundle_witness,
    ``FastConfirmation.Spec.GenesisStubPremiseWitness.ffg_interpretation_fidelity,
    ``FastConfirmation.Spec.FullTwelveWitness.full_bundle_witness,
    ``FastConfirmation.Spec.FullTwelveWitness.changed_root_safe_from_next_slot,
    ``FastConfirmation.Spec.FullTwelveWitness.delayed_receipts_are_first,
    ``FastConfirmation.Spec.FullTwelveWitness.ffg_interpretation_fidelity,
    ``FastConfirmation.Spec.TargetEdgePremiseWitness.full_bundle_witness,
    ``FastConfirmation.Spec.TargetEdgePremiseWitness.target_edge_support_exercised,
    ``FastConfirmation.Spec.TargetEdgePremiseWitness.target_edge_safe_from_next_slot,
    ``FastConfirmation.Spec.TargetEdgePremiseWitness.ffg_interpretation_fidelity,
    ``FastConfirmation.Spec.FullTwelveEnvelopeWitness.full_bundle_witness,
    ``FastConfirmation.Spec.FullTwelveEnvelopeWitness.changed_root_safe_from_next_slot,
    ``FastConfirmation.Spec.FullTwelveEnvelopeWitness.payload_accepted_with_delay,
    ``FastConfirmation.Spec.FullTwelveEnvelopeWitness.envelope_relay_exercised,
    ``FastConfirmation.Spec.FullTwelveEnvelopeBridgeRun.single_early_envelope_receipt,
    ``FastConfirmation.Spec.FullTwelveEnvelopeWitness.payload_status_branches,
    ``FastConfirmation.Spec.FullTwelveEnvelopeWitness.fcr_branch_samples,
    ``FastConfirmation.Spec.FullTwelveEnvelopeWitness.fcr_guard_samples,
    ``FastConfirmation.Spec.FullTwelveEnvelopeWitness.gloas_discount_sample,
    ``FastConfirmation.Spec.FullTwelveEnvelopeWitness.ffg_interpretation_fidelity,
    ``FastConfirmation.Spec.ByzantinePremiseWitness.full_bundle_witness,
    ``FastConfirmation.Spec.ByzantinePremiseWitness.byzantine_weight_exercised,
    ``FastConfirmation.Spec.ByzantinePremiseWitness.slashing_relay_exercised,
    ``FastConfirmation.Spec.ByzantinePremiseWitness.changed_root_safe_from_next_slot,
    ``FastConfirmation.Spec.ByzantinePremiseWitness.ffg_interpretation_fidelity,
    ``FastConfirmation.Spec.ByzantinePremiseWitness.previous_result_proviso_exercised,
    ``FastConfirmation.Spec.ByzantinePremiseWitness.previous_result_descendant_support_exercised,
    ``FastConfirmation.Spec.CheckpointSyncFilterWitness.checkpoint_sync_filter_counterexample,
    ``FastConfirmation.Spec.CheckpointSyncFilterWitness.normalized_anchor_run_keeps_child,
    ``FastConfirmation.Spec.CheckpointSyncFilterWitness.anchor_only_view_satisfies_inclusion,
    ``FastConfirmation.Spec.EarlyEpochBoundaryWitness.epoch_one_boundary_regression,
    ``FastConfirmation.Spec.EarlyEpochBoundaryWitness.epoch_one_fixture_satisfies_boundary_laws,
    ``FastConfirmation.Spec.EstimateForcesBalance.slot_committee_weight_forced,
    ``FastConfirmation.Spec.StrictPrefixExtraQuery.extra_query_changes_head_counterexample,
    ``FastConfirmation.Spec.PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample
  ]

/-- Authored proofs that Model or Statements may hold, each with its reason. -/
private def allowedModelProofs : Array (Name × String) :=
  #[(``FastConfirmation.Spec.Execution.SuccessfulScheduledBlockImport.processedCount_lt,
     "supports the successor-prefix definition in Model")]

private def libraries : Array String :=
  #["FastConfirmationModel", "FastConfirmationStatements", "FastConfirmationInternal",
    "FastConfirmationProofs", "FastConfirmationWitnesses"]

private def inLibraries (libs : Array String) (module : Name) : Bool :=
  let text := module.toString
  libs.any fun lib => text == lib || text.startsWith (lib ++ ".")

private def isProjectName (module : Name) : Bool :=
  module == `FastConfirmation || inLibraries libraries module

private def unexpectedAxioms (axioms : Array Name) : Array Name :=
  axioms.filter fun name => !allowedAxioms.contains name

/-! ## Resolved module provenance -/

private inductive ModuleOrigin where
  | project
  | toolchain
  | package (name : String)
  deriving BEq, Inhabited

private structure PinnedPackage where
  name : String
  build : System.FilePath
  tracked : Std.HashSet String

private def realOrSelf (path : System.FilePath) : IO System.FilePath := do
  try return (← IO.FS.realPath path).normalize catch _ => return path.normalize

private def isUnder (root path : System.FilePath) : Bool :=
  path.toString.startsWith (root.toString ++ System.FilePath.pathSeparator.toString)

private def git (folder : System.FilePath) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["-C", folder.toString] ++ args }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"git {args} failed in {folder}: {out.stderr}"
  return out.stdout

/-- Read the pinned packages. Each checkout must be at its manifest revision
with no changed tracked file; the tracked file list is kept. -/
private def pinnedPackages (root : System.FilePath) : IO (Array PinnedPackage) := do
  let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "lake-manifest.json"))
  let packages ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "packages"
  let mut result := #[]
  for package in packages do
    let name ← IO.ofExcept <| package.getObjValAs? String "name"
    let rev ← IO.ofExcept <| package.getObjValAs? String "rev"
    let folder := root / ".lake" / "packages" / name
    let head := (← git folder #["rev-parse", "HEAD"]).trimAscii.copy
    unless head == rev do
      throw <| IO.userError s!"package {name} is at {head}, not the pinned {rev}"
    unless (← git folder #["status", "--porcelain", "--untracked-files=no"]).isEmpty do
      throw <| IO.userError s!"pinned package {name} has changed tracked files"
    let tracked := ((← git folder #["ls-files", "-z"]).splitOn "\x00").filter (· ≠ "")
    result := result.push
      { name, build := ← realOrSelf (folder / ".lake" / "build" / "lib" / "lean"),
        tracked := Std.HashSet.ofList tracked }
  return result

private def relativeSource (module : Name) : String :=
  "/".intercalate (module.components.map (·.toString (escape := false))) ++ ".lean"

/-- Resolve every loaded module to its object file and origin. The result has
one origin for each module index, and the list of provenance failures. -/
private def resolveModules (env : Environment) : IO (Array ModuleOrigin × Array String) := do
  let root ← realOrSelf (← IO.currentDir)
  let projectBuild ← realOrSelf (root / ".lake" / "build" / "lib" / "lean")
  let sysroot ← findSysroot
  let toolchainLib ← realOrSelf (sysroot / "lib" / "lean")
  let toolchainSources := [sysroot / "src" / "lean", sysroot / "src" / "lean" / "lake"]
  let packages ← pinnedPackages root
  let mut entries : Array System.FilePath := #[]
  for entry in ← searchPathRef.get do
    let entry ← realOrSelf entry
    unless entries.contains entry do
      entries := entries.push entry
  let mut origins := #[]
  let mut failures := #[]
  let mut shadowed : Std.HashSet String := {}
  for module in env.allImportedModuleNames do
    let rootName := module.getRoot.toString (escape := false)
    let holders ← entries.filterM fun entry =>
      (entry / rootName).isDir <||> ((entry / rootName).addExtension "olean").pathExists
    let some entry := holders[0]?
      | failures := failures.push s!"{module}: no search path entry holds it"
        origins := origins.push .project
        continue
    if holders.size > 1 && !shadowed.contains rootName then
      shadowed := shadowed.insert rootName
      failures := failures.push s!"root {rootName} is in more than one search path entry: {holders.toList}"
    let olean := modToFilePath entry module "olean"
    let file ← realOrSelf olean
    let source := relativeSource module
    if isUnder projectBuild file then
      unless isProjectName module do
        failures := failures.push s!"{module}: non-project module in the project build folder"
      unless ← (root / source).pathExists do
        failures := failures.push s!"{module}: project object file has no project source {source}"
      origins := origins.push .project
    else if isProjectName module then
      failures := failures.push s!"{module}: project module resolves outside the project build folder: {file}"
      origins := origins.push .project
    else if isUnder toolchainLib file then
      unless ← toolchainSources.anyM fun dir => (dir / source).pathExists do
        failures := failures.push s!"{module}: toolchain object file has no toolchain source"
      origins := origins.push .toolchain
    else if let some package := packages.find? fun package => isUnder package.build file then
      unless package.tracked.contains source do
        failures := failures.push s!"{module}: source {source} is not tracked by pinned package {package.name}"
      origins := origins.push (.package package.name)
    else
      failures := failures.push s!"{module}: resolves outside the project, toolchain, and pinned packages: {file}"
      -- An unknown module is audited as a project module.
      origins := origins.push .project
  return (origins, failures)

/-! ## Declaration audit -/

private def isProjectModule (env : Environment) (origins : Array ModuleOrigin) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some moduleIdx => origins[moduleIdx.toNat]? == some .project

private def inModelOrStatements (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some moduleIdx =>
      inLibraries #["FastConfirmationModel", "FastConfirmationStatements"]
        env.allImportedModuleNames[moduleIdx.toNat]!

/-- An authored proof has its own source range and is a theorem, or a
definition, instance, or opaque constant whose type is a proposition.
Projections, recursors, and `noConfusion` are generated structure data; other
generated declarations (equation lemmas, `injEq`, `_proof_` terms) have no
source range. -/
private def isAuthoredProof (env : Environment) (name : Name) (info : ConstantInfo) :
    CommandElabM Bool := do
  if (env.getProjectionFnInfo? name).isSome || isAuxRecursor env name ||
      isNoConfusion env name then
    return false
  unless (← Lean.findDeclarationRangesCore? name).isSome do
    return false
  match info with
  | .thmInfo _ => return true
  | .defnInfo _ | .opaqueInfo _ => liftTermElabM <| isProp info.type
  | _ => return false

private def isGeneratedSafePartial (env : Environment) (origins : Array ModuleOrigin) (name : Name)
    (info : ConstantInfo) : CommandElabM Bool := do
  let some parent := Lean.Compiler.isUnsafeRecName? name
    | return false
  unless info.isPartial && !info.isUnsafe do return false
  /- Source declarations have their own range. Equation-compiler details do
  not; `findDeclarationRanges?` would incorrectly fall back to the parent. -/
  if (← Lean.findDeclarationRangesCore? name).isSome then
    return false
  match env.find? parent with
  | some parentInfo =>
      return isProjectModule env origins parent &&
        env.getModuleIdxFor? name == env.getModuleIdxFor? parent &&
        !parentInfo.isPartial && !parentInfo.isUnsafe &&
        info.type == parentInfo.type
  | none => return false

elab "audit_project_trust" : command => do
  let env ← getEnv
  unless publicWitnesses.size == 40 do
    throwError "public theorem witness set must contain exactly 40 declarations"
  unless publicWitnesses.toList.eraseDups.length == publicWitnesses.size do
    throwError "public theorem witness set contains duplicate declarations"

  let (origins, provenanceFailures) ← resolveModules env
  unless provenanceFailures.isEmpty do
    throwError "import provenance failed for {provenanceFailures.size} modules:\n\
      {"\n".intercalate (provenanceFailures.toList.take 20)}"
  let projectModules := (origins.filter (· == .project)).size
  let packageModules := (origins.filter fun origin => origin matches .package _).size

  let mut projectDeclarations := 0
  let mut projectTheorems := 0
  let mut generatedPartials := 0
  let mut modelProofs : Array Name := #[]
  for (name, info) in env.constants do
    if isProjectModule env origins name then
      projectDeclarations := projectDeclarations + 1
      if info.isUnsafe then
        throwError "project declaration is unsafe: {name}"
      if info.isPartial then
        unless ← isGeneratedSafePartial env origins name info do
          throwError "project declaration is partial: {name}"
        generatedPartials := generatedPartials + 1
      if Lean.isExtern env name then
        throwError "project declaration has an extern implementation: {name}"
      if (Lean.Compiler.getImplementedBy? env name).isSome then
        throwError "project declaration has an implemented_by override: {name}"
      if info.type.hasSorry then
        throwError "project declaration type contains sorryAx: {name}"
      match info with
      | .axiomInfo _ =>
          throwError "project declaration is an axiom/constant: {name}"
      | .opaqueInfo _ =>
          throwError "project declaration is opaque: {name}"
      | .defnInfo value =>
          if value.value.hasSorry then
            throwError "project definition body contains sorryAx: {name}"
      | .thmInfo value =>
          projectTheorems := projectTheorems + 1
          if value.value.hasSorry then
            throwError "project theorem body contains sorryAx: {name}"
      | _ => pure ()
      if inModelOrStatements env name then
        if ← isAuthoredProof env name info then
          modelProofs := modelProofs.push name
      let bad := unexpectedAxioms (← Lean.collectAxioms name)
      unless bad.isEmpty do
        throwError "project declaration {name} uses disallowed axioms: {bad.toList}"

  let allowed := allowedModelProofs.map (·.1)
  let unexpected := modelProofs.filter (!allowed.contains ·)
  unless unexpected.isEmpty do
    throwError "authored proofs in Model or Statements: \
      {(unexpected.qsort (Name.quickLt · ·)).toList}"
  for (name, _) in allowedModelProofs do
    unless modelProofs.contains name do
      throwError "allowed Model proof is absent or is no longer an authored proof: {name}"

  for name in publicWitnesses do
    match env.find? name with
    | some (.thmInfo _) =>
        let axioms ← Lean.collectAxioms name
        let bad := unexpectedAxioms axioms
        unless bad.isEmpty do
          throwError "public theorem {name} uses disallowed axioms: {bad.toList}"
    | some _ =>
        throwError "public witness exists but is not a theorem: {name}"
    | none =>
        throwError "public theorem witness is missing: {name}"

  logInfo m!"import provenance passed: {origins.size} modules \
    ({projectModules} project, {packageModules} pinned package, \
    {origins.size - projectModules - packageModules} toolchain)"
  logInfo m!"project trust audit passed: {projectDeclarations} declarations, \
    {projectTheorems} theorems, {generatedPartials} generated partials, \
    {modelProofs.size} allowed Model proof, {publicWitnesses.size} public witnesses"

audit_project_trust
