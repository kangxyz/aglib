/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Mechanical audit support. This deliberately uses legacy imports to preserve
private and generated declarations from every imported module. Origin selection
uses defining module identities, independently of declaration namespaces.
Adapted from R5Lab Checks.Basic and QuillenTest.Axioms on the fixed migration basis. -/

open Lean Elab Command

namespace AglibAudit

/-- The fixed logical foundation policy. -/
def allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

/-- Imported module origin, or the current module for locally elaborated declarations. -/
def definingModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.header.mainModule

/-- Collect imported inventories and current stage-2 declarations, including private names. -/
def declarationsFromModules (env : Environment) (prefixes : Array Name) : NameSet := Id.run do
  let selected (name : Name) := prefixes.any (·.isPrefixOf (definingModule env name))
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if prefixes.any (·.isPrefixOf env.header.moduleNames[i]!) then
      for name in env.header.moduleData[i]!.constNames do
        if selected name then names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  return names

/-- Audit the actual selected kernel declarations rather than exported public names. -/
def auditModules (prefixes : Array Name) : CommandElabM Nat := do
  let env ← getEnv
  if env.header.isModule then
    throwError "Exhaustive axiom audit requires legacy (.private) transitive imports"
  let names := declarationsFromModules env prefixes
  let mut count := 0
  for name in names.toArray.qsort Name.lt do
    unless (env.checked.get.find? name).isSome do
      throwError "Selected audit declaration {name} is missing from the checked kernel environment"
    count := count + 1
    for dependency in ← collectAxioms name do
      unless allowedAxioms.contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  return count

/-- Discover only occupied production source; no registry or topic placeholders. -/
partial def sourceModules (dir : System.FilePath) : IO (Array Name) := do
  let mut names := #[]
  if !(← dir.isDir) then return names
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      names := names ++ (← sourceModules entry.path)
    else if entry.path.toString.endsWith ".lean" then
      let text := entry.path.toString.dropEnd 5 |>.toString
      names := names.push ((text.splitOn "/").foldl Name.str Name.anonymous)
  return names.qsort Name.lt

/-- Actual direct imports, including current-module import headers. -/
def moduleImports (env : Environment) (name : Name) : CommandElabM (Array Import) := do
  if name == env.header.mainModule then return env.header.imports
  let some index := env.header.moduleNames.findIdx? (· == name)
    | throwError "Missing compiled import header for {name}"
  return env.header.moduleData[index]!.imports

/-- Exact transitive reachability from one entry, not the auditor's combined imports. -/
def entryModules (env : Environment) (entry : Name) : CommandElabM (Array Name) := do
  let mut pending := #[entry]
  let mut visited := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.push name
    for imported in ← moduleImports env name do
      pending := pending.push imported.module
  return visited

/-- Every occupied source must occur in the production root's compiled closure. -/
def auditEnrollment (sourceDir : System.FilePath := "Aglib") : CommandElabM Nat := do
  let env ← getEnv
  let closure ← entryModules env `Aglib
  let modules ← sourceModules sourceDir
  for name in modules do
    unless closure.contains name do
      throwError "Source enrollment: {name} is absent from Aglib's compiled closure"
  for name in closure do
    if (`R5Lab).isPrefixOf name || (`Quillen).isPrefixOf name ||
        (`Essays).isPrefixOf name || (`AglibTest).isPrefixOf name then
      throwError "Forbidden production closure module {name}"
  for name in closure do
    if (`Aglib).isPrefixOf name then
      for imported in ← moduleImports env name do
        unless (`Aglib).isPrefixOf imported.module ||
            (`Mathlib).isPrefixOf imported.module || imported.module == `Init do
          throwError "Forbidden compiled production import {name} -> {imported.module}"
  return modules.size

end AglibAudit
