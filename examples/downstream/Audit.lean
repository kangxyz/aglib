/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Consumer
import Lean.Util.CollectAxioms

/-! Independent downstream package origin audit. Legacy imports preserve hidden
implementation declarations; this client imports no tests or original library. -/

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then throwError "Downstream origin audit requires legacy imports"
  let selected (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some i => (`Consumer).isPrefixOf env.header.moduleNames[i.toNat]! ||
        (`Aglib).isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if (`Consumer).isPrefixOf env.header.moduleNames[i]! ||
        (`Aglib).isPrefixOf env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        if selected name then names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Selected downstream declaration {name} is absent from checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  if names.isEmpty then throwError "Downstream audit selected no declarations"
  logInfo m!"Downstream audited {names.size} client/foundation declarations by module origin."
