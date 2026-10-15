/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib
import AglibTest.AuditSupport
import AglibTest.AuditCoverage

/-! Explicit legacy audit replay, separate from positive fixtures. This checks
all production defining-module origins and occupied-source compiled enrollment.
It does not discharge explicit mathematical premises of the imported theorems. -/

open Lean in
run_cmd do
  let modules ← AglibAudit.auditEnrollment
  let count ← AglibAudit.auditModules #[`Aglib]
  if count == 0 then throwError "Production audit selected no declarations"
  let env ← getEnv
  let coverage := AglibAudit.declarationsFromModules env
    #[`AglibTest.AuditCoverage]
  unless coverage.contains `AuditForeign.rootDatum &&
      coverage.contains `AuditForeign.GeneratedDatum.rec do
    throwError "Origin inventory omitted root-namespace or generated coverage declarations"
  let hidden := coverage.toArray.filter fun name =>
    match name with
    | .str _ "hiddenDatum" => (`_private).isPrefixOf name
    | _ => false
  unless hidden.size == 1 do
    throwError "Origin inventory omitted the actual private hiddenDatum declaration"
  unless (env.checked.get.find? hidden[0]!).isSome do
    throwError "The selected private coverage constant is absent from the checked environment"
  let coverageCount ← AglibAudit.auditModules #[`AglibTest.AuditCoverage]
  logInfo m!"Audited {count} production declarations from {modules} occupied modules; \
    private/generated origin control: {coverageCount} declarations; allowed: \
    propext, Classical.choice, Quot.sound."
