/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import AglibTest.AuditSupport
import AglibTest.NegativeControls.ImportedFixture
import Lean.Elab.GuardMsgs

/-! The auditor must reject the custom axiom by its defining module, regardless of namespace. -/

/-- depends on unsupported assumption UnrelatedNegativeNamespace.importedBad -/
#guard_msgs (error, substring := true) in
run_cmd do
  let count ← AglibAudit.auditModules
    #[`AglibTest.NegativeControls.ImportedFixture]
  unless count > 0 do
    throwError "Imported negative control selected no declarations"
