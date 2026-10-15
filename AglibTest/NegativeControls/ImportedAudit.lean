/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import AglibTest.AuditSupport
import AglibTest.NegativeControls.ImportedFixture

/-! Must fail on the custom axiom by its defining module, regardless of namespace. -/

run_cmd do
  let count ← AglibAudit.auditModules
    #[`AglibTest.NegativeControls.ImportedFixture]
  unless count > 0 do
    throwError "Imported negative control selected no declarations"
