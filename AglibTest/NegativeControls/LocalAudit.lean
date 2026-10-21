/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import AglibTest.AuditSupport
import Lean.Elab.GuardMsgs

/-! The auditor must reject a current-module stage-2 axiom with an unrelated root name. -/

axiom localBad : False
private theorem privateLocalBad : False := localBad

/-- depends on unsupported assumption localBad -/
#guard_msgs (error, substring := true) in
open Lean in
run_cmd do
  let _ ← AglibAudit.auditModules #[(← getEnv).header.mainModule]
