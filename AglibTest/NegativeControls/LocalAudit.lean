import AglibTest.AuditSupport

/-! Must fail on a current-module stage-2 axiom with an unrelated root name. -/

axiom localBad : False
private theorem privateLocalBad : False := localBad

open Lean in
run_cmd do
  let _ ← AglibAudit.auditModules #[(← getEnv).header.mainModule]
