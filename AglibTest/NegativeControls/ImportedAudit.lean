import AglibTest.AuditSupport
import AglibTest.NegativeControls.ImportedFixture

/-! Must fail on the custom axiom by its defining module, regardless of namespace. -/

run_cmd do
  let count ← AglibAudit.auditModules
    #[`AglibTest.NegativeControls.ImportedFixture]
  unless count > 0 do
    throwError "Imported negative control selected no declarations"
