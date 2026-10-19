import AglibTest.AuditSupport
import AglibTest.AuditCoverage
import Lean.Data.Json.Parser

/-! Fixed selected-origin audit driver. Selection is one JSON argument containing
arrays of module-name components, never Lean source. The fresh target environment below has the
same legacy header as the former generated SelectedAudit program; this driver's
own helper declarations and extra API imports are excluded from that target. -/

open Lean Elab Command

namespace SelectedOriginAudit

/- Reflect only frontend configuration, before any runtime selection is read.
No selection text is parsed as Lean syntax or compiled into declarations. -/
run_cmd do
  let mut encodedOptions := mkConst ``Options.empty
  for (key, value) in (← getOptions) do
    let encoded ← match value with
      | .ofString value => pure <| mkApp (mkConst ``DataValue.ofString) (toExpr value)
      | .ofBool value => pure <| mkApp (mkConst ``DataValue.ofBool) (toExpr value)
      | .ofName value => pure <| mkApp (mkConst ``DataValue.ofName) (toExpr value)
      | .ofNat value => pure <| mkApp (mkConst ``DataValue.ofNat) (toExpr value)
      | .ofInt value => pure <| mkApp (mkConst ``DataValue.ofInt) (toExpr value)
      | .ofSyntax _ => throwError "Syntax-valued frontend options are unsupported by this driver"
    encodedOptions := mkApp3 (mkConst ``Options.insert) encodedOptions (toExpr key) encoded
  liftCoreM <| addAndCompile <| .defnDecl {
    name := `SelectedOriginAudit.frontendOptions
    levelParams := []
    type := mkConst ``Options
    value := encodedOptions
    hints := .opaque
    safety := .safe
  }
  liftCoreM <| addAndCompile <| .defnDecl {
    name := `SelectedOriginAudit.frontendTrustLevel
    levelParams := []
    type := mkConst ``UInt32
    value := toExpr (← getEnv).header.trustLevel
    hints := .opaque
    safety := .safe
  }

/-- Reject filesystem separators and Unicode C0/C1 controls in components. -/
def forbiddenComponentChar (character : Char) : Bool :=
  character == '/' || character == '\\' || character.toNat < 32 ||
    (127 ≤ character.toNat && character.toNat ≤ 159)

/-- Structured names preserve dots/spaces inside quoted identifier components.
The producer validates Lean identifier syntax; this consumer never parses code. -/
def decodeSelection (text : String) : Except String (Array Name) := do
  let selection ← (← Json.parse text).getArr?
  if selection.isEmpty then throw "Module selection must be nonempty"
  selection.mapM fun value => do
    let components ← value.getArr?
    if components.isEmpty then throw "Module component array must be nonempty"
    let mut name := Name.anonymous
    for component in components do
      let component ← component.getStr?
      if component.isEmpty then throw "Module-name components must be nonempty"
      if component == "." || component == ".." || component.toList.any forbiddenComponentChar then
        throw "Module-name component contains a path separator, path alias, or control character"
      name := Name.str name component
    return name

/-- Exact legacy import order, including the frontend's implicit Init imports. -/
def targetImports (selected : Array Name) : Array Import := Id.run do
  let mut imports : Array Import := #[{ module := `Init }, { module := `Init, isMeta := true },
    { module := `AglibTest.AuditSupport }, { module := `AglibTest.AuditCoverage }]
  for name in selected do
    unless name == `AglibTest.AuditSupport || name == `AglibTest.AuditCoverage do
      imports := imports.push { module := name }
  return imports

/-- These audit predicates are copied unchanged from Axioms.lean's control block. -/
def audit (selected : Array Name) : CommandElabM Unit := do
  let count ← AglibAudit.auditModules selected
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
  logInfo m!"Selected-origin axiom audit: {count} declarations; private/generated origin control: {coverageCount}."

unsafe def run (selected : Array Name) : IO UInt32 := do
  let options := frontendOptions
  let trustLevel := frontendTrustLevel
  -- The normal frontend also enables initializers before loading extensions.
  -- Preserve its actual options/trust instead of API defaults or a guessed level.
  enableInitializersExecution
  let env ← importModules (loadExts := true) (level := .private)
    (targetImports selected) options trustLevel
  let env := env.setMainModule `SelectedAudit
  let context : Command.Context := {
    fileName := "<selected-origin-audit>"
    fileMap := FileMap.ofString ""
    snap? := none
    cancelTk? := none
  }
  match ← EIO.toIO' ((audit selected context).run (Command.mkState env {} options)) with
  | .error error =>
    IO.eprintln (← error.toMessageData.toString)
    return 1
  | .ok (_, state) =>
    for message in state.messages.reportedPlusUnreported.toList do
      IO.println (← message.toString)
    return if state.messages.hasErrors then 1 else 0

end SelectedOriginAudit

unsafe def main (args : List String) : IO UInt32 := do
  try
    let [selectionJson] := args
      | throw <| IO.userError "Usage: SelectedAudit.lean <JSON array of nonempty module-component arrays>"
    let selected ← IO.ofExcept <| SelectedOriginAudit.decodeSelection selectionJson
    SelectedOriginAudit.run selected
  catch error =>
    IO.eprintln s!"Selected-origin audit failed: {error}"
    return 1
