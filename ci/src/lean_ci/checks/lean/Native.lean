import Batteries.Tactic.Lint
import Lean.Util.CollectAxioms
import Lean.Data.Json.Parser

open Lean Core Batteries.Tactic.Lint

namespace LeanCiNative

/-- Fixed declaration predicate, deliberately independent of batch membership. -/
def importsFor (origin : Name) : Array Import :=
  #[{module := `Batteries.Tactic.Lint}, {module := origin}]

def originDecls (env : Environment) (origin : Name) : Array Name :=
  env.constants.map₁.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some index => if env.header.moduleNames[index.toNat]! == origin then names.push name else names
    | none => names

def lint (origin : Name) (nolints : Array (Name × Name)) : CoreM Json := do
  let decls := originDecls (← getEnv) origin
  let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
  let results ← lintCore decls linters (inIO := true) (currentModule := origin)
  let results := results.map fun (linter, decls) =>
    (linter, nolints.foldl (init := decls) fun decls (linter', decl') =>
      if linter.name == linter' then decls.erase decl' else decls)
  let mut diagnostics := #[]
  for (linter, messages) in results do
    for (name, message) in messages.toArray.qsort (fun a b => a.1.lt b.1) do
      diagnostics := diagnostics.push <| Json.mkObj [
        ("linter", toJson linter.name.toString), ("declaration", toJson name.toString),
        ("message", toJson (← message.toString))]
  let failed := results.any (!·.2.isEmpty)
  let formatted ← if failed then
    (← formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
      s!"in {origin}" (runSlowLinters := true) .medium linters.size).toString
    else pure ""
  return Json.mkObj [("success", toJson (!failed)),
    ("inventory", toJson ((decls.qsort Name.lt).map Name.toString)),
    ("checks", toJson (linters.map (·.name.toString))),
    ("diagnostics", toJson diagnostics), ("formatted", toJson formatted)]

def audit (origin : Name) (checkAxioms : Bool) : CoreM Json := do
  let env ← getEnv
  let decls := (originDecls env origin).qsort Name.lt
  let mut diagnostics : Array Json := #[]
  for name in decls do
    unless (env.checked.get.find? name).isSome do
      diagnostics := diagnostics.push <| toJson s!"{name}: missing checked declaration"
    if checkAxioms then
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          diagnostics := diagnostics.push <| toJson s!"{name}: unsupported assumption {dependency}"
  return Json.mkObj [("success", toJson diagnostics.isEmpty),
    ("inventory", toJson (decls.map Name.toString)), ("diagnostics", toJson diagnostics)]

def decode (text : String) : Except String (Array Name) := do
  let values ← (← Json.parse text).getArr?
  if values.isEmpty then throw "Empty module selection"
  values.mapM fun value => do
    let components ← value.getArr?
    if components.isEmpty then throw "Empty module components"
    let mut name := Name.anonymous
    for component in components do
      let c ← component.getStr?
      if c.isEmpty || c == "." || c == ".." || c.toList.any (fun x =>
          x == '/' || x == '\\' || x.toNat < 32 || (127 ≤ x.toNat && x.toNat ≤ 159)) then
        throw "Invalid module component"
      name := Name.str name c
    return name

/-- One finite process owns all referenced compacted regions until process exit.
No explicit region freeing is safe while the persistent prefix is live. -/
unsafe def run (kind : String) (origins : Array Name) (pilot : Bool) (nolints : Array (Name × Name)) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let lintMode := kind == "declarations" || kind == "reference"
  -- Audit trust stays at the frontend default zero, never the lint trust 1024.
  let trust : UInt32 := if lintMode then 1024 else 0
  let runtimeImports : Array Import := if lintMode then #[{module := `Batteries.Tactic.Lint}] else #[{module := `Init}]
  let started ← IO.monoMsNow
  let (_, base) ← withImporting <| (importModulesCore (globalLevel := .private) runtimeImports).run
  let prepared ← IO.monoMsNow
  let prefixEnv ← if pilot then
    some <$> withImporting (do
      enableInitializersExecution
      finalizeImport base runtimeImports {} trust false true (level := .private))
    else pure none
  let mut failed := false
  for origin in origins do
    let before ← IO.monoMsNow
    try
      let imports := if lintMode then importsFor origin else #[{module := `Init}, {module := origin}]
      let env ← if kind == "reference" then
        do
          enableInitializersExecution
          importModules imports {} trust (loadExts := true) (level := .private)
        else withImporting do
          enableInitializersExecution
          let (_, isolated) ← (importModulesCore (globalLevel := .private) imports).run base
          finalizeImport isolated imports {} trust false true (level := .private)
      let imported ← IO.monoMsNow
      let action := if lintMode then lint origin nolints else audit origin (kind == "axioms")
      let (result, _) ← CoreM.toIO action {fileName := "", fileMap := default, options := {}} {env}
      let finished ← IO.monoMsNow
      let shared := match prefixEnv with
        | none => 0
        | some pre => pre.header.moduleNames.foldl (init := 0) fun count name =>
          match pre.header.moduleNames.findIdx? (· == name), env.header.moduleNames.findIdx? (· == name) with
          | some a, some b => if ptrEq pre.header.moduleData[a]! env.header.moduleData[b]! then count + 1 else count
          | _, _ => count
      let success := (result.getObjValAs? Bool "success").toOption.getD false
      failed := failed || !success
      let output := Json.mkObj [("kind", toJson (if kind == "reference" then "declarations" else kind)),
        ("module", toJson origin.toString), ("success", toJson success), ("result", result),
        ("import_ms", toJson (imported - before)), ("check_ms", toJson (finished - imported)),
        ("prefix_preparations", toJson (1 : Nat)), ("prefix_ms", toJson (prepared - started)),
        ("shared_prefix_modules", toJson shared),
        ("prefix_modules", toJson (prefixEnv.map (·.header.moduleNames.size) |>.getD 0)),
        ("environment_modules", toJson (if pilot then env.header.moduleNames.map Name.toString else #[]))]
      IO.println output.compress
      (← IO.getStdout).flush
    catch error =>
      failed := true
      IO.println <| (Json.mkObj [("kind", toJson kind), ("module", toJson origin.toString),
        ("success", toJson false), ("error", toJson error.toString)]).compress
      (← IO.getStdout).flush
  return if failed then 1 else 0

end LeanCiNative

unsafe def main (args : List String) : IO UInt32 := do
  try
    let (kind, selection, pilot, nolintsText) ← match args with
      | [kind, selection, pilot, nolints] => pure (kind, selection, pilot, nolints)
      | [kind, selection, pilot] => pure (kind, selection, pilot, "[]")
      | _ => throw <| IO.userError "Expected kind, selection JSON, pilot flag, nolints JSON"
    unless ["declarations", "reference", "inventory", "axioms"].contains kind do
      throw <| IO.userError "Unknown native kind"
    LeanCiNative.run kind (← IO.ofExcept <| LeanCiNative.decode selection) (pilot == "true")
      (← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse nolintsText))
  catch error =>
    IO.eprintln s!"Native check failed: {error}"
    return 1
