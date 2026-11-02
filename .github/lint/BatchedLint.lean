/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic

/-!
CI-only full declaration lint with bounded scheduling.
Backports Batteries PR #2026 (41c46f8a9586f75b6ea12296c05e932cc2707d51),
Batteries/Tactic/Lint/Frontend.lean, and PR #2028
(30691c775364967184547c94468bf6b5f25400fb), scripts/runLinter.lean.
The pinned f2effa runner's roots, imports, checks, options and suppressions are retained.
Every invocation runs all selected checks; there is no result cache or module selection.
-/

open Lean Core Batteries.Tactic.Lint System

namespace BatchedLint

def log (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

def batchSize : Nat := 64

/-- Fixed dedicated workers; only failed checks are retained. Worker state is discarded. -/
def mapOnWorkers (jobs : Array α) (numWorkers : Nat) (f : α → CoreM β) :
    CoreM (Array β) := do
  let next ← IO.mkRef 0
  let cancelTk? := (← read).cancelTk?
  let numWorkers := min (max numWorkers 1) jobs.size
  let tasks ← (Array.range numWorkers).mapM fun _ => do
    EIO.asTask (prio := .dedicated) <|
      (← Core.wrapAsync (cancelTk? := cancelTk?) fun _ => do
        let mut done := #[]
        repeat
          Core.checkInterrupted
          let i ← next.modifyGet fun i => (i, i + 1)
          let some job := jobs[i]? | break
          done := done.push (← f job)
        return done) ()
  tasks.flatMapM (MonadExcept.ofExcept ·.get)

/-- Each check gets fresh Core/Meta state, a child name generator and its own heartbeat budget. -/
def lintDecl (linter : NamedLinter) (decl : Name) (inIO : Bool) :
    CoreM (Option MessageData) := do
  let act : MetaM (Option MessageData) := do
    let result ← linter.test decl
    if inIO then
      printTraces
      (← IO.getStdout).flush
    return result
  let run ← Core.withCurrHeartbeats <|
    Core.wrapAsync (fun _ => act.run' Lean.Elab.Command.mkMetaContext) (← read).cancelTk?
  match ← (run ()).toBaseIO with
  | .ok msg? => return msg?
  | .error err =>
      if err.isInterrupt then throw err
      return some m!"LINTER FAILED:\n{err.toMessageData}"

/-- Run the full declaration × linter predicate using upstream's batches of 64. -/
def lintCoreBatched (decls : Array Name) (linters : Array NamedLinter)
    (numWorkers : Nat) (currentModule : Option Name := none) (inIO := false) :
    CoreM (Array (NamedLinter × Std.HashMap Name MessageData)) := do
  traceLint s!"Running linters:\n  {"\n  ".intercalate <| linters.map (s!"{·.name}") |>.toList}"
    inIO currentModule
  if inIO then (← IO.getStdout).flush
  let indexed := linters.zipIdx
  let batches := if linters.isEmpty then #[] else
    (Array.range ((decls.size + batchSize - 1) / batchSize)).map fun i =>
      decls.extract (i * batchSize) ((i + 1) * batchSize)
  let actualWorkers := min (max numWorkers 1) batches.size
  if inIO then
    log s!"[{currentModule.getD .anonymous}] full lint: backend=batched; {decls.size} declarations, {linters.size} linters, {actualWorkers} workers, batch={batchSize}"
  let progress ← IO.mkRef (0, 0, 0)
  let step := max 1 ((batches.size + 9) / 10)
  let start ← IO.monoMsNow
  let failures ← mapOnWorkers batches actualWorkers fun batch => do
    let mut failures := #[]
    for decl in batch do
      Core.checkInterrupted
      let ignored := (nolintAttr.getParam? (← getEnv) decl).getD #[]
      for (linter, i) in indexed do
        unless ignored.contains linter.name do
          if let some msg ← lintDecl linter decl inIO then
            failures := failures.push (i, decl, msg)
    if inIO then
      let (n, done, msgs) ← progress.modifyGet fun (n, done, msgs) =>
        let p := (n + 1, done + batch.size, msgs + failures.size); (p, p)
      if n % step == 0 || n == batches.size then
        log s!"[{currentModule.getD .anonymous}] Linted {done}/{decls.size} declarations, {msgs} messages, {(← IO.monoMsNow) - start} ms"
    return failures
  let mut messages : Array (Std.HashMap Name MessageData) := .replicate linters.size {}
  for (i, decl, msg) in failures.flatten do
    messages := messages.modify i (·.insert decl msg)
  let result ← (linters.zip messages).mapM fun (linter, msgs) => do
    traceLint s!"{if msgs.isEmpty then "Passed!" else
      s!"Failed with {msgs.size} messages (before nolints.json)."}"
      inIO currentModule linter.name
    if inIO then (← IO.getStdout).flush
    pure (linter, msgs)
  traceLint "Completed linting!" inIO currentModule
  if inIO then (← IO.getStdout).flush
  return result

/-- Unknown implementations retain the old full API, including arbitrary custom linters. -/
def knownLinter (linter : NamedLinter) : IO Bool := do
  let batteries := #[`checkType, `docBlame, `impossibleInstance, `nonClassInstance,
    `simpComm, `simpNF, `synTaut, `unusedArguments, `unusedHavesSuffices].map
      (`Batteries.Tactic.Lint ++ ·)
  if batteries.contains linter.declName then return true
  let providers : Array (Name × UInt64 × Array Name) := #[
    (`Mathlib.Tactic.Linter.Lint, 0x0bcaafd617652033,
      #[`Batteries.Tactic.Lint.structureInType, `Batteries.Tactic.Lint.deprecatedNoSince]),
    (`Mathlib.Tactic.Linter.Style, 0x82ea161b15e4d33e,
      #[`Mathlib.Linter.Style.nameCheck.defsWithUnderscore]),
    (`Mathlib.Tactic.Linter.TacticDocumentation, 0xfd332c6970f219e1, #[`tacticAlt, `tacticDocs]),
    (`Mathlib.Tactic.SetNotationForOrder, 0xe49bd5b6e9ec760e,
      #[`Mathlib.Meta.SetNotationForOrder.subsetDotNotationLinter])]
  for (name, expected, decls) in providers do
    if decls.contains linter.declName then
      let some source ← (← getSrcSearchPath).findWithExt "lean" name | return false
      let .ok contents ← (IO.FS.readFile source).toBaseIO | return false
      -- Same normalized String hash as the accepted Lake source fingerprints.
      return mixHash 1723 (hash contents.crlfToLf) == expected
  return false

unsafe def lintRoot (root : Name) (workers : Nat) (leakEnv : Bool) :
    IO UInt32 := do
  let start ← IO.monoMsNow
  log s!"[{root}] importing full lint environment (persistent={leakEnv})"
  let nolintsPath : FilePath := "scripts/nolints.json"
  let nolints : Array (Name × Name) ← if ← nolintsPath.pathExists then
    IO.ofExcept <| Json.parse (← IO.FS.readFile nolintsPath) >>= fromJson?
  else pure #[]
  unsafe enableInitializersExecution
  let env ← importModules #[root, `Batteries.Tactic.Lint] {}
    (trustLevel := 1024) (loadExts := true) (leakEnv := leakEnv)
  log s!"[{root}] import elapsed={(← IO.monoMsNow) - start} ms"
  let ctx : Core.Context := {
    fileName := ""
    fileMap := default
    options := ({} : Options).setBool `trace.Batteries.Lint true
  }
  let lintStart ← IO.monoMsNow
  let (failed, _) ← CoreM.toIO (ctx := ctx) (s := {env}) do
    let decls ← getDeclsInPackage root.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let known ← linters.allM (fun l => do return ← knownLinter l)
    let results ← if known then
      lintCoreBatched decls linters workers (some root) true
    else
      log s!"[{root}] custom/unrecognized linter: using original full lintCore"
      lintCore decls linters (inIO := true) (currentModule := root)
    (← IO.getStdout).flush
    let mut tally : Std.HashMap Name Nat := {}
    for (linter, _) in nolints do
      tally := tally.alter linter fun | none => some 1 | some n => some (n + 1)
    let msgs := tally.toList.map fun (linter, n) => s!"{linter}: {n}"
    log s!"[{root}] {nolintsPath} summary (number of nolints per linter):\n  {"\n  ".intercalate msgs}"
    let results := results.map fun (linter, decls) =>
      (linter, nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls)
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmt ← formatLinterResults results decls (groupByFilename := true)
        (useErrorFormat := true) s!"in {root}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmt.toString)
    return failed
  log s!"[{root}] lint elapsed={(← IO.monoMsNow) - lintStart} ms; total={(← IO.monoMsNow) - start} ms"
  if failed then return 1
  log s!"-- Linting passed for {root}."
  return 0

unsafe def run (args : Array String) : IO UInt32 := do
  let mut modules : Array Name := #[]
  let mut noBuild := false
  for arg in args do
    if arg == "--no-build" then
      noBuild := true
    else if arg == "--trace" || arg == "-v" then
      pure ()
    else if arg.startsWith "-" || arg.isEmpty then
      throw <| IO.userError s!"unsupported driver argument: {arg}"
    else
      modules := modules.push arg.toName
  unless noBuild && !modules.isEmpty do
    throw <| IO.userError "expected --no-build and explicit configured driver roots"
  initSearchPath (← findSysroot)
  let workers := ((← IO.getEnv "CI_LINT_WORKERS").bind String.toNat?).getD 2
    |>.max 1 |>.min ((Platform.Internal.getHardwareConcurrency ()).toNat.max 1)
  for root in modules do
    for name in #[root, `Batteries.Tactic.Lint] do
      let olean ← findOLean name
      unless ← olean.pathExists do
        throw <| IO.userError s!"missing olean: {olean}"
    let code ← lintRoot root workers (modules.size == 1)
    if code != 0 then return code
  return 0

end BatchedLint

unsafe def main (args : List String) : IO Unit := do
  let code ← match args with
    | [serialized] => do
      let driverArgs : Array String ← IO.ofExcept <| Json.parse serialized >>= fromJson?
      BatchedLint.run driverArgs
    | _ => throw <| IO.userError "expected configured driver arguments as JSON"
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit code.toUInt8
