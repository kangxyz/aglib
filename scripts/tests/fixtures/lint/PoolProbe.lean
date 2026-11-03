import BatchedLint

open Lean Core Meta Batteries.Tactic.Lint

def probeLinter (name : Name) (test : Name → MetaM (Option MessageData)) : NamedLinter :=
  {name, declName := name, test, noErrorsFound := m!"ok", errorsFound := m!"failed"}

unsafe def poolProbe : IO Unit := do
  enableInitializersExecution
  let env ← importModules #[`Batteries.Tactic.Lint] {} (trustLevel := 1024) (loadExts := true)
  if (← IO.getEnv "AGLIB_LINT_MATHLIB_SOURCES").isSome then
    for name in #[`Batteries.Tactic.Lint.structureInType,
        `Batteries.Tactic.Lint.deprecatedNoSince,
        `Mathlib.Linter.Style.nameCheck.defsWithUnderscore,
        `Mathlib.Meta.SetNotationForOrder.subsetDotNotationLinter, `tacticAlt, `tacticDocs] do
      unless ← BatchedLint.knownLinter (probeLinter name (fun _ => pure none)) do
        throw <| IO.userError s!"accepted provider was not recognized: {name}"
  let names ← IO.mkRef (#[] : Array Name)
  let isolated := probeLinter `isolated fun _ => do
    if (← getEnv).mainModule == `Leaked then return some m!"Core state leaked"
    unless (← getMCtx).decls.isEmpty do return some m!"Meta state leaked"
    modifyEnv (·.setMainModule `Leaked)
    let mvar ← mkFreshExprMVar (mkConst ``Nat)
    let fresh := mvar.mvarId!.name
    let duplicate ← names.modifyGet fun names => (names.contains fresh, names.push fresh)
    if duplicate then return some m!"name generator collision"
    IO.addHeartbeats 1000
    Core.checkSystem "pool-probe"
    return none
  let ctx : Core.Context := {fileName := "probe", fileMap := default, maxHeartbeats := 50000}
  let (results, _) ← CoreM.toIO (ctx := ctx) (s := {env}) do
    BatchedLint.lintCoreBatched (.replicate 256 `Nat) #[isolated, isolated] 4
  unless results.all (·.2.isEmpty) do
    for (_, messages) in results do
      for (_, message) in messages.toArray do IO.eprintln (← message.toString)
    throw <| IO.userError "isolation/heartbeat probe failed"
  unless (← names.get).size == 512 do throw <| IO.userError "not every check executed"
  let excessive := probeLinter `excessive fun _ => do
    IO.addHeartbeats 100000
    Core.checkSystem "pool-probe"
    return none
  let (overBudget, _) ← CoreM.toIO (ctx := ctx) (s := {env}) do
    BatchedLint.lintCoreBatched #[`Nat] #[excessive] 1
  unless overBudget.any (!·.2.isEmpty) do throw <| IO.userError "over-budget check did not fail"
  let throwing := probeLinter `throwing fun _ => throwError "forced-check-exception"
  let (exceptions, _) ← CoreM.toIO (ctx := ctx) (s := {env}) do
    BatchedLint.lintCoreBatched #[`Nat] #[throwing] 1
  unless exceptions.any (!·.2.isEmpty) do throw <| IO.userError "check exception did not fail"
  let token ← IO.CancelToken.new
  token.set
  let cancelled ← ((BatchedLint.lintCoreBatched #[`Nat] #[isolated] 1).run
    {ctx with cancelTk? := some token} {env}).toBaseIO
  match cancelled with
  | .error error => unless error.isInterrupt do throw <| IO.userError "interrupt was converted"
  | .ok _ => throw <| IO.userError "cancelled batch returned success"
  let interrupting := probeLinter `interrupting fun _ => throwInterruptException
  let insideInterrupt ← ((BatchedLint.lintCoreBatched #[`Nat] #[interrupting] 1).run
    ctx {env}).toBaseIO
  match insideInterrupt with
  | .error error => unless error.isInterrupt do throw <| IO.userError "check interrupt was converted"
  | .ok _ => throw <| IO.userError "check interrupt became a suppressible result"
  let distinct := (Array.range 257).map (Name.num `probe)
  let calls ← IO.mkRef ({} : Std.HashMap (Name × Name) Nat)
  let indexed (rule : Name) (divisor : Nat) := probeLinter rule fun decl => do
    calls.modify fun counts => counts.insert (rule, decl) (counts[(rule, decl)]?.getD 0 + 1)
    let .num _ index := decl | return some m!"unexpected probe name"
    return if index % divisor == 0 then some m!"expected failure" else none
  let (coverage, _) ← CoreM.toIO (ctx := ctx) (s := {env}) do
    BatchedLint.lintCoreBatched distinct #[indexed `first 3, indexed `second 5] 2
  unless coverage.size == 2 do throw <| IO.userError "missing linter result"
  for ((_, messages), ruleIndex) in coverage.zipIdx do
    let divisor := if ruleIndex == 0 then 3 else 5
    let expected := (Array.range 257).filter (· % divisor == 0) |>.map (Name.num `probe)
    unless messages.size == expected.size && expected.all messages.contains do
      throw <| IO.userError "per-linter failure map mismatch"
  let counts ← calls.get
  unless counts.size == 514 && counts.toArray.all (·.2 == 1) do
    throw <| IO.userError "batch coverage dropped or duplicated a check"
  let fatal ← ((BatchedLint.mapOnWorkers #[0] 1 fun _ =>
    throwError "forced-worker-exception" : CoreM (Array Unit)).run ctx {env}).toBaseIO
  match fatal with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "worker exception returned success"
  IO.println "pool-probe: isolation, fresh names, per-check budgets, exceptions, inside-check interrupt, 257x2 exact coverage passed"

#eval poolProbe
