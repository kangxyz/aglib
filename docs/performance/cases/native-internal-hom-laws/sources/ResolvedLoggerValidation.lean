import Lean

example (x y z : Nat) (h : x = y) (k : z = y) : x = z := by
  let R := Nat
  have hAction := congrArg (fun a : Nat => a) h
  have hNative := congrArg (fun a : Nat => a) k
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut action : Option Lean.Expr := none
    let mut native : Option Lean.Expr := none
    let mut ring : Option (Lean.Expr × Lean.Expr) := none
    for decl in ← Lean.getLCtx do
      let name := decl.userName.eraseMacroScopes.toString
      if name == "hAction" || name == "hNative" then
        let actualType ← Lean.instantiateMVars decl.type
        let actualType ← Lean.Meta.whnf actualType
        let args := actualType.getAppArgs
        unless args.size == 3 do
          throwError "W4 diagnostic: equality does not have three arguments"
        Lean.logInfo m!"W4.actual.{name}: typeHead={actualType.getAppFn}, lhsHead={args[1]!.getAppFn}"
        if name == "hAction" then action := some args[1]!
        else native := some args[1]!
      if name == "R" then
        if let some value := decl.value? then
          let value ← Lean.instantiateMVars value
          ring := some (decl.toExpr, value)
    let some actionValue := action | throwError "W4 diagnostic: hAction missing"
    let some nativeValue := native | throwError "W4 diagnostic: hNative missing"
    let mut cases := [("raw", actionValue, nativeValue)]
    if let some (ringExpr, value) := ring then
      let normalize := fun e : Lean.Expr => e.replace fun part =>
        if part == ringExpr then some value else none
      cases := cases ++ [("ring", normalize actionValue, normalize nativeValue)]
    for (label, left, right) in cases do
      Lean.logInfo m!"W4.middle.{label}Same={left == right}"
      let mut pending := [("middle", left, right)]
      let mut difference : Option (String × Lean.Expr × Lean.Expr) := none
      for _ in [:4096] do
        if difference.isSome then break
        match pending with
        | [] => break
        | (path, a, b) :: rest =>
          pending := rest
          unless a == b do
            match a, b with
            | .mdata _ inner, _ => pending := (path ++ ".metaL", inner, b) :: pending
            | _, .mdata _ inner => pending := (path ++ ".metaR", a, inner) :: pending
            | .app af aa, .app bf ba =>
              pending := (path ++ ".fn", af, bf) :: (path ++ ".arg", aa, ba) :: pending
            | _, _ => difference := some (path, a, b)
      if let some (path, a, b) := difference then
        Lean.logInfo m!"W4.middle.{label}Path={path}"
        Lean.logInfo m!"W4.middle.{label}Left={reprStr a}"
        Lean.logInfo m!"W4.middle.{label}Right={reprStr b}"
      else unless pending.isEmpty do
        Lean.logError m!"W4 structural diagnostic reached its4096-node reporting bound"
  exact hAction.trans hNative.symm
