/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.BaseChange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Conservative

/-!
# Producer declaration type metadata

No theorem value access, reduction, unfolding, definitional-equality test, or
budget/semantic option change. Outer telescopes are peeled syntactically.
-/

public section

open Lean Meta

namespace ProducerTypeExtraction

def emit (s : String) : MetaM Unit := do IO.println s

def kind : Expr → String
  | .bvar _ => "bvar" | .fvar _ => "fvar" | .mvar _ => "mvar"
  | .sort _ => "sort" | .const _ _ => "const" | .app _ _ => "app"
  | .lam _ _ _ _ => "lambda" | .forallE _ _ _ _ => "forall"
  | .letE _ _ _ _ _ => "let" | .lit _ => "literal"
  | .mdata _ _ => "metadata" | .proj _ _ _ => "projection"

partial def head (e : Expr) : MetaM String := do
  match e with
  | .app f _ => head f
  | .const n us => pure s!"const {n} universes={reprStr us}"
  | .fvar _ => pure s!"fvar {(← getFVarLocalDecl e).userName}"
  | .bvar i => pure s!"bvar {i}"
  | .mvar id => pure s!"mvar {id.name}"
  | .sort u => pure s!"sort {reprStr u}"
  | .proj n i b => pure s!"projection {n}.{i} base=({← head b})"
  | .lam n _ b _ => pure s!"lambda {n} body=({← head b})"
  | .forallE n _ b _ => pure s!"forall {n} body=({← head b})"
  | .letE n _ _ b _ => pure s!"let {n} body=({← head b})"
  | .mdata _ b => pure s!"metadata ({← head b})"
  | .lit l => pure s!"literal {reprStr l}"

partial def bounded (e : Expr) (depth : Nat) : MetaM String := do
  if depth == 0 then return ← head e
  match e with
  | .app _ _ =>
    let args := e.getAppArgs
    let mut entries : Array String := #[]
    for i in [:min args.size 6] do
      entries := entries.push s!"{i}:({← bounded args[i]! (depth - 1)})"
    pure s!"({← head e}) argc={args.size} [{String.intercalate "; " entries.toList}]"
  | .lam n t b bi =>
    pure s!"lambda {n} {reprStr bi} domain=({← head t}) \
      body=({← bounded b (depth - 1)})"
  | .proj n i b => pure s!"projection {n}.{i} base=({← bounded b (depth - 1)})"
  | .mdata _ b => pure s!"metadata ({← bounded b (depth - 1)})"
  | _ => head e

def nodes (e : Expr) : MetaM Nat := do
  let r ← IO.mkRef 0
  e.forEach fun _ => r.modify (· + 1)
  r.get

partial def binderNames (e : Expr) : Array Name :=
  match e with
  | .forallE n _ b _ => #[n] ++ binderNames b
  | _ => #[]

def lookupLocal (locals : Array (Name × Expr)) (s : String) : MetaM Expr := do
  for (n, e) in locals do
    if n.toString == s then return e
  throwError "Producer binder absent: {s}"

def intended (locals : Array (Name × Expr)) (slot : String) : MetaM Expr := do
  let coeff := `AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
  let etale := `AlgebraicGeometry.Scheme.EtaleCohomology
  let lam ← lookupLocal locals "Λ"
  let (decl, arg, coefficient) ← match slot with
    | "R₁" => pure (coeff ++ `moduleDerivedDirectImage, "f", true)
    | "R₂" => pure (coeff ++ `moduleDerivedDirectImage, "f'", true)
    | "R₁'" => pure (etale ++ `derivedDirectImage, "f", false)
    | "R₂'" => pure (etale ++ `derivedDirectImage, "f'", false)
    | "G" => pure (coeff ++ `moduleDerivedInverseImage, "g", true)
    | "H" => pure (coeff ++ `moduleDerivedInverseImage, "g'", true)
    | "G'" => pure (etale ++ `derivedInverseImage, "g", false)
    | "H'" => pure (etale ++ `derivedInverseImage, "g'", false)
    | "QA" => pure (coeff ++ `moduleDerivedUnderlying, "S", true)
    | "QB" => pure (coeff ++ `moduleDerivedUnderlying, "X", true)
    | "QC" => pure (coeff ++ `moduleDerivedUnderlying, "S'", true)
    | "QD" => pure (coeff ++ `moduleDerivedUnderlying, "X'", true)
    | _ => throwError "Unexpected functor slot {slot}"
  let x ← lookupLocal locals arg
  let (first, second) ← match slot with
    | "R₁" => pure (`wMS, `wMX)
    | "R₂" => pure (`wMS', `wMX')
    | "R₁'" => pure (`wAX, `wAS)
    | "R₂'" => pure (`wAX', `wAS')
    | "G" => pure (`wMS, `wMS')
    | "H" => pure (`wMX, `wMX')
    | "G'" => pure (`wAS', `wAS)
    | "H'" => pure (`wAX', `wAX)
    | "QA" => pure (`wMS, `wAS)
    | "QB" => pure (`wMX, `wAX)
    | "QC" => pure (`wMS', `wAS')
    | "QD" => pure (`wMX', `wAX')
    | _ => throwError "Unexpected slot universes {slot}"
  let ci ← getConstInfo decl
  let levels ← ci.levelParams.mapM fun p => do
    if p == `u then return Level.param `u
    if p == `w || p == `wMX then return Level.param first
    if p == `w' || p == `wAX then return Level.param second
    throwError "Unexpected native universe parameter {p} for {decl}"
  emit s!"INTENDED_LEVELS {slot} nativeParams={reprStr ci.levelParams} \
    selected={reprStr levels}"
  let fn := mkConst decl levels
  let e ← if coefficient then mkAppM' fn #[lam, x] else mkAppM' fn #[x]
  instantiateMVars e

def reportSlot (slot : String) (actual expected : Expr) : MetaM Unit := do
  emit s!"SLOT {slot} actualKind={kind actual} actualNodes={← nodes actual} \
    expectedNodes={← nodes expected} alphaEqual={actual == expected} \
    structuralEqual={actual.equal expected} expectedHasMVars={expected.hasMVar}"
  emit s!"ACTUAL {slot} {← bounded actual 2}"
  emit s!"INTENDED {slot} {← bounded expected 1}"
  if actual.getAppFn.isConstOf ``CategoryTheory.Functor.mk then
    let args := actual.getAppArgs
    let ci ← getConstInfo ``CategoryTheory.Functor.mk
    match ci with
    | .ctorInfo c =>
      emit s!"FUNCTOR_CTOR {slot} numParams={c.numParams} totalArgs={args.size}"
      for (field, offset) in [("obj", 0), ("map", 1)] do
        if let some v := args[c.numParams + offset]? then
          emit s!"FIELD {slot}.{field} kind={kind v} nodes={← nodes v} {← bounded v 3}"
    | _ => throwError "Functor.mk is not constructor metadata"

def reportCube (locals : Array (Name × Expr)) (body : Expr) : MetaM Unit := do
  let cubeName := `CategoryTheory.HorizontalMateCubeEquation
  unless body.getAppFn.isConstOf cubeName do
    throwError "Raw producer conclusion has unexpected head: {← head body}"
  emit s!"CUBE {← head body} argc={body.getAppArgs.size} nodes={← nodes body}"
  let cube ← getConstInfo cubeName
  let names := binderNames cube.type
  let args := body.getAppArgs
  unless names.size == args.size do
    throwError "Cube binder count {names.size} differs from raw application count {args.size}"
  let slots := ["R₁", "R₂", "R₁'", "R₂'", "G", "H", "G'", "H'", "QA", "QB", "QC", "QD"]
  let mut actualCount : Nat := 0
  for i in [:names.size] do
    let n := names[i]!.toString
    emit s!"CUBE_ARGUMENT index={i} binder={n} kind={kind args[i]!} head=({← head args[i]!})"
    if slots.contains n then
      emit s!"ACTUAL_FIRST {n} kind={kind args[i]!} nodes={← nodes args[i]!} \
        {← bounded args[i]! 2}"
      actualCount := actualCount + 1
  unless actualCount == 12 do throwError "Expected twelve actual slots; found {actualCount}"
  emit "ACTUAL_COMPLETE twelve named slots emitted before optional intended construction"
  let mut seen : Nat := 0
  for i in [:names.size] do
    let n := names[i]!.toString
    if slots.contains n then
      try
        let expected ← intended locals n
        reportSlot n args[i]! expected
      catch ex =>
        emit s!"INTENDED_GAP {n} {← ex.toMessageData.toString}"
      seen := seen + 1
  unless seen == 12 do throwError "Expected twelve slots; found {seen}"
  emit "COMPLETE twelve slots; raw type only; no theorem value/reduction/defeq inspected"

partial def peel (e : Expr) (locals : Array (Name × Expr)) : MetaM Unit := do
  match e with
  | .forallE n t b bi =>
    emit s!"PRODUCER_BINDER index={locals.size} name={n} binderInfo={reprStr bi} \
      typeNodes={← nodes t} type=({← bounded t 1})"
    withLocalDecl n bi t fun x => peel (b.instantiate1 x) (locals.push (n, x))
  | _ => reportCube locals e

run_meta do
  let n := `AlgebraicGeometry.Scheme.EtaleCohomology.moduleDerivedBaseChangeMap_underlying
  let ci ← getConstInfo n
  emit s!"PRODUCER {n} levelParams={reprStr ci.levelParams} rawTypeNodes={← nodes ci.type}"
  peel ci.type #[]

end ProducerTypeExtraction
