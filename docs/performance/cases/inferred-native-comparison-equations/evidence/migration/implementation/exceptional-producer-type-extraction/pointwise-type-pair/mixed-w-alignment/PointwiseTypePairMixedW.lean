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
# Raw pointwise type pair

The expected formation binder is copied from PointwiseCube b720, replacing only
sq.w.symm by h. The diagnostic inspects producer type inference, not its proof.
Raw syntax is retained before optional syntactic comparison. No definitional
equality test, native functor/exchange unfolding, or semantic option change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.PointwiseTypePair

open Coefficients

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wAX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

attribute [local instance] CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Formation of the expected literal proposition; no pointwise proof is asserted. -/
theorem expectedFormation (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (_h :
    (derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K) ≫
      ((derivedBaseChangeMap f f' g g' h).app
        ((moduleDerivedUnderlying Λ X).obj K)) ≫
      (derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K) =
    (moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K) ≫
      (moduleDerivedUnderlying Λ S').map
        ((moduleDerivedBaseChangeMap Λ f f' g g' h).app K) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K)) : True := True.intro

end AlgebraicGeometry.Scheme.EtaleCohomology.PointwiseTypePair

open Lean Meta

namespace PointwiseTypePairDiagnostic

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
  if e.isApp then
    let args := e.getAppArgs
    let mut entries : Array String := #[]
    for i in [:min args.size 8] do
      entries := entries.push s!"{i}:({← bounded args[i]! (depth - 1)})"
    return s!"({← head e}) argc={args.size} [{String.intercalate "; " entries.toList}]"
  else return ← head e

structure DumpState where
  cache : Std.HashMap ExprStructEq Nat := {}
  rows : Array String := #[]

partial def intern (e : Expr) : StateT DumpState MetaM Nat := do
  if let some i := (← get).cache[ExprStructEq.mk e]? then return i
  let payload ← match e with
    | .app f a => pure s!"app fn={← intern f} arg={← intern a}"
    | .lam n t b bi =>
      pure s!"lambda name={reprStr n} info={reprStr bi} type={← intern t} body={← intern b}"
    | .forallE n t b bi =>
      pure s!"forall name={reprStr n} info={reprStr bi} type={← intern t} body={← intern b}"
    | .letE n t v b nondep =>
      pure s!"let name={reprStr n} nondep={nondep} type={← intern t} \
        value={← intern v} body={← intern b}"
    | .mdata md b => pure s!"metadata data={reprStr md} body={← intern b}"
    | .proj n i b => pure s!"projection name={reprStr n} index={i} body={← intern b}"
    | .fvar id =>
      let d ← getFVarLocalDecl e
      pure s!"fvar id={reprStr id.name} name={reprStr d.userName}"
    | .mvar id => pure s!"mvar id={reprStr id.name}"
    | .bvar i => pure s!"bvar index={i}"
    | .const n us => pure s!"const name={reprStr n} levels={reprStr us}"
    | .sort l => pure s!"sort level={reprStr l}"
    | .lit l => pure s!"literal value={reprStr l}"
  let i := (← get).rows.size
  modify fun s => {
    cache := s.cache.insert (ExprStructEq.mk e) i
    rows := s.rows.push s!"RAW_NODE {i} {payload}"
  }
  return i

def dump (label : String) (e : Expr) : MetaM Unit := do
  let (root, state) ← (intern e).run {}
  emit s!"RAW_{label}_BEGIN"
  for row in state.rows do emit row
  emit s!"RAW_{label}_ROOT {root} nodes={state.rows.size}"
  emit s!"RAW_{label}_END"

def reportWHeads (label : String) (e : Expr) : MetaM Unit := do
  let standard := `CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard
  let generic := Name.str `CategoryTheory.GrothendieckTopology
    "instWEqualsLocallyBijectiveOfHasWeakSheafifyOfHasSheafComposeOfPreserves\
      SheafificationOfReflectsIsomorphismsForget"
  let standardCount ← IO.mkRef (0 : Nat)
  let genericCount ← IO.mkRef (0 : Nat)
  e.forEach fun node => do
    if let .const n levels := node then
      if n == standard then
        standardCount.modify (· + 1)
        emit s!"W_CONST {label} standard levels={reprStr levels}"
      if n == generic then
        genericCount.modify (· + 1)
        emit s!"W_CONST {label} generic levels={reprStr levels}"
  emit s!"W_HEADS {label} standardUniqueConstNodes={← standardCount.get} \
    genericUniqueConstNodes={← genericCount.get}"

partial def captureClosedBinders (label : String) (t : Expr) (index : Nat) : MetaM Unit := do
  match t with
  | .forallE n d b bi =>
    emit s!"CLOSED_BINDER {label} index={index} name={n} info={reprStr bi}"
    if d.getAppFn.isConstOf `HasDerivedCategory || n == `K || n == `_h then
      let tag := s!"{label}_BINDER_{index}"
      dump tag d
      reportWHeads tag d
    captureClosedBinders label b (index + 1)
  | _ => emit s!"CLOSED_BINDERS_COMPLETE {label} count={index}"

def findLocal (locals : Array (Name × Expr)) (n : Name) (bi : BinderInfo)
    (t : Expr) : MetaM Expr := do
  if bi == .instImplicit then
    for (_, x) in locals do
      if (← getFVarLocalDecl x).type == t then return x
    throwError "No raw-type-matching original local instance for {n}"
  for (name, x) in locals do
    if name == n then return x
  throwError "No original producer local named {n}"

partial def alignExpected (locals : Array (Name × Expr)) (t : Expr)
    (index : Nat) : MetaM Expr := do
  match t with
  | .forallE n d b bi =>
    if n == `_h then return d
    let x ← findLocal locals n bi d
    emit s!"EXPECTED_BINDER {n} mapsTo=({← head x}) typeHead=({← head d})"
    let producerType := (← getFVarLocalDecl x).type
    emit s!"BINDER_TYPE_MATCH index={index} name={n} alpha={d == producerType} \
      structural={d.equal producerType}"
    if d.getAppFn.isConstOf `HasDerivedCategory || n == `K then
      dump s!"EXPECTED_PRE_REBIND_{index}" d
      dump s!"PRODUCER_MATCHED_BINDER_{index}" producerType
      reportWHeads s!"EXPECTED_PRE_REBIND_{index}" d
      reportWHeads s!"PRODUCER_MATCHED_BINDER_{index}" producerType
    unless d == producerType do
      dump s!"EXPECTED_BINDER_GAP_{index}" d
      dump s!"PRODUCER_BINDER_GAP_{index}" producerType
      throwError "Aligned local {n} has a raw type mismatch; no substitution performed"
    alignExpected locals (b.instantiate1 x) (index + 1)
  | _ =>
    dump "EXPECTED_UNALIGNED_TYPE" t
    throwError "Expected formation declaration has no final _h binder"

structure Difference where
  path : String
  reason : String
  actual : Expr
  expected : Expr

partial def firstDifference (a b : Expr) (path : String) (fuel : Nat) : Option Difference :=
  if a.equal b then none else
  if fuel == 0 then some ⟨path, "bounded-depth", a, b⟩ else
  match a, b with
  | .app _ _, .app _ _ => Id.run do
    if let some d := firstDifference a.getAppFn b.getAppFn (path ++ ".head") (fuel - 1) then
      return some d
    let aa := a.getAppArgs
    let bb := b.getAppArgs
    for i in [:min aa.size bb.size] do
      if let some d := firstDifference aa[i]! bb[i]! s!"{path}.arg[{i}]" (fuel - 1) then
        return some d
    return some ⟨path, s!"application-arity actual={aa.size} expected={bb.size}", a, b⟩
  | .lam na ta ba bia, .lam nb tb bb bib
  | .forallE na ta ba bia, .forallE nb tb bb bib =>
    if na != nb || bia != bib then some ⟨path, "binder-name-or-info", a, b⟩
    else (firstDifference ta tb (path ++ ".domain") (fuel - 1)).orElse fun _ =>
      firstDifference ba bb (path ++ ".body") (fuel - 1)
  | .proj na ia ea, .proj nb ib eb =>
    if na != nb || ia != ib then some ⟨path, "projection-name-or-index", a, b⟩
    else firstDifference ea eb (path ++ ".projectionBody") (fuel - 1)
  | .mdata ma ea, .mdata mb eb =>
    if ma != mb then some ⟨path, "metadata-payload", a, b⟩
    else firstDifference ea eb (path ++ ".metadataBody") (fuel - 1)
  | .letE na ta va ba nda, .letE nb tb vb bb ndb =>
    if na != nb || nda != ndb then some ⟨path, "let-name-or-nondep", a, b⟩
    else (firstDifference ta tb (path ++ ".letType") (fuel - 1)).orElse fun _ =>
      (firstDifference va vb (path ++ ".letValue") (fuel - 1)).orElse fun _ =>
        firstDifference ba bb (path ++ ".letBody") (fuel - 1)
  | _, _ => some ⟨path, "raw-constructor-or-payload", a, b⟩

def reportPair (locals : Array (Name × Expr)) (cube : Expr) : MetaM Unit := do
  unless locals.size == 19 do throwError "Expected nineteen producer locals"
  unless cube.getAppFn.isConstOf `CategoryTheory.HorizontalMateCubeEquation do
    throwError "Unexpected producer conclusion head"
  let kType := cube.getAppArgs[1]!
  withLocalDecl `K .default kType fun k => do
    let ci ← getConstInfo
      `AlgebraicGeometry.Scheme.EtaleCohomology.moduleDerivedBaseChangeMap_underlying
    let term := mkApp (mkAppN (mkConst ci.name (ci.levelParams.map Level.param))
      (locals.map Prod.snd)) k
    emit s!"ACTUAL_INFER_START producerArgs={locals.size} KType=({← head kType})"
    let actual ← inferType term
    dump "ACTUAL" actual
    reportWHeads "ACTUAL" actual
    emit s!"ACTUAL_RETAINED kind={kind actual} head=({← head actual})"
    let expectedCi ← getConstInfo
      `AlgebraicGeometry.Scheme.EtaleCohomology.PointwiseTypePair.expectedFormation
    captureClosedBinders "EXPECTED_CLOSED" expectedCi.type 0
    captureClosedBinders "PRODUCER_CLOSED" ci.type 0
    dump "PRODUCER_K_TYPE" kType
    reportWHeads "PRODUCER_K_TYPE" kType
    let expected ← alignExpected (locals.push (`K, k)) expectedCi.type 0
    dump "EXPECTED" expected
    reportWHeads "EXPECTED" expected
    emit s!"PAIR_RETAINED actualHasMVars={actual.hasMVar} expectedHasMVars={expected.hasMVar}"
    emit s!"RAW_EQUALITY alpha={actual == expected} structural={actual.equal expected}"
    if let some diff := firstDifference actual expected "root" 32 then
      emit s!"FIRST_DIFF path={diff.path} reason={diff.reason}"
      emit s!"DIFF_ACTUAL kind={kind diff.actual} {← bounded diff.actual 2}"
      emit s!"DIFF_EXPECTED kind={kind diff.expected} {← bounded diff.expected 2}"
      dump "DIFF_ACTUAL" diff.actual
      dump "DIFF_EXPECTED" diff.expected
    emit "COMPLETE raw pointwise type pair; no Meta defeq or theorem value inspected"

partial def peel (e : Expr) (locals : Array (Name × Expr)) : MetaM Unit := do
  match e with
  | .forallE n t b bi =>
    emit s!"ORIGINAL_BINDER {locals.size} {n} {reprStr bi} head=({← head t})"
    withLocalDecl n bi t fun x => do
      emit s!"ORIGINAL_LOCAL index={locals.size} id={reprStr x.fvarId!.name} name={n}"
      peel (b.instantiate1 x) (locals.push (n, x))
  | _ => reportPair locals e

run_meta do
  let ci ← getConstInfo
    `AlgebraicGeometry.Scheme.EtaleCohomology.moduleDerivedBaseChangeMap_underlying
  emit s!"PRODUCER_LEVELS {reprStr ci.levelParams}"
  peel ci.type #[]

end PointwiseTypePairDiagnostic
