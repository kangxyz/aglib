/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.NoetherianComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineTests
public import Mathlib.GroupTheory.OrderOfElement
public import Aglib.CategoryTheory.Abelian.Ext.OriginalComparisonValues
public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection

/-! # Reverse finite-image transfer of the local projective-line comparison

The original finite cohomology square transfers closed-fibre comparison on
the finite direct-image coefficient to the original coefficient on the source.
The local projective-line theorem supplies this comparison for every coefficient
killed by a positive integer. No field-extension theorem is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u eX eS eX' eS'

attribute [local instance] hasSheafifyLarge

/-- Identify the complete original pullback family before any other geometric
map, direct image, coefficient or degree is substituted. -/
private theorem cohomologyPullback_originalFamily
    {X S : Scheme.{u}}
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
    (k : S ⟶ X) :
    cohomologyPullback.{u, eX, eS} k =
      (inverseImage k).extPrecompMap
        (((inverseImageConstantIso k).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) := rfl

/-! Diagnostic-only named checks of the original proof components.
Each uses the same actual maps; no native or mathematical closure is claimed. -/

/-- Whole native square and mate value, before an Ext coefficient is inserted. -/
private theorem diag_original_mateValue
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    baseChangeMap f f' g g' h =
      (mateEquiv (inverseImageAdjunction f) (inverseImageAdjunction f')
        (TwoSquare.mk (inverseImage g) (inverseImage f) (inverseImage f') (inverseImage g')
          ((inverseImageComp g f').symm ≪≫
            eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h) ≪≫
            inverseImageComp f g').hom)).natTrans := by
  rw [baseChangeMap_eq_nativeMate, inverseImageSquareIso_eq_comp]

/-- Original first source proof at an arbitrary original coefficient object. -/
private theorem diag_original_sourceFirst
    {S S' X' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S')
    (A : AddCommGrpCat.{u + 1}) :
    ((inverseImageConstantIso (f' ≫ g)).app A).inv ≫
        (inverseImageComp g f').hom.app
          ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj A) =
      ((inverseImageConstantIso f').app A).inv ≫
        (inverseImage f').map ((inverseImageConstantIso g).app A).inv := by
  simpa only [Iso.app_inv] using inverseImageComp_constant_inv g f' A

/-- Original equality-transport source proof at the same original coefficient. -/
private theorem diag_original_sourceSecond
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (A : AddCommGrpCat.{u + 1}) :
    ((inverseImageConstantIso (f' ≫ g)).app A).inv ≫
        (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h) ≪≫
          inverseImageComp f g').hom.app
            ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj A) =
      ((inverseImageConstantIso g').app A).inv ≫
        (inverseImage g').map ((inverseImageConstantIso f).app A).inv := by
  have he := Functor.sourceInverse_eq_transport
    (fun k : X' ⟶ S => inverseImage k) (fun k => inverseImageConstantIso k) h A
  simp only [Iso.app_inv, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  rw [← Category.assoc, he]
  exact inverseImageComp_constant_inv f g' A

/-- The actual finite exchange dictionary at the selected coefficient. -/
private theorem diag_original_finiteIso
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((baseChangeMap f f' g g' h.w.symm).app F) := by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  exact Finite.finiteBaseChange_app_isIso f f' g g' h F

set_option diagnostics true in
/-- The actual finite cohomology square also transports bijectivity from the
finite direct-image coefficient back to its source. -/
theorem cohomologyPullback_source_bijective_of_finiteDirectImage
    {X S X' S' : Scheme.{u}}
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
    [HasExt.{eS'} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) [IsFinite f]
    (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : Function.Bijective (cohomologyPullback.{u, eS, eS'} g
      ((directImage f).obj F) q)) :
    Function.Bijective (cohomologyPullback.{u, eX, eX'} g' F q) :=
  by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  let A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let U := (constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj A
  let c := inverseImageComp g f'
  let d := eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h.w.symm) ≪≫ inverseImageComp f g'
  have hSquare : inverseImageSquareIso f f' g g' h.w.symm = c.symm ≪≫ d :=
    inverseImageSquareIso_eq_comp f f' g g' h.w.symm
  have hMate : baseChangeMap f f' g g' h.w.symm =
      (mateEquiv (inverseImageAdjunction f) (inverseImageAdjunction f')
        (TwoSquare.mk (inverseImage g) (inverseImage f) (inverseImage f') (inverseImage g')
          (c.symm ≪≫ d).hom)).natTrans := by
    rw [baseChangeMap_eq_nativeMate, hSquare]
  have hs : ((inverseImageConstantIso (f' ≫ g)).app A).inv ≫ c.hom.app U =
      ((inverseImageConstantIso f').app A).inv ≫
        (inverseImage f').map ((inverseImageConstantIso g).app A).inv := by
    simpa only [Iso.app_inv] using inverseImageComp_constant_inv g f' A
  have ht : ((inverseImageConstantIso (f' ≫ g)).app A).inv ≫ d.hom.app U =
      ((inverseImageConstantIso g').app A).inv ≫
        (inverseImage g').map ((inverseImageConstantIso f).app A).inv := by
    have he := Functor.sourceInverse_eq_transport
      (fun k : X' ⟶ S => inverseImage k) (fun k => inverseImageConstantIso k) h.w.symm A
    simp only [Iso.app_inv, d, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
    rw [← Category.assoc, he]
    exact inverseImageComp_constant_inv f g' A
  let : IsIso ((baseChangeMap f f' g g' h.w.symm).app F) :=
    Finite.finiteBaseChange_app_isIso f f' g g' h F
  have hInferred := Adjunction.originalExtSourceComparison_bijective_of_mate_values.{
    u + 2, u + 1, eS, u + 2, u + 1, eX, u + 2, u + 1, eS', u + 2, u + 1, eX'}
    (inverseImageAdjunction f) (inverseImageAdjunction f') (inverseImage g) (inverseImage g')
    ((inverseImageConstantIso f).app A) ((inverseImageConstantIso f').app A)
    (inverseImage (f' ≫ g)) c d ((inverseImageConstantIso g).app A).inv
    ((inverseImageConstantIso g').app A).inv ((inverseImageConstantIso (f' ≫ g)).app A).inv
    hs ht (baseChangeMap f f' g g' h.w.symm) hMate
    (cohomologyPullback.{u, eS, eS'} g) (cohomologyPullback_originalFamily g)
    (cohomologyPullback.{u, eX, eX'} g') (cohomologyPullback_originalFamily g') F q hF
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let expected ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
      let some decl := (← Lean.getLCtx).findFromUserName? `hInferred
        | Lean.throwError "missing exact diagnostic inferred proof"
      let inferred ← Lean.instantiateMVars decl.type
      let describe (e : Lean.Expr) : String :=
        let kind := match e.getAppFn with
          | .const n _ => s!"const:{n}"
          | .fvar f => s!"fvar:{f.name}"
          | .mvar _ => "mvar"
          | .lam .. => "lambda"
          | .forallE .. => "forall"
          | .letE .. => "let"
          | .sort _ => "sort"
          | .lit _ => "literal"
          | .bvar i => s!"bvar:{i}"
          | .mdata .. => "metadata"
          | .proj .. => "projection"
          | .app .. => "application"
        s!"{kind};args={e.getAppNumArgs};hash={hash e}"
      Lean.logInfo m!"LFC_BOUND_EXPECTED {describe expected}"
      Lean.logInfo m!"LFC_BOUND_INFERRED {describe inferred}"
      Lean.logInfo m!"LFC_BOUND_SYNTACTIC_EQUAL {expected == inferred}"
      let ea := expected.getAppArgs
      let ia := inferred.getAppArgs
      for i in [:min 6 (min ea.size ia.size)] do
        Lean.logInfo m!"LFC_ARG {i} E[{describe ea[i]!}] I[{describe ia[i]!}] EQ={ea[i]! == ia[i]!}"
        let eb := ea[i]!.getAppArgs
        let ib := ia[i]!.getAppArgs
        for j in [:min 4 (min eb.size ib.size)] do
          Lean.logInfo m!"LFC_ARG2 {i}.{j} E[{describe eb[j]!}] I[{describe ib[j]!}]"
          Lean.logInfo m!"LFC_ARG2_EQ {i}.{j} {eb[j]! == ib[j]!}"
  exact hInferred

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
