/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericTrivializationGalois
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteSetRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedConstantValues
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.ZMod
public import Aglib.Algebra.Category.ModuleCat.FullForget

/-!
# Actual finite étale trivializations of finite ZMod local systems

The original underlying finite additive sheaf is represented and split using
the proved finite étale Galois-category construction. On that same cover its
original module of global sections supplies the constant module value. Full
scalar forgetting lifts the original additive comparison with that value.
The two native ZMod constructions have no supplied global-cover, geometric
point, representability, splitting or module-comparison premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] [Finite R]
  [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
  {X : Scheme.{u}} [ConnectedSpace X]

/-- Over a finite ring with full additive forgetting, every original finite-type
locally constant module sheaf admits a genuine connected Galois finite étale
trivialization. The cover and module isomorphism are constructed. -/
theorem nonempty_galoisCoverConstantTrivialization
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F) :
    Nonempty (GaloisCoverConstantTrivialization F) := by
  let L := (moduleUnderlying R X).obj F
  let D := CoefficientRepresentation.ofFiniteLocallyConstant L (stacks03RV X)
    (isFiniteLocallyConstant_underlying hF)
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let s := Scheme.FiniteEtale.algebraicClosureResiduePoint X x
  let T := finiteSplittingCover s D.group
  let Y := T.cover
  let : PreGaloisCategory.IsGalois Y := T.galois
  let : ConnectedSpace Y.obj.left :=
    Scheme.FiniteEtale.Connectedness.connectedSpace_of_categoricalConnected Y
  let : Finite T.localValue := T.finite_localValue
  let FY := (moduleInverseImage R Y.obj.hom).obj F
  let e : (moduleUnderlying R Y.obj.left).obj FY ≅
      (constantSheaf Y.obj.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj T.localValue :=
    (moduleInverseImageUnderlyingIso R Y.obj.hom).app F ≪≫
      (inverseImage Y.obj.hom).mapIso D.iso.symm ≪≫ T.localTrivializationIso
  let : IsIso ((constantAdjunction Y.obj.left).unit.app T.localValue) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConstantFinite.constantUnit_bijective_value_of_connected Y.obj.left T.localValue)
  let M : ModuleCat.{u + 1} R := FY.obj.obj (op (etaleTerminal Y.obj.left))
  let eM : (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj M ≅ T.localValue :=
    (globalSections Y.obj.left).mapIso e ≪≫
      (asIso ((constantAdjunction Y.obj.left).unit.app T.localValue)).symm
  let : Finite M := Finite.of_injective eM.hom
    (ConcreteCategory.bijective_of_isIso eM.hom).injective
  let eModule :
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ≅ FY :=
    (moduleUnderlying R Y.obj.left).preimageIso
      ((moduleConstantUnderlyingIso R Y.obj.left).app M ≪≫
        (constantSheaf Y.obj.left.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso eM ≪≫ e.symm)
  exact ⟨{
    cover := Y
    galois_cover := inferInstance
    connected_cover := inferInstance
    surjective_cover := ⟨T.surjective⟩
    value := M
    finite_value := Module.Finite.of_finite
    iso := eModule.symm }⟩

omit [Finite R] [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full] in
/-- Every positive ZMod finite local system has an actual global connected
Galois finite étale trivialization, with its original scalar action. -/
def zmodGaloisCoverConstantTrivialization (n : ℕ) (hn : 0 < n)
    (F : ModuleSheaf (ZMod n) X) (hF : IsFiniteTypeLocallyConstant F) :
    GaloisCoverConstantTrivialization F := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).Full :=
    ModuleCat.forget₂_full_of_surjective_intCast (ZMod n) ZMod.intCast_surjective
  exact Classical.choice (nonempty_galoisCoverConstantTrivialization F hF)

omit [Finite R] [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full] in
/-- The original lifted ZMod coefficient ring has the same actual global-cover
existence theorem, without changing its module realization or scalar action. -/
def uLiftZModGaloisCoverConstantTrivialization (n : ℕ) (hn : 0 < n)
    (F : ModuleSheaf (ULift.{u + 1} (ZMod n)) X) (hF : IsFiniteTypeLocallyConstant F) :
    GaloisCoverConstantTrivialization F := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}).Full :=
    ModuleCat.uLiftZMod_forget₂_full n
  exact Classical.choice (nonempty_galoisCoverConstantTrivialization F hF)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
