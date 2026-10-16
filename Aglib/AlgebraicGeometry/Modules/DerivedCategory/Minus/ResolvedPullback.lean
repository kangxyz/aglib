/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.Models
public import Aglib.AlgebraicGeometry.Modules.Complex.Pullback


/-!
# Geometric flat-model pullback into the actual derived category

The projective homotopy functor, exact sheafification, and arbitrary geometric
pullback give an additive functor which inverts every original bounded-above
sheaf quasi-isomorphism. Its actual object and map formulas are retained; it
lands in `DerivedCategory.Minus`, agrees with termwise pullback on genuinely
flat inputs, and has the actual augmentation comparison for identity maps.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/ResolvedBoundedPullback.lean`.
SHA-256: `59861283cf59c1ef6cc0daead698e3a5fbaa6a8a41b97b6edea0ff33ab7197a7`.
Selected source lines: 1–159.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

open CochainComplex


open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- A genuinely functorial replacement followed by arbitrary geometric pullback,
with values in the actual derived category. -/
def resolvedPullbackFunctor (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules] :
    BoundedAboveComplex Y.Modules ⥤ DerivedCategory X.Modules :=
  letI : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).Additive :=
    SheafOfModulesOfCommRing.associatedSheaf_additive Y.sheaf
  (underlyingPresheafBoundedFunctor Y ⋙
    projectiveModelHomotopyFunctor (_root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) ⋙
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapHomotopyCategory (.up ℤ) ⋙
    (Scheme.Modules.pullback f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).copyObj
    (fun K => DerivedCategory.Q.obj
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y K)))
    (fun K => (DerivedCategory.quotientCompQhIso X.Modules).app
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y K)))

/-- The displayed derived objects are normalized using the canonical quotient comparison,
while retaining the original homotopy-composite functor by this natural isomorphism. -/
def resolvedPullbackFunctorComparisonIso (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules] :
    letI : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).Additive :=
      SheafOfModulesOfCommRing.associatedSheaf_additive Y.sheaf
    underlyingPresheafBoundedFunctor Y ⋙
    projectiveModelHomotopyFunctor (_root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) ⋙
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapHomotopyCategory (.up ℤ) ⋙
    (Scheme.Modules.pullback f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      resolvedPullbackFunctor f :=
  letI : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).Additive :=
    SheafOfModulesOfCommRing.associatedSheaf_additive Y.sheaf
  Functor.isoCopyObj _ _ _

@[simp]
theorem resolvedPullbackFunctor_obj (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules]
    (K : BoundedAboveComplex Y.Modules) :
    (resolvedPullbackFunctor f).obj K =
      DerivedCategory.Q.obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y
        K)) :=
        rfl

@[simp]
theorem resolvedPullbackFunctor_map (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules]
    {K L : BoundedAboveComplex Y.Modules} (s : K ⟶ L) :
    (resolvedPullbackFunctor f).map s =
      DerivedCategory.Q.map
        ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map (flatModelMap s)) := by
  change (DerivedCategory.quotientCompQhIso X.Modules).inv.app
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y K)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient X.Modules (.up ℤ)).map
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map (flatModelMap s))) ≫
    (DerivedCategory.quotientCompQhIso X.Modules).hom.app
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y L)) = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]

/-- The functor evaluates to the actual pullback of the constructed flat model. -/
def resolvedPullbackObjectIso (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules]
    (K : BoundedAboveComplex Y.Modules) :
    (resolvedPullbackFunctor f).obj K ≅
      DerivedCategory.Q.obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y
        K)) :=
  (resolvedPullbackFunctorComparisonIso f).symm.app K ≪≫
    (DerivedCategory.quotientCompQhIso X.Modules).app
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y K))

instance resolvedPullbackFunctor_additive (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules] :
    (resolvedPullbackFunctor f).Additive := by
  exact Functor.additive_of_iso (resolvedPullbackFunctorComparisonIso f)

/-- The original support of the chosen flat model gives actual bounded-above derived support. -/
def resolvedPullbackFunctorMinus (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules] :
    BoundedAboveComplex Y.Modules ⥤ DerivedCategory.Minus X.Modules :=
  (DerivedCategory.TStructure.t.minus).lift (resolvedPullbackFunctor f) (fun K => by
    let b := chosenUpperBound ((underlyingPresheafBoundedFunctor Y).obj K)
    have : ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y K)).IsStrictlyLE
      b := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro n hn
      exact (Scheme.Modules.pullback f).map_isZero ((flatModel Y K).isZero_of_isStrictlyLE b n hn)
    have : (DerivedCategory.Q.obj
        ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y K))).IsLE b :=
          inferInstance
    exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso (resolvedPullbackObjectIso f K).symm b⟩)

/-- The genuine resolved pullback functor inverts original sheaf quasi-isomorphisms. -/
theorem resolvedPullbackFunctor_inverts (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules]
    {K L : BoundedAboveComplex Y.Modules} (s : K ⟶ L) [QuasiIso s.hom] :
    IsIso ((resolvedPullbackFunctor f).map s) := by
  have := pullback_flatModelMap_quasiIso f s
  rw [resolvedPullbackFunctor_map]
  infer_instance

/-- On genuinely degreewise-flat original complexes, the derived object has its expected
underived geometric representative. No flatness assumption on the scheme map is used. -/
def resolvedPullbackFlatObjectIso (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules]
    (K : BoundedAboveComplex Y.Modules) (hK : ∀ n, stalkwiseFlat Y (K.obj.X n)) :
    (resolvedPullbackFunctor f).obj K ≅
      DerivedCategory.Q.obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj K.obj) := by
  have : QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map (flatModelπ Y K)) :=
    quasiIso_pullback_of_boundedAbove_stalkwiseFlat f (flatModel_flat Y K) hK
      (chosenUpperBound ((underlyingPresheafBoundedFunctor Y).obj K)) (chosenUpperBound K)
      (fun n hn => (flatModel Y K).isZero_of_isStrictlyLE _ n hn)
      (fun n hn => K.obj.isZero_of_isStrictlyLE _ n hn) _
  exact resolvedPullbackObjectIso f K ≪≫
    asIso (DerivedCategory.Q.map ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map
      (flatModelπ Y
      K)))

/-- Resolved pullback along an identity is naturally the original derived localization functor. -/
def resolvedPullbackIdIso (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules] :
    resolvedPullbackFunctor (𝟙 X) ≅ (boundedAbove X.Modules).ι ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun K => by
    let q :=
      (AlgebraicGeometry.Scheme.Modules.Complex.pullbackIdIso X).hom.app (flatModel X K) ≫
        flatModelπ X K
    have : QuasiIso q := by dsimp [q]; infer_instance
    exact asIso (DerivedCategory.Q.map q)) (fun {K L} s => by
      rw [resolvedPullbackFunctor_map]
      change DerivedCategory.Q.map ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (𝟙 X)).map
        (flatModelMap s)) ≫ DerivedCategory.Q.map _ =
        DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map s.hom
      rw [← Functor.map_comp, ← Functor.map_comp]
      rw [← Category.assoc,
        (AlgebraicGeometry.Scheme.Modules.Complex.pullbackIdIso X).hom.naturality,
        Category.assoc, Category.assoc]
      exact DerivedCategory.Q_map_eq_of_homotopy X.Modules
        ((flatModelMapHomotopy s).compLeft
          ((AlgebraicGeometry.Scheme.Modules.Complex.pullbackIdIso X).hom.app (flatModel X K))))

end AlgebraicGeometry.Scheme.Modules
