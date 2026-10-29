/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricPullbackCoefficient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomology

/-! # Actual geometric-system cohomology and original fibre-product restrictions -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e uI vI
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

/-- Normalize the original all-degree map before evaluating a concrete geometric system. -/
theorem diagramCohomologyMap_pullbackCoefficientSystem
    {I : Type uI} [Category.{vI} I] (Y : I ⥤ Scheme.{u}ᵒᵖ)
    (b : Cone Y) (F : AbelianSheaf.{u, u + 1} b.pt.unop)
    [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (Y.obj i).unop)]
    (q : ℕ) {i j : I} (a : i ⟶ j) :
    diagramCohomologyMap Y (pullbackCoefficientSystem Y b F) q a =
      cohomologyTransfer (Y.map a).unop (pullbackCoefficientTransition Y b F a) q := by
  refine (diagramCohomologyMap_eq_transfer Y (pullbackCoefficientSystem Y b F) q a).trans ?_
  exact congrArg
    (fun t : (inverseImage (Y.map a).unop).obj
        ((pullbackCoefficientSystem Y b F).obj i) ⟶ (pullbackCoefficientSystem Y b F).obj j =>
      (cohomologyTransfer (Y.map a).unop
        (F := (pullbackCoefficientSystem Y b F).obj i)
        (G := (pullbackCoefficientSystem Y b F).obj j) t q :
        AddCommGrpCat.of (Sheaf.H.{e} ((pullbackCoefficientSystem Y b F).obj i) q) ⟶
          AddCommGrpCat.of (Sheaf.H.{e} ((pullbackCoefficientSystem Y b F).obj j) q)))
    (diagramInverseTransition_pullbackCoefficientSystem Y b F a)

/-- Evaluate a whole triangle comparison at the original fixed coefficient system. -/
theorem pullbackCoefficientTransition_of_triangleIso_eq
    {I : Type uI} [Category.{vI} I] (Y : I ⥤ Scheme.{u}ᵒᵖ)
    (b : Cone Y) (F : AbelianSheaf.{u, u + 1} b.pt.unop)
    {i j : I} (a : i ⟶ j)
    (e : inverseImage (b.π.app j).unop ≅
      inverseImage (b.π.app i).unop ⋙ inverseImage (Y.map a).unop)
    (he : pullbackTriangleIso (b.π.app j).unop (b.π.app i).unop (Y.map a).unop
      (congrArg Quiver.Hom.unop (b.w a)) = e) :
    pullbackCoefficientTransition Y b F a = e.inv.app F :=
  NatTrans.congr_app (congrArg Iso.inv he) F

/-- Transport an original cohomology map across literal arrow and coefficient equalities. -/
theorem cohomologyTransfer_of_heq
    {S T : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} T)]
    (f g : T ⟶ S) (hfg : f = g)
    {F : AbelianSheaf.{u, u + 1} S} {G : AbelianSheaf.{u, u + 1} T}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage g).obj F ⟶ G)
    (hφ : HEq φ ψ) (q : ℕ) :
    cohomologyTransfer f φ q =
      AddCommGrpCat.ofHom ((Sheaf.H.map ψ q).comp (cohomologyPullback g F q)) := by
  subst g
  cases hφ
  rfl

/-- The original fibre-product restriction accepts a native arrow/coefficient comparison. -/
theorem fibreProductCohomologyRestriction_of_heq
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Etale} (g : V ⟶ U)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom f))]
    (F : AbelianSheaf.{u, u + 1} X)
    (k : pullback V.hom f ⟶ pullback U.hom f)
    (hk : k = ((siteBaseChange f).map g).left)
    (φ : (inverseImage k).obj ((inverseImage (pullback.snd U.hom f)).obj F) ⟶
      (inverseImage (pullback.snd V.hom f)).obj F)
    (hφ : HEq φ ((pullbackTriangleIso ((siteBaseChange f).obj V).hom
      ((siteBaseChange f).obj U).hom ((siteBaseChange f).map g).left
      (MorphismProperty.Over.w ((siteBaseChange f).map g))).inv.app F)) (q : ℕ) :
    cohomologyTransfer k φ q =
      AddCommGrpCat.ofHom (fibreProductCohomologyRestriction f g F q) :=
  cohomologyTransfer_of_heq k ((siteBaseChange f).map g).left hk φ _ hφ q

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual strict-local cocone is colimiting in the opposite scheme category. -/
def geometricCoefficientLimitIsColimit :
    IsColimit (geometricCoefficientLimitCocone R Ω f) :=
  (baseChangedConeIsLimit R Ω f).op.whiskerEquivalence
    (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).symm

/-- The geometric structure arrow is the literal native pullback projection. -/
theorem geometricCoefficientStructure_eq (U : GeometricEtaleNeighborhood R Ω) :
    ((geometricCoefficientBaseCone R Ω f).π.app U).unop =
      ((siteBaseChange f).obj (etaleObject R Ω U)).hom := rfl

/-- The geometric transition is the original native base-changed chart morphism. -/
theorem geometricCoefficientMap_eq {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    ((geometricCoefficientDiagram R Ω f).map a).unop =
      ((siteBaseChange f).map (etaleMap R Ω a)).left := rfl

/-- Compare the complete native triangle before evaluating it at a coefficient sheaf. -/
theorem geometricPullbackTriangleIso_eq
    {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    pullbackTriangleIso ((geometricCoefficientBaseCone R Ω f).π.app V).unop
        ((geometricCoefficientBaseCone R Ω f).π.app U).unop
        ((geometricCoefficientDiagram R Ω f).map a).unop
        (congrArg Quiver.Hom.unop ((geometricCoefficientBaseCone R Ω f).w a)) =
      pullbackTriangleIso ((siteBaseChange f).obj (etaleObject R Ω V)).hom
        ((siteBaseChange f).obj (etaleObject R Ω U)).hom
        ((siteBaseChange f).map (etaleMap R Ω a)).left
        (MorphismProperty.Over.w ((siteBaseChange f).map (etaleMap R Ω a))) := by
  simp only [geometricCoefficientStructure_eq, geometricCoefficientMap_eq]
  rfl

/-- The structural coefficient transition is the literal chart triangle component. -/
theorem geometricPullbackCoefficientTransition_eq
    (F : AbelianSheaf.{u, u + 1} X)
    {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    pullbackCoefficientTransition (geometricCoefficientDiagram R Ω f)
        (geometricCoefficientBaseCone R Ω f) F a =
      (pullbackTriangleIso ((siteBaseChange f).obj (etaleObject R Ω V)).hom
        ((siteBaseChange f).obj (etaleObject R Ω U)).hom
        ((siteBaseChange f).map (etaleMap R Ω a)).left
        (MorphismProperty.Over.w ((siteBaseChange f).map (etaleMap R Ω a)))).inv.app F :=
  pullbackCoefficientTransition_of_triangleIso_eq
    (geometricCoefficientDiagram R Ω f) (geometricCoefficientBaseCone R Ω f) F a _
    (geometricPullbackTriangleIso_eq R Ω f a)

variable [hExt : ∀ U : GeometricEtaleNeighborhood R Ω,
    HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (etaleObject R Ω U).hom f))]

local instance (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((geometricCoefficientDiagram R Ω f).obj U).unop) :=
  hExt U

/-- Original cohomology transfer respects the native geometric coefficient boundary. -/
theorem geometricCohomologyTransfer_eq
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    cohomologyTransfer ((geometricCoefficientDiagram R Ω f).map a).unop
        (pullbackCoefficientTransition (geometricCoefficientDiagram R Ω f)
          (geometricCoefficientBaseCone R Ω f) F a) q =
      AddCommGrpCat.ofHom (fibreProductCohomologyRestriction f (etaleMap R Ω a) F q) :=
  fibreProductCohomologyRestriction_of_heq f (etaleMap R Ω a) F
    ((geometricCoefficientDiagram R Ω f).map a).unop
    (geometricCoefficientMap_eq R Ω f a) _
    (heq_of_eq (geometricPullbackCoefficientTransition_eq R Ω f F a)) q

/-- The actual all-degree stage transition is the original fibre-product restriction. -/
theorem geometricDiagramCohomologyMap_eq
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    diagramCohomologyMap (geometricCoefficientDiagram R Ω f)
        (geometricPullbackCoefficientSystem R Ω f F) q a =
      AddCommGrpCat.ofHom (fibreProductCohomologyRestriction f (etaleMap R Ω a) F q) :=
  (diagramCohomologyMap_pullbackCoefficientSystem
    (geometricCoefficientDiagram R Ω f) (geometricCoefficientBaseCone R Ω f) F q a).trans
      (geometricCohomologyTransfer_eq R Ω f F q a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
