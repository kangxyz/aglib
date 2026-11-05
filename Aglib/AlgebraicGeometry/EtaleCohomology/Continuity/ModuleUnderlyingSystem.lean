/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleCoefficientSystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramInjectives
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImageHomEquiv

/-! # Forgetting scalars in the original varying coefficient system

The native direct-image functor commutes literally with forgetting scalars.
The identity and composition comparisons, including reindexing equality
transports, give a genuine original abelian system. No fullness is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u r uI vI

variable (R : Type r) [Ring R]

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge

/-- The unchanged native scalar-forgetting functor at a scheme. -/
abbrev underlying (X : Scheme.{u}) : Coefficient R X ⥤ AbelianSheaf.{u, u + 1} X :=
  ModuleCat.Sheaf.underlying R X.smallEtaleTopology

/-- Scalar forgetting retains the original direct-image identity comparison. -/
theorem underlying_directImageIdIso_hom (X : Scheme.{u}) (F : Coefficient R X) :
    (underlying R X).map ((directImageIdIso R X).hom.app F) =
      (EtaleCohomology.directImageIdIso X).hom.app ((underlying R X).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

/-- Scalar forgetting retains the original inverse direct-image composition comparison. -/
theorem underlying_directImageCompIso_inv {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (F : Coefficient R T) :
    (underlying R X).map ((directImageCompIso R f g).inv.app F) =
      (EtaleCohomology.directImageCompIso f g).inv.app ((underlying R T).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)

/-- The actual reindexed identity comparison commutes with forgetting scalars. -/
theorem underlying_diagram_idIso_hom (i : I) (F : Coefficient R (X.obj i).unop) :
    (underlying R (X.obj i).unop).map
        (((diagramAdjunctionData R X).idIso i).hom.app F) =
      ((Continuity.diagramAdjunctionData X).idIso i).hom.app
        ((underlying R (X.obj i).unop).obj F) := by
  simp only [InjectiveSystem.AdjunctionData.reindex, schemeAdjunctionData,
    Continuity.schemeAdjunctionData, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Functor.map_comp, eqToHom_map, underlying_directImageIdIso_hom]

/-- The original reindexed composition, including its equality transport,
commutes with scalar forgetting. -/
theorem underlying_diagram_compIso_hom {i j k : I} (a : i ⟶ j) (b : j ⟶ k)
    (F : Coefficient R (X.obj k).unop) :
    (underlying R (X.obj i).unop).map
        (((diagramAdjunctionData R X).compIso a b).hom.app F) =
      ((Continuity.diagramAdjunctionData X).compIso a b).hom.app
        ((underlying R (X.obj k).unop).obj F) := by
  simp only [InjectiveSystem.AdjunctionData.reindex, schemeAdjunctionData,
    Continuity.schemeAdjunctionData, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    Iso.symm_hom, eqToHom_app, Functor.map_comp, eqToHom_map,
    underlying_directImageCompIso_inv]

/-- Forget scalar structure on the original objects and transition arrows. -/
def underlyingSystem (F : DiagramCoefficientSystem R X) :
    Continuity.DiagramCoefficientSystem X where
  obj i := (underlying R (X.obj i).unop).obj (F.obj i)
  map a := (underlying R (X.obj _).unop).map (F.map a)
  map_id i := by
    have h := congrArg ((underlying R (X.obj i).unop).map) (F.map_id i)
    rw [Functor.map_comp, underlying_diagram_idIso_hom, CategoryTheory.Functor.map_id] at h
    exact h
  map_comp a b := by
    have h := congrArg ((underlying R (X.obj _).unop).map) (F.map_comp a b)
    rw [Functor.map_comp, underlying_diagram_compIso_hom, Functor.map_comp] at h
    exact h

/-- Morphisms retain their original components after forgetting scalars. -/
def underlyingSystemHom {F G : DiagramCoefficientSystem R X}
    (a : InjectiveSystem.System.Hom (diagramAdjunctionData R X) F G) :
    InjectiveSystem.System.Hom (Continuity.diagramAdjunctionData X)
      (underlyingSystem R X F) (underlyingSystem R X G) where
  app i := (underlying R (X.obj i).unop).map (a.app i)
  naturality f := by
    exact congrArg ((underlying R (X.obj _).unop).map) (a.naturality f)

/-- The native pullback comparison respects the original adjunction unit. -/
@[reassoc]
theorem inverseImageUnderlyingIso_unit {X S : Scheme.{u}} (f : S ⟶ X)
    (F : Coefficient R X) :
    (underlying R X).map ((imageAdjunction R f).unit.app F) ≫
      (EtaleCohomology.directImage f).map
        ((ModuleCat.Sheaf.pullbackUnderlyingIso R (siteBaseChange f)
          X.smallEtaleTopology S.smallEtaleTopology).hom.app F) =
    (inverseImageAdjunction f).unit.app ((underlying R X).obj F) :=
  ModuleCat.Sheaf.pullbackUnderlyingIso_unit R (siteBaseChange f)
    X.smallEtaleTopology S.smallEtaleTopology F

/-- The original adjunction transposes the same module arrow after forgetting scalars. -/
theorem underlying_homEquiv {X S : Scheme.{u}} (f : S ⟶ X)
    (M : Coefficient R X) (N : Coefficient R S)
    (a : (inverseImage R f).obj M ⟶ N) :
    (underlying R X).map ((imageAdjunction R f).homEquiv M N a) =
      (inverseImageAdjunction f).homEquiv ((underlying R X).obj M) ((underlying R S).obj N)
        ((ModuleCat.Sheaf.pullbackUnderlyingIso R (siteBaseChange f)
          X.smallEtaleTopology S.smallEtaleTopology).inv.app M ≫ (underlying R S).map a) :=
  ModuleCat.Sheaf.pullbackUnderlyingIso_homEquiv R (siteBaseChange f)
    X.smallEtaleTopology S.smallEtaleTopology M N a

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
