/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Evaluation
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Mathlib.Algebra.Homology.Additive
/-!
# Original sections under open restriction and trivialization

The original restriction section isomorphism preserves sheaf arrows and extends to
actual cochain complexes. Unit and trivialized section identifications agree with
the genuine geometric ring-section maps. No affineness or acyclicity is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules

section
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original sections of a restricted sheaf equal sections on the image open,
with naturality in the sheaf retained. -/
def restrictedSectionsIso :
    Scheme.Modules.restrictFunctor j ⋙ SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤) ≅
      SheafOfModules.additiveEvaluation X.ringCatSheaf (op j.opensRange) := by
  refine NatIso.ofComponents (fun M => M.restrictAppIso j ⊤ ≪≫
    M.presheaf.mapIso (eqToIso j.image_top_eq_opensRange.symm).op) ?_
  intro M N f
  change f.app (j ''ᵁ ⊤) ≫
      N.presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op =
    M.presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op ≫ f.app j.opensRange
  exact (f.mapPresheaf.naturality (eqToHom j.image_top_eq_opensRange.symm).op).symm

/-- The cochain isomorphism between actual restricted sections and original
sections on the open image. -/
def restrictedSectionsComplexIso (I : CochainComplex X.Modules ℕ) :
    ((SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)).mapHomologicalComplex _).obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex _).obj I) ≅
      ((SheafOfModules.additiveEvaluation X.ringCatSheaf (op j.opensRange)).mapHomologicalComplex
        _).obj I := by
  letI : @Functor.PreservesZeroMorphisms U.Modules inferInstance
      AddCommGrpCat.{u} inferInstance inferInstance inferInstance
      (SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)) := by
    exact SheafOfModules.additiveEvaluation_preservesZeroMorphisms U.ringCatSheaf (op ⊤)
      (sourceZero := (inferInstance : HasZeroMorphisms U.Modules))
      (targetZero := (inferInstance : HasZeroMorphisms AddCommGrpCat.{u}))
  letI : @Functor.PreservesZeroMorphisms X.Modules inferInstance
      AddCommGrpCat.{u} inferInstance inferInstance inferInstance
      (SheafOfModules.additiveEvaluation X.ringCatSheaf (op j.opensRange)) := by
    exact SheafOfModules.additiveEvaluation_preservesZeroMorphisms
      X.ringCatSheaf (op j.opensRange)
      (sourceZero := (inferInstance : HasZeroMorphisms X.Modules))
      (targetZero := (inferInstance : HasZeroMorphisms AddCommGrpCat.{u}))
  exact (Functor.mapHomologicalComplexCompIso (restrictedSectionsIso j) (.up ℕ)).app I

end

/-- Unit sheaf restriction agrees with the original ring-section identification. -/
lemma restrictedSectionsIso_inv_unit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ((restrictedSectionsIso j).app (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)).map
        (Scheme.Modules.restrictUnitIso j).hom =
    AddCommGrpCat.ofHom (IsOpenImmersion.ΓIsoTop j).inv.hom.toAddMonoidHom := by
  rfl

/-- Unit restriction is compatible with the original composition comparison. -/
lemma restrictUnitIso_comp {U V X : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctorComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.restrictFunctor f).map (Scheme.Modules.restrictUnitIso g).hom ≫
      (Scheme.Modules.restrictUnitIso f).hom = (Scheme.Modules.restrictUnitIso (f ≫ g)).hom := by
  apply Scheme.Modules.hom_ext
  intro O
  ext x
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorComp_hom_app_app]
  change ((X.presheaf.map (eqToHom _).op ≫ (g.appIso (f ''ᵁ O)).hom ≫
    (f.appIso O).hom).hom x) = ((f ≫ g).appIso O).hom.hom x
  simp only [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_comp_appLE]

/-- Original sections on an open image in a specified actual trivialization. -/
def trivializedOpenSectionsIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (e : M.restrict j ≅ SheafOfModules.unit U.ringCatSheaf) :
    Γ(M, j.opensRange) ≅ AddCommGrpCat.of Γ(U, ⊤) :=
  ((restrictedSectionsIso j).app M).symm ≪≫
    (SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)).mapIso e

/-- A trivialization arising from a global sheaf arrow retains that arrow on sections. -/
lemma trivializedOpenSectionsIso_hom {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (e : M.restrict j ≅ SheafOfModules.unit U.ringCatSheaf)
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hφ : (Scheme.Modules.restrictFunctor j).map φ ≫
      (Scheme.Modules.restrictUnitIso j).hom = e.hom) :
    (trivializedOpenSectionsIso j M e).hom =
      φ.app j.opensRange ≫ AddCommGrpCat.ofHom
        (IsOpenImmersion.ΓIsoTop j).inv.hom.toAddMonoidHom := by
  change ((restrictedSectionsIso j).app M).inv ≫
    (SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)).map e.hom = _
  rw [← hφ, Functor.map_comp, ← Category.assoc]
  erw [← (restrictedSectionsIso j).inv.naturality φ]
  rw [Category.assoc]
  exact congrArg (fun k => φ.app j.opensRange ≫ k) (restrictedSectionsIso_inv_unit j)

/-- Restricting a global arrow into the unit sheaf preserves its original section map. -/
lemma restrictedSectionsIso_inv_map_unit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    φ.app j.opensRange ≫ AddCommGrpCat.ofHom
        (IsOpenImmersion.ΓIsoTop j).inv.hom.toAddMonoidHom =
      ((restrictedSectionsIso j).app M).inv ≫
        (SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)).map
        ((Scheme.Modules.restrictFunctor j).map φ ≫
          (Scheme.Modules.restrictUnitIso j).hom) := by
  rw [Functor.map_comp, ← Category.assoc]
  erw [← (restrictedSectionsIso j).inv.naturality φ]
  rw [Category.assoc]
  exact (congrArg (fun k => φ.app j.opensRange ≫ k) (restrictedSectionsIso_inv_unit j)).symm


end AlgebraicGeometry.Scheme.Modules
