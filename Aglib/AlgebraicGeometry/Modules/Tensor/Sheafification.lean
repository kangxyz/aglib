/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/LineTensorSheafification.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 117]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Actual line tensor and original module-sheafification units

Open-chart trivializations make the original tensor of a sheafification unit
invertible after sheafification. All comparison maps are the original unit,
original presheaf tensor map and original continuous/cocontinuous restriction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory AlgebraicGeometry SheafOfModulesOfCommRing
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The original module-sheafification comparison under open restriction. -/
def restrictionSheafificationIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom ⋙
        SheafOfModulesOfCommRing.associatedSheaf U.sheaf ≅
      SheafOfModulesOfCommRing.associatedSheaf X.sheaf ⋙ Scheme.Modules.restrictFunctor j :=
  SheafOfModules.sheafificationPushforwardIso
    (F := j.opensFunctor) (J := Opens.grothendieckTopology U)
    (K := Opens.grothendieckTopology X)
    (S := U.ringCatSheaf) (R := X.ringCatSheaf)
    ⟨whiskerRight (restrictionRingHom j).hom (forget₂ CommRingCat RingCat)⟩

/-- The sheafified original unit remains invertible after the actual open restriction. -/
theorem isIso_sheafified_restricted_unit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    IsIso ((SheafOfModulesOfCommRing.associatedSheaf U.sheaf).map
      ((PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).map
        ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P))) :=
  SheafOfModules.isIso_sheafification_pushforward_unit
    (F := j.opensFunctor) (J := Opens.grothendieckTopology U)
    (K := Opens.grothendieckTopology X)
    (S := U.ringCatSheaf) (R := X.ringCatSheaf)
    ⟨whiskerRight (restrictionRingHom j).hom (forget₂ CommRingCat RingCat)⟩ P

/-- A presheaf which is an actual module sheaf after open restriction has
an invertible restricted original sheafification unit before further tensoring. -/
theorem isIso_restricted_unit_of_iso_sheaf {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj)
    (M : U.Modules)
    (e : (PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).obj P ≅
      (SheafOfModulesOfCommRing.toPresheaf U.sheaf).obj M) :
    IsIso ((PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).map
      ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P)) := by
  let F := PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom
  have hη : IsIso ((SheafOfModulesOfCommRing.associatedSheafUnit U.sheaf).app (F.obj P)) :=
    (PresheafOfModules.sheafificationAdjunction
      (R := U.ringCatSheaf) (𝟙 _)).isIso_unit_app_of_iso e
  have h := SheafOfModules.sheafificationPushforwardComparison_unit
    (F := j.opensFunctor) (J := Opens.grothendieckTopology U)
    (K := Opens.grothendieckTopology X)
    (S := U.ringCatSheaf) (R := X.ringCatSheaf)
    ⟨whiskerRight (restrictionRingHom j).hom (forget₂ CommRingCat RingCat)⟩ P
  change (SheafOfModulesOfCommRing.associatedSheafUnit U.sheaf).app (F.obj P) ≫
      (SheafOfModulesOfCommRing.toPresheaf U.sheaf).map ((restrictionSheafificationIso
          j).hom.app P) =
    F.map ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P) at h
  rw [← h]
  infer_instance

/-- Actual line tensor preserves the original sheafification unit after sheafification. -/
theorem isIso_line_tensor_sheafificationUnit {X : Scheme.{u}} (L : X.Modules)
    {ι : Type v} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hc : ∀ x : X, ∃ i y, j i y = x)
    (eL : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)
    (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    IsIso ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
      ((tensorLeft ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L)).map
        ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P))) := by
  apply isIso_of_restrict_openCover Y j hc
  intro i
  let F := PresheafOfModulesOfCommRing.pushforward (restrictionRingHom (j i)).hom
  let S := SheafOfModulesOfCommRing.associatedSheaf (Y i).sheaf
  let A := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L
  let η := (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P
  let u : F.obj A ≅ (SheafOfModulesOfCommRing.toPresheaf (Y i).sheaf).obj
      (SheafOfModules.unit (Y i).ringCatSheaf) :=
    (SheafOfModulesOfCommRing.toPresheaf (Y i).sheaf).mapIso (eL i)
  let t : tensorLeft (F.obj A) ⋙ S ≅ S :=
    isoWhiskerRight ((curriedTensor _).mapIso u ≪≫ leftUnitorNatIso _) S ≪≫
      leftUnitor S
  have hη : IsIso (S.map (F.map η)) := isIso_sheafified_restricted_unit (j i) P
  have ht : IsIso (S.map ((tensorLeft (F.obj A)).map (F.map η))) :=
    (NatIso.isIso_map_iff t (F.map η)).mpr hη
  have hn := PresheafOfModulesOfCommRing.pushforwardTensorHom_naturality
    (restrictionRingHom (j i)).hom (𝟙 A) η
  simp only [CategoryTheory.Functor.map_id] at hn
  change (tensorLeft (F.obj A)).map (F.map η) ≫
      (PresheafOfModulesOfCommRing.pushforwardTensorIso
        (restrictionRingHom (j i)).hom A ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj
          ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).obj P))).hom =
    (PresheafOfModulesOfCommRing.pushforwardTensorIso
      (restrictionRingHom (j i)).hom A P).hom ≫ F.map ((tensorLeft A).map η) at hn
  have hnS := congrArg (fun f => S.map f) hn
  rw [S.map_comp, S.map_comp] at hnS
  have hcomp : IsIso (S.map (PresheafOfModulesOfCommRing.pushforwardTensorIso
      (restrictionRingHom (j i)).hom A P).hom ≫ S.map (F.map ((tensorLeft A).map η))) := by
    rw [← hnS]
    infer_instance
  have hg : IsIso (S.map (F.map ((tensorLeft A).map η))) := by
    rw [← isIso_comp_left_iff (S.map
      (PresheafOfModulesOfCommRing.pushforwardTensorIso
        (restrictionRingHom (j i)).hom A P).hom)]
    exact hcomp
  exact (NatIso.isIso_map_iff (restrictionSheafificationIso (j i))
    ((tensorLeft A).map η)).mp hg
end AlgebraicGeometry.Scheme.Modules
