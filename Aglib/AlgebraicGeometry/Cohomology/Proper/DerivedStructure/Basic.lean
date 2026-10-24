/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Original structural derived units and native degree-zero normalization

The actual structural section map and the installed derived single unit
supply the original derived structure object and its degree-zero equations.
The analogous literal structure-module coefficient arrow defines the native
pushforward unit. These constructions require no geometric finiteness.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

/-- The standard derived category of module sheaves for the original structural units. -/
local instance derivedStructureBasicSource (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _

/-- The standard derived category of `R`-modules for structural global sections. -/
local instance derivedStructureBasicTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- The actual structural map on the original whole-space section carrier. -/
def moduleStructuralSectionsMap : ModuleCat.of R R ⟶
    (moduleGlobalSectionsFunctorOfHom X α).obj (SheafOfModules.unit X.ringCatSheaf) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let N : ModuleCat.{u} R := (moduleGlobalSectionsFunctorOfHom X α).obj O
  let c : R →ₗ[R] N := {
    toFun := fun r => α r
    map_add' := α.map_add
    map_smul' := fun r s => by
      change α (r * s) = α r * α s
      exact α.map_mul r s }
  exact ModuleCat.ofHom (X := R) (Y := N) c

/-- Evaluation of the actual structural map is the original ring homomorphism. -/
theorem moduleStructuralSectionsMap_apply (r : R) :
    moduleStructuralSectionsMap X α r = α r := rfl

private theorem normalized_unit_paste
    {C : Type*} [Category C] {N A B D P : C}
    (eN : A ≅ N) (eP : B ≅ P) (e₀ : D ≅ P)
    (c : N ⟶ P) (v : A ⟶ B) (w : B ⟶ D) (z : A ⟶ D)
    (hc : eN.inv ≫ v = c ≫ eP.inv) (hw : eP.inv ≫ w = e₀.inv)
    (hz : z = v ≫ w) : eN.inv ≫ z ≫ e₀.hom = c := by
  calc
    _ = eN.inv ≫ (v ≫ w) ≫ e₀.hom := by rw [hz]
    _ = (eN.inv ≫ v) ≫ w ≫ e₀.hom := by simp only [Category.assoc]
    _ = (c ≫ eP.inv) ≫ w ≫ e₀.hom := by rw [hc]
    _ = c ≫ (eP.inv ≫ w) ≫ e₀.hom := by simp only [Category.assoc]
    _ = c ≫ e₀.inv ≫ e₀.hom := by rw [hw]
    _ = c := by rw [e₀.inv_hom_id, Category.comp_id]

private theorem isIso_of_iso_normalization
    {C : Type*} [Category C] {N A D P : C}
    (eN : A ≅ N) (e₀ : D ≅ P) (c : N ⟶ P) (z : A ⟶ D) [IsIso c]
    (h : eN.inv ≫ z ≫ e₀.hom = c) : IsIso z := by
  have : IsIso (eN.inv ≫ z ≫ e₀.hom) := by rw [h]; infer_instance
  have : IsIso (z ≫ e₀.hom) := IsIso.of_isIso_comp_left eN.inv (z ≫ e₀.hom)
  exact IsIso.of_isIso_comp_right z e₀.hom

private theorem module_comp_apply_eq
    {A B C D : ModuleCat.{u} R} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : A ⟶ D)
    (h : a ≫ b ≫ c = d) (x : A) : c (b (a x)) = d x := by
  have h' := congrArg (fun k : A ⟶ D => k x) h
  simpa only [ModuleCat.comp_apply] using h'

/-- The installed bounded-below derived global sections of the original structure module. -/
def moduleDerivedStructure : DerivedCategory.Plus (ModuleCat.{u} R) :=
  (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf))

/-- The literal structural section map followed by the existing native derived single unit. -/
def moduleDerivedStructureUnit :
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) ⟶
      moduleDerivedStructure X α :=
  (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
      (moduleStructuralSectionsMap X α) ≫
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleUnit
      (SheafOfModules.unit X.ringCatSheaf)

/-- The original left-exact H0 comparison sends the actual derived unit to
the literal structural map on sections. -/
theorem moduleDerivedStructureUnit_homology :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app
        (ModuleCat.of R R) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (moduleDerivedStructureUnit X α) ≫
      (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.hom.app
        (SheafOfModules.unit X.ringCatSheaf) = moduleStructuralSectionsMap X α := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let c := moduleStructuralSectionsMap X α
  have hc := E.inv.naturality c
  change c ≫ E.inv.app (F.obj O) = E.inv.app (ModuleCat.of R R) ≫ H.map (S.map c) at hc
  exact normalized_unit_paste (E.app (ModuleCat.of R R)) (E.app (F.obj O))
    (F.rightDerivedSingleHomologyZeroIso.app O) c (H.map (S.map c))
    (H.map (F.rightDerivedSingleUnit O)) (H.map (S.map c ≫ F.rightDerivedSingleUnit O))
    hc.symm (F.rightDerivedSingleUnit_homology_zero O) (H.map_comp _ _)

/-- Evaluation of the H0 equation retains every original scalar. -/
theorem moduleDerivedStructureUnit_homology_apply (r : R) :
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.hom.app
        (SheafOfModules.unit X.ringCatSheaf)
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (moduleDerivedStructureUnit X α)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app
            (ModuleCat.of R R) r)) = α r := by
  exact (module_comp_apply_eq _ _ _ _ (moduleDerivedStructureUnit_homology X α) r).trans
    (moduleStructuralSectionsMap_apply X α r)

/-- Bijectivity of the actual structural sections map makes H0 of the
same derived unit invertible. -/
theorem isIso_moduleDerivedStructureUnit_homology_of_bijective
    (hα : Function.Bijective α) :
    IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      (moduleDerivedStructureUnit X α)) := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let η := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
    (moduleDerivedStructureUnit X α)
  let c := moduleStructuralSectionsMap X α
  have hc : Function.Bijective c := by
    constructor
    · intro r s h
      apply hα.1
      exact (moduleStructuralSectionsMap_apply X α r).symm.trans
        (h.trans (moduleStructuralSectionsMap_apply X α s))
    · intro s
      obtain ⟨r, hr⟩ := hα.2 s
      exact ⟨r, (moduleStructuralSectionsMap_apply X α r).trans hr⟩
  let : IsIso c := (ConcreteCategory.isIso_iff_bijective _).mpr hc
  exact isIso_of_iso_normalization (E.app (ModuleCat.of R R))
    (F.rightDerivedSingleHomologyZeroIso.app O) c η
    (moduleDerivedStructureUnit_homology X α)

/-- The original structure-module map followed by the installed native
derived pushforward unit. -/
def moduleDerivedPushforwardUnit {Y : Scheme.{u}} (g : Y ⟶ X) :
    (DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
          (SheafOfModules.unit Y.ringCatSheaf)) :=
  (DerivedCategory.Plus.singleFunctor X.Modules 0).map
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforward g).rightDerivedSingleUnit
      (SheafOfModules.unit Y.ringCatSheaf)

end AlgebraicGeometry.Scheme.Cohomology
