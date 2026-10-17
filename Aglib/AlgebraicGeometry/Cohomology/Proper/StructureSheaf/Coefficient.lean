/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Stability

/-!
# The structure module as a coherent relatively flat coefficient

The actual structure module `SheafOfModules.unit X.ringCatSheaf` is finitely
presented by its native free-on-one presentation, hence affine-locally of
finite type on every scheme. Its actual module stalks corepresent the same
membership functor as a free module of rank one, so they are flat over the
local rings of the source; for a flat morphism `f`, transitivity of flatness
over `f.stalkMap x` gives `Scheme.Modules.relativeFlat f` of the structure
module. No Noetherianity, quasicompactness or properness is assumed.

These are the coefficient inputs of the proper local criterion for the
structure sheaf. Intended owners: the finite-type statements belong with
`Modules/QuasiCoherent/FiniteType`, the stalk statements with `Modules/Flat`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The structure module is finitely presented by its native free-on-one presentation. -/
theorem unit_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation := by
  let M : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}
  let q : M.LocalGeneratorsData.{u} :=
    (SheafOfModules.free.generatingSections (R := X.ringCatSheaf)
      PUnit.{u + 1}).localGeneratorsData
  have : q.IsLocallyFreeData := inferInstanceAs
    ((SheafOfModules.free.generatingSections (R := X.ringCatSheaf)
      PUnit.{u + 1}).localGeneratorsData.IsLocallyFreeData)
  have : ∀ i, Finite (q.generators i).I := fun _ => inferInstanceAs (Finite PUnit.{u + 1})
  have hM : M.IsFinitePresentation :=
    Scheme.Cohomology.finitePresentation_of_finite_local_basis X M q
  let e : M ≅ SheafOfModules.unit X.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e hM

/-- The structure module is affine-locally quasicoherent of finite type on every scheme. -/
theorem affineLocallyFiniteType_unit (X : Scheme.{u}) :
    QuasiCoherent.affineLocallyFiniteType X (SheafOfModules.unit X.ringCatSheaf) := by
  have := unit_isFinitePresentation X
  exact QuasiCoherent.affineLocallyFiniteType_of_finitePresentation _

/-- Stalks of the actual structure module corepresent membership sections on the whole
space, through the original stalk/skyscraper adjunction and unit-Hom comparison. -/
def unitStalkCorepresentable (X : Scheme.{u}) (x : X) :
    (pointOpenSections X x ⊤).CorepresentableBy
      ((moduleStalk X x).obj (SheafOfModules.unit X.ringCatSheaf)) where
  homEquiv := ((moduleStalkSkyscraperAdjunction X x).homEquiv _ _).trans
    (unitHomGlobalSectionsEquiv X _)
  homEquiv_comp p q := by
    dsimp
    erw [Adjunction.homEquiv_naturality_right, unitHomGlobalSectionsEquiv_naturality]

/-- The actual stalk of the structure module is free of rank one over the local ring. -/
def unitStalkIso (X : Scheme.{u}) (x : X) :
    (moduleStalk X x).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (PLift (x ∈ (⊤ : X.Opens)))) :=
  (unitStalkCorepresentable X x).uniqueUpToIso (freePointOpenCorepresentable X x ⊤)

/-- The actual stalks of the structure module are flat over the local rings. -/
instance unit_stalk_flat (X : Scheme.{u}) (x : X) :
    Module.Flat (X.presheaf.stalk x)
      ((moduleStalk X x).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  let : Module.Flat (X.presheaf.stalk x)
      ((ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (PLift (x ∈ (⊤ : X.Opens))))) :=
    inferInstanceAs (Module.Flat (X.presheaf.stalk x)
      (ULift.{u} (PLift (x ∈ (⊤ : X.Opens))) →₀ X.presheaf.stalk x))
  exact Module.Flat.of_linearEquiv ((unitStalkIso X x).toLinearEquiv)

/-- For a flat morphism, the structure module is relatively flat: its stalks are flat over
the base local rings through the original `stalkMap`. -/
theorem relativeFlat_unit_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    relativeFlat f (SheafOfModules.unit X.ringCatSheaf) := by
  intro x
  let φ := (f.stalkMap x).hom
  let := φ.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  let N := (moduleStalk X x).obj (SheafOfModules.unit X.ringCatSheaf)
  let : Module (Y.presheaf.stalk (f x)) N := Module.compHom N φ
  have : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) N :=
    ⟨fun a b n => by
      change (φ a * b) • n = φ a • (b • n)
      rw [mul_smul]⟩
  exact Module.Flat.trans (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) N

end AlgebraicGeometry.Scheme.Modules
