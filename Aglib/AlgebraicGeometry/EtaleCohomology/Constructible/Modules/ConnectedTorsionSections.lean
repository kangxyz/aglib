/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Images
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedTorsionSections

/-! # Original constant module sections on a connected qcqs scheme

The original module constant-adjunction unit is an isomorphism for additive
torsion values, including values infinite as abelian groups. Its comparison
with the original abelian unit retains the original module structure.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  ModuleCat.Sheaf.forget_preservesSheafification

variable (R : Type r) [CommRing R]

/-- Original global sections with the original constant-ring module structure. -/
abbrev moduleGlobalSections (X : Scheme.{u}) : ModuleSheaf R X ⥤ ModuleCat.{u + 1} R :=
  (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op (etaleTerminal X))

/-- The original native module constant/sections adjunction. -/
abbrev moduleConstantAdjunction (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⊣ moduleGlobalSections R X :=
  constantSheafAdj _ _ (etaleTerminalIsTerminal X)

/-- The original module unit becomes the original abelian unit under the native
constant-sheaf comparison. -/
theorem moduleConstantUnit_underlying (X : Scheme.{u}) (M : ModuleCat.{u + 1} R) :
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
        ((moduleConstantAdjunction R X).unit.app M) ≫
      ((moduleConstantUnderlyingIso R X).hom.app M).hom.app (op (etaleTerminal X)) =
        (constantAdjunction X).unit.app
          ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj M) := by
  let J := X.smallEtaleTopology
  let V := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  have h : Functor.whiskerRight (toSheafify J ((Functor.const X.Etaleᵒᵖ).obj M)) V ≫
      ((constantCommuteCompose J V).hom.app M).hom =
        (Functor.constComp X.Etaleᵒᵖ M V).hom ≫
          toSheafify J ((Functor.const X.Etaleᵒᵖ).obj (V.obj M)) := by
    rw [constantCommuteCompose_hom_app_hom, sheafComposeIso_inv_fac_assoc,
      ← toSheafify_naturality]
  simp only [moduleConstantAdjunction, constantAdjunction, constantSheafAdj,
    Adjunction.comp_unit_app, constantPresheafAdj_unit_app, Category.id_comp]
  change V.map ((toSheafify J ((Functor.const X.Etaleᵒᵖ).obj M)).app
      (op (etaleTerminal X))) ≫ ((constantCommuteCompose J V).hom.app M).hom.app
      (op (etaleTerminal X)) =
        (toSheafify J ((Functor.const X.Etaleᵒᵖ).obj (V.obj M))).app
          (op (etaleTerminal X))
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.constComp_hom_app,
    Category.id_comp] using congrArg (fun t => t.app (op (etaleTerminal X))) h

/-- No finite underlying value is required: torsion suffices on a connected qcqs scheme. -/
theorem moduleConstantUnit_isIso_of_isAddTorsion
    (X : Scheme.{u}) [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    (M : ModuleCat.{u + 1} R) (hM : IsAddTorsion M) :
    IsIso ((moduleConstantAdjunction R X).unit.app M) := by
  let V := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let η := (moduleConstantAdjunction R X).unit.app M
  let c := (globalSections X).mapIso ((moduleConstantUnderlyingIso R X).app M)
  have hη : IsIso ((constantAdjunction X).unit.app (V.obj M)) :=
    constantUnit_isIso_of_isAddTorsion X (V.obj M) hM
  have hcomp : IsIso (V.map η ≫ c.hom) := by
    rw [show V.map η ≫ c.hom = _ from moduleConstantUnit_underlying R X M]
    exact hη
  let hc : IsIso c.hom := c.isIso_hom
  have : IsIso (V.map η) := IsIso.of_isIso_comp_right _ c.hom
  exact isIso_of_reflects_iso η V

/-- The actual module unit identifies the literal value with its constant sections. -/
def moduleConstantSectionsIso
    (X : Scheme.{u}) [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    (M : ModuleCat.{u + 1} R) (hM : IsAddTorsion M) :
    M ≅ (moduleGlobalSections R X).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) := by
  let := moduleConstantUnit_isIso_of_isAddTorsion R X M hM
  exact asIso ((moduleConstantAdjunction R X).unit.app M)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
