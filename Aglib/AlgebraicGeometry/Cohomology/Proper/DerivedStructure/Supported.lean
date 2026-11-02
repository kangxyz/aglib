/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.Surface
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Stalk.Structure

/-!
# Original first higher image of a supported local modification

The original local-spectrum Cartesian square identifies the centre stalk
of R1 with the SAME local structure H1. The unchanged complement kills the
other actual stalks. This is the original proof extracted from the point-
blowup derived-unit consumer, without a blowup or surface hypothesis on
this first-higher-image argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

local instance supportedStructureDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The SAME local H1 and actual unchanged complement kill the original R1.
Properness, integrality, normality, Noetherianity and dimension are not needed
for this supported first-higher-image statement. -/
theorem firstHigherImage_isZero_of_localStructureH1_of_isIso_complement
    {X Y T : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (x : X) (hx : IsClosed ({x} : Set X))
    (a : T ⟶ Y) (p : T ⟶ Spec (X.presheaf.stalk x))
    (H : IsPullback a p f (X.fromSpecStalk x))
    (hU : IsIso (f ∣_ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)))
    (hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf T (SheafOfModules.unit T.ringCatSheaf)) 1)) :
    IsZero (((pushforward f).rightDerived 1).obj
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)) := by
  classical
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let : O.IsQuasicoherent := isQuasicoherent_unit Y
  let R1 := ((pushforward f).rightDerived 1).obj O
  apply (isZero_iff_stalks R1).mpr
  intro y
  by_cases hy : y = x
  · subst y
    let OT : T.Modules := SheafOfModules.unit T.ringCatSheaf
    let α := p.appTop.hom.comp (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom
    let := moduleCohomologyModuleOfHom T α OT 1
    let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf T OT) 1) := hH
    let e := originalStructureH1StalkLinearEquiv f x a p H
    let : Subsingleton ((moduleStalk X x).obj R1) := e.injective.subsingleton
    have hz : IsZero ((moduleStalk X x).obj R1) := ModuleCat.isZero_of_subsingleton _
    exact ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero hz).of_iso
      ((moduleStalkForgetIso X x).app R1).symm
  · let U : X.Opens := ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩
    let : IsIso (f ∣_ U) := hU
    exact higherImage_stalk_isZero_on_isomorphism_open f O U y hy 0

end AlgebraicGeometry.Scheme.Cohomology
