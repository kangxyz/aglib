/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction.Insertion

/-!
# The same normal insertion through an actual normal-frame map

An actual normal map preserving the original unit frame transports the
original tensor unitor. If the same determinant is transported through
that map, its insertion arrow is unchanged. This applies in particular
to the genuine exterior-degree transport.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem tensorToUnit_comp {X : Scheme.{u}} {L M : X.Modules}
    (f : L ⟶ M) (g : M ⟶ SheafOfModules.unit X.ringCatSheaf) (N : X.Modules) :
    (tensorToUnit (f ≫ g)).app N =
      (moduleTensorCoefficientMap X f).app N ≫ (tensorToUnit g).app N := by
  change (((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).map (f ≫ g)).app N) ≫
      (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).hom.app N = _
  rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rfl

private theorem frameInsertion_change {C : Type*} [Category C]
    {N N' Q P : C} (a : N ≅ Q) (a' : N' ≅ Q) (Δ : N ≅ P) (Δ' : N' ≅ P)
    (n : N ⟶ N') (hA : n ≫ a'.hom = a.hom) (hΔ : Δ.hom = n ≫ Δ'.hom) :
    a.symm ≪≫ Δ = a'.symm ≪≫ Δ' := by
  have hi : a.inv ≫ n = a'.inv := by
    apply (cancel_mono a'.hom).mp
    have h := congrArg (fun z => a.inv ≫ z) hA
    simpa only [Category.assoc, Iso.inv_hom_id] using h
  apply Iso.ext
  change a.inv ≫ Δ.hom = a'.inv ≫ Δ'.hom
  rw [hΔ, ← Category.assoc, hi]

/-- Preserving the same normal frame and the same determinant preserves the actual insertion.
No separate invertibility premise on the normal arrow is used. -/
theorem normalDeterminantInsertionIso_changeNormal
    {X : Scheme.{u}} (C C' : LineBundle X)
    (eC : C.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (eC' : C'.val ≅ SheafOfModules.unit X.ringCatSheaf)
    {Q P : X.Modules} (Δ : tensorSheaf X C.val Q ≅ P)
    (Δ' : tensorSheaf X C'.val Q ≅ P) (n : C.val ⟶ C'.val)
    (hFrame : n ≫ eC'.hom = eC.hom)
    (hΔ : Δ.hom = (moduleTensorCoefficientMap X n).app Q ≫ Δ'.hom) :
    normalDeterminantInsertionIso C eC Δ = normalDeterminantInsertionIso C' eC' Δ' := by
  let a := ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso eC).app Q ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app Q
  let a' := ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso eC').app Q ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app Q
  have hA : (moduleTensorCoefficientMap X n).app Q ≫ a'.hom = a.hom :=
    (tensorToUnit_comp n eC'.hom Q).symm.trans
      (congrArg (fun f => (tensorToUnit f).app Q) hFrame)
  exact frameInsertion_change a a' Δ Δ' ((moduleTensorCoefficientMap X n).app Q) hA hΔ

/-- Transporting the normal frame and its determinant through the same actual isomorphism
leaves the ordinary insertion arrow unchanged. -/
theorem normalDeterminantInsertionIso_transportNormal
    {X : Scheme.{u}} (C C' : LineBundle X)
    (eC : C.val ≅ SheafOfModules.unit X.ringCatSheaf) (n : C.val ≅ C'.val)
    {Q P : X.Modules} (Δ' : tensorSheaf X C'.val Q ≅ P) :
    normalDeterminantInsertionIso C eC
        (((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso n).app Q ≪≫ Δ') =
      normalDeterminantInsertionIso C' (n.symm ≪≫ eC) Δ' := by
  apply normalDeterminantInsertionIso_changeNormal C C' eC (n.symm ≪≫ eC) _ Δ' n.hom
  · exact n.hom_inv_id_assoc eC.hom
  · rfl

end AlgebraicGeometry.Scheme.Modules
