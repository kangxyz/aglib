/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction.Insertion

/-!
# Restriction of the same normal insertion

The original tensor restriction and structure-module unit comparisons
carry a genuine normal-frame square to a square of the original tensor
unitors. An actual determinant square then gives the same insertion
square. Normal maps need not be separately assumed invertible.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
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

private theorem insertionSquare
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {T Q P : C} {T' Q' P' : D} (a : T ≅ Q) (a' : T' ≅ Q')
    (Δ : T ≅ P) (Δ' : T' ≅ P') (k : F.obj T ⟶ T')
    (f : F.obj Q ⟶ Q') (g : F.obj P ⟶ P')
    (hA : k ≫ a'.hom = F.map a.hom ≫ f)
    (hΔ : F.map Δ.hom ≫ g = k ≫ Δ'.hom) :
    F.map (a.symm ≪≫ Δ).hom ≫ g = f ≫ (a'.symm ≪≫ Δ').hom := by
  have hi : F.map a.inv ≫ k = f ≫ a'.inv := by
    apply (cancel_mono a'.hom).mp
    have ht := congrArg (fun z => F.map a.inv ≫ z) hA
    change F.map a.inv ≫ (k ≫ a'.hom) =
      (F.mapIso a).inv ≫ ((F.mapIso a).hom ≫ f) at ht
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using ht
  simp only [Iso.trans_hom, Iso.symm_hom, F.map_comp, Category.assoc]
  rw [hΔ, ← Category.assoc, hi, Category.assoc]

/-- Actual normal-frame and determinant squares preserve the same original insertion arrow. -/
theorem normalDeterminantInsertionIso_restrict
    {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    (C : LineBundle X) (C' : LineBundle X')
    (eC : C.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (eC' : C'.val ≅ SheafOfModules.unit X'.ringCatSheaf)
    {Q P : X.Modules} {Q' P' : X'.Modules}
    (Δ : tensorSheaf X C.val Q ≅ P) (Δ' : tensorSheaf X' C'.val Q' ≅ P')
    (aC : (restrictFunctor j).obj C.val ⟶ C'.val)
    (aQ : (restrictFunctor j).obj Q ⟶ Q') (bP : (restrictFunctor j).obj P ⟶ P')
    (hC : (restrictFunctor j).map eC.hom ≫ (restrictUnitIso j).hom = aC ≫ eC'.hom)
    (hΔ : (restrictFunctor j).map Δ.hom ≫ bP =
      (tensorRestrictionIso j C.val Q).inv ≫
        (moduleTensorCoefficientMap X' aC).app (Q.restrict j) ≫
        (moduleTensorLeftFunctor X' C'.val).map aQ ≫ Δ'.hom) :
    (restrictFunctor j).map (normalDeterminantInsertionIso C eC Δ).hom ≫ bP =
      aQ ≫ (normalDeterminantInsertionIso C' eC' Δ').hom := by
  let F := restrictFunctor j
  let S := tensorRestrictionIso j C.val Q
  let a := ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso eC).app Q ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app Q
  let a' := ((SheafOfModulesOfCommRing.tensorFunctor X'.sheaf).mapIso eC').app Q' ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso X'.sheaf).app Q'
  let k := S.inv ≫ (moduleTensorCoefficientMap X' aC).app (Q.restrict j) ≫
    (moduleTensorLeftFunctor X' C'.val).map aQ
  have hu := tensorToUnit_restrict j eC.hom Q
  have hn := (tensorToUnit eC'.hom).naturality aQ
  have h₀ : S.hom ≫ F.map a.hom ≫ aQ =
      (moduleTensorCoefficientMap X' aC).app (Q.restrict j) ≫
        (moduleTensorLeftFunctor X' C'.val).map aQ ≫ a'.hom := by
    calc
      _ = (tensorToUnit (F.map eC.hom ≫ (restrictUnitIso j).hom)).app (Q.restrict j) ≫ aQ :=
        congrArg (fun z => z ≫ aQ) hu
      _ = (tensorToUnit (aC ≫ eC'.hom)).app (Q.restrict j) ≫ aQ :=
        congrArg (fun z => (tensorToUnit z).app (Q.restrict j) ≫ aQ) hC
      _ = (moduleTensorCoefficientMap X' aC).app (Q.restrict j) ≫
          ((tensorToUnit eC'.hom).app (Q.restrict j) ≫ aQ) := by
        rw [tensorToUnit_comp, Category.assoc]
      _ = _ := congrArg (fun z => (moduleTensorCoefficientMap X' aC).app
        (Q.restrict j) ≫ z) hn.symm
  have hA : k ≫ a'.hom = F.map a.hom ≫ aQ := by
    have ht := congrArg (fun z => S.inv ≫ z) h₀
    simpa only [k, Category.assoc, Iso.inv_hom_id_assoc] using ht.symm
  exact insertionSquare F a a' Δ Δ' k aQ bP hA hΔ

end AlgebraicGeometry.Scheme.Modules
