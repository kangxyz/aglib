/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Preadditive.ScalarDiagram

/-! # Original coefficient transformations preserve the actual scalar diagram

Naturality in the entire coefficient functor supplies left linearity for an
arbitrary ring. Naturality only in module-linear coefficient maps is not used
as a substitute for this stronger hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace CategoryTheory.Functor
universe u v i j w r
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {I : Type i} [Category.{j} I]
  {H K : C ⥤ I ⥤ AddCommGrpCat.{w}} [H.Additive] [K.Additive]
  {R : Type r} [Ring R] (A : C) (ρ : R →+* End A)

/-- The entire original coefficient transformation is left-linear on each unchanged value. -/
def coefficientModuleDiagramNatTrans (α : H ⟶ K) :
    H.coefficientModuleDiagram A ρ ⟶ K.coefficientModuleDiagram A ρ where
  app i := ModuleCat.ofHom
    (X := (H.coefficientModuleDiagram A ρ).obj i)
    (Y := (K.coefficientModuleDiagram A ρ).obj i)
    { __ := ((α.app A).app i).hom
      map_smul' := by
        intro a x
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (α.naturality (ρ a)) i) x }
  naturality i j f := by
    apply (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).map_injective
    exact (α.app A).naturality f

/-- Forgetting scalars returns the original component map exactly. -/
theorem coefficientModuleDiagramNatTrans_apply (α : H ⟶ K) (i : I)
    (x : (H.coefficientModuleDiagram A ρ).obj i) :
    (coefficientModuleDiagramNatTrans A ρ α).app i x = (α.app A).app i x := rfl

/-- An original coefficient isomorphism gives the original scalar-compatible isomorphism. -/
def coefficientModuleDiagramNatIso (α : H ≅ K) :
    H.coefficientModuleDiagram A ρ ≅ K.coefficientModuleDiagram A ρ where
  hom := coefficientModuleDiagramNatTrans A ρ α.hom
  inv := coefficientModuleDiagramNatTrans A ρ α.inv
  hom_inv_id := by
    ext i x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (α.hom_inv_id_app A) i) x
  inv_hom_id := by
    ext i x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (α.inv_hom_id_app A) i) x

end CategoryTheory.Functor
