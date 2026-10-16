/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.FiniteCoefficients

/-! # Naturality of the original finite Cech coefficient comparison

The forward finite Cech comparisons commute with a natural transformation between
additive finite-product-preserving coefficient functors. The equation uses the
native map on homological complexes and the original product projections. All
category, product, and finite-index universes remain independent.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace CategoryTheory.Cech
universe w v v' v'' u u' u''
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
  {B : Type u''} [Category.{v''} B] [HasProducts.{w} B] [Preadditive B]
  (F G : A ⥤ B) [F.Additive] [G.Additive]
  [PreservesFiniteProducts F] [PreservesFiniteProducts G]
  (τ : F ⟶ G) {ι : Type w} [Finite ι] (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- The original finite Cech forward comparison is natural in its coefficient functor. -/
theorem finiteCechComplexCoefficientIso_naturality_functor :
    (NatTrans.mapHomologicalComplex τ (.up ℕ)).app ((cechComplexFunctor U).obj P) ≫
      (finiteCechComplexCoefficientIso G U P).hom =
    (finiteCechComplexCoefficientIso F U P).hom ≫
      (cechComplexFunctor U).map (Functor.whiskerLeft P τ) := by
  ext q : 2
  apply Pi.hom_ext
  intro a
  simp only [comp_f, NatTrans.mapHomologicalComplex_app_f]
  change (τ.app (∏ᶜ fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k)))) ≫
      (𝟙 _ ≫ piComparison G
        (fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k)))))) ≫
          Pi.π (fun a : Fin (q + 1) → ι => G.obj (P.obj (op (∏ᶜ fun k => U (a k))))) a =
    ((𝟙 _ ≫ piComparison F
      (fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k))))) ≫
      Limits.Pi.map (fun a : Fin (q + 1) → ι => τ.app (P.obj (op (∏ᶜ fun k => U (a k)))))) ≫
        Pi.π (fun a : Fin (q + 1) → ι => G.obj (P.obj (op (∏ᶜ fun k => U (a k))))) a
  simp only [Category.id_comp, Category.assoc, Pi.map_π]
  rw [piComparison_comp_π, ← Category.assoc, piComparison_comp_π]
  exact (τ.naturality
    (Pi.π (fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k)))) a)).symm

end CategoryTheory.Cech
