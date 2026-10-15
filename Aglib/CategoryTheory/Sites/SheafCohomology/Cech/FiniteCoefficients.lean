/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison

/-!
# Finite-family Cech coefficient comparison

Finite Cech products commute with finite-product-preserving coefficient
functors. The cochain comparison retains all source, morphism and coefficient
universes and only asks for finite product preservation. There is no scheme,
field, topology, covering or cohomology-finiteness hypothesis.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.CechBaseChange` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. The FiniteCoefficients section: two coefficient
  isomorphisms and their original universes/assumptions.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace CategoryTheory.Cech

section FiniteCoefficients
universe w v v' v'' u u' u''
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
  {B : Type u''} [Category.{v''} B] [HasProducts.{w} B]
  (F : A ⥤ B) [PreservesFiniteProducts F]
  {ι : Type w} [Finite ι] (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- Finite Cech products commute with a finite-product-preserving coefficient functor. -/
def finiteCechCosimplicialCoefficientIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P ⋙ F ≅
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj (P ⋙ F) := by
  refine NatIso.ofComponents (fun n => PreservesProduct.iso F
    (fun a : Fin (n.len + 1) → ι => P.obj (op (∏ᶜ fun i => U (a i))))) ?_
  intro n m g
  apply Limits.Pi.hom_ext
  intro a
  simp [FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    FormalCoproduct.cech, FormalCoproduct.mapPower, PreservesProduct.iso_hom, Function.comp_def,
    ← Functor.map_comp]

variable [Preadditive A] [Preadditive B] [F.Additive]
/-- The actual finite-family Cech complex commutes with additive finite-product-preserving
  coefficients. -/
def finiteCechComplexCoefficientIso :
    (F.mapHomologicalComplex _).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ F) :=
  CategoryTheory.Cech.alternatingCofaceCoefficientIso F
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P) ≪≫
      (AlgebraicTopology.alternatingCofaceMapComplex B).mapIso
        (finiteCechCosimplicialCoefficientIso F U P)

omit [Preadditive A] [Preadditive B] [F.Additive] in
/-- Under the stronger arbitrary-limit hypothesis, both interfaces use the
same original product comparison on every cosimplicial degree. -/
theorem finiteCechCosimplicialCoefficientIso_eq [PreservesLimitsOfSize.{w, w} F] :
    finiteCechCosimplicialCoefficientIso F U P = cechCosimplicialCoefficientIso F U P := rfl

/-- The finite-family cochain comparison agrees with the existing interface
when its stronger preservation hypothesis is available. -/
theorem finiteCechComplexCoefficientIso_eq [PreservesLimitsOfSize.{w, w} F] :
    finiteCechComplexCoefficientIso F U P = cechComplexCoefficientIso F U P := rfl
end FiniteCoefficients

end CategoryTheory.Cech
