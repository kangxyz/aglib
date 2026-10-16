/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Exactness
/-!
# Coefficient comparison for the Cech complex over arbitrary categories

`cechCosimplicialCoefficientIso` compares the original Cech cosimplicial objects
under a product-preserving coefficient functor. `cechComplexCoefficientIso`
retains the actual alternating coface complex and requires additivity.
The source, coefficient and product universes remain explicit; no topological
space, covering or sheaf hypothesis is imposed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' v'' u u' u''
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
  {B : Type u''} [Category.{v''} B] [HasProducts.{w} B]
  (F : A ⥤ B) [PreservesLimitsOfSize.{w, w} F]
  {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- The natural isomorphism commuting the Cech cosimplicial object of `U` with the
product-preserving coefficient functor `F`. -/
def cechCosimplicialCoefficientIso :
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

/-- The isomorphism commuting the alternating coface complex of `Q` with the additive coefficient
functor `F`. -/
def alternatingCofaceCoefficientIso (Q : CosimplicialObject A) :
    (F.mapHomologicalComplex _).obj (AlgebraicTopology.AlternatingCofaceMapComplex.obj Q) ≅
      AlgebraicTopology.AlternatingCofaceMapComplex.obj (Q ⋙ F) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  simp [AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD, CosimplicialObject.δ]

/-- The isomorphism from the image under `F` of the Cech complex of `P` to the Cech complex with
coefficients `P ⋙ F`, for additive product-preserving `F`. -/
def cechComplexCoefficientIso :
    (F.mapHomologicalComplex _).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ F) :=
  alternatingCofaceCoefficientIso F
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P) ≪≫
      (AlgebraicTopology.alternatingCofaceMapComplex B).mapIso
        (cechCosimplicialCoefficientIso F U P)

end CategoryTheory.Cech
