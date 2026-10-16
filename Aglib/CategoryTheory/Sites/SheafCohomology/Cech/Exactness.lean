/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
/-!
# Exactness of the Cech complex over arbitrary categories

A terminal cover component gives an extra degeneracy, hence exactness in every
positive degree of Mathlib's `cechComplexFunctor`. The proof compares its
alternating coface complex to the opposite of the contracted face complex.

`cechCosimplicialChangeIso` compares the original Cech objects under a
finite-product-preserving functor with thin target. The ambient category,
coefficient categories and their product-universe hypotheses remain explicit.

Reference: Stacks Project, [Tag 01X9](https://stacks.math.columbia.edu/tag/01X9).
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
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  (U : FormalCoproduct.{w} C) {T : C} (hT : IsTerminal T)
  (P : Cᵒᵖ ⥤ A)

/-- The augmented simplicial object in `Aᵒᵖ` obtained by evaluating `P` on the Cech object of `U`
augmented to the terminal object `T`. -/
abbrev evaluatedCechAugmentation : SimplicialObject.Augmented Aᵒᵖ :=
  ((SimplicialObject.Augmented.whiskering _ _).obj
    ((FormalCoproduct.evalOp C A).obj P).rightOp).obj
    (U.cech.augmentOfIsTerminal (FormalCoproduct.isTerminalIncl _ hT))

/-- The extra degeneracy on the evaluated Cech augmentation induced by a map from the terminal
object `T` into the selected member `U.obj i₀`. -/
def evaluatedCechExtraDegeneracy {i₀ : U.I} (d : T ⟶ U.obj i₀) :
    (evaluatedCechAugmentation U hT P).ExtraDegeneracy :=
  (U.extraDegeneracyCech hT d).map ((FormalCoproduct.evalOp C A).obj P).rightOp

lemma splitCechChain_exactAt_succ {i₀ : U.I} (d : T ⟶ U.obj i₀) (n : ℕ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (evaluatedCechAugmentation U hT P).left).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (ChainComplex.exactAt_succ_single_obj _ n).isZero_homology.of_iso
    ((evaluatedCechExtraDegeneracy U hT P d).homotopyEquiv.toHomologyIso (n + 1))

/-- The isomorphism identifying the unop of the evaluated alternating face complex with the Cech
cochain complex of `P`. -/
def evaluatedCechUnopIso :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (evaluatedCechAugmentation U hT P).left).unop ≅
    (FormalCoproduct.cochainComplexFunctor U.cech).obj P := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  simp [AlgebraicTopology.AlternatingFaceMapComplex.obj,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    FormalCoproduct.cochainComplexFunctor, FormalCoproduct.cosimplicialObjectFunctor,
    AlgebraicTopology.AlternatingFaceMapComplex.objD,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rfl

include hT in
/-- All positive degrees of the actual Cech complex are exact when one cover
component admits a section from the terminal object. -/
lemma splitCech_exactAt_succ {i₀ : U.I} (d : T ⟶ U.obj i₀) (n : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor U.cech).obj P).ExactAt (n + 1) :=
  (splitCechChain_exactAt_succ U hT P d n).unop.of_iso (evaluatedCechUnopIso U hT P)

include hT in
lemma cechComplex_exactAt_succ_of_terminal_component {ι : Type w} (V : ι → C)
    {i₀ : ι} (d : T ⟶ V i₀) (n : ℕ) :
    ((cechComplexFunctor V).obj P).ExactAt (n + 1) :=
  splitCech_exactAt_succ (FormalCoproduct.mk _ V) hT P d n

end CategoryTheory.Cech


namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type u'} [Category.{v'} D] [HasFiniteProducts D] [Quiver.IsThin D]
  {A : Type u''} [Category.{v''} A] [HasProducts.{w} A]
  (F : C ⥤ D) [PreservesFiniteProducts F] {ι : Type w} (V : ι → C)
  (P : Dᵒᵖ ⥤ A)

/-- The comparison between Cech coefficients pulled back along `F` and the Cech object of the image
family, for finite-product-preserving `F` with thin target. -/
def cechCosimplicialChangeIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ V).cech).obj
      (F.op ⋙ P) ≅
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ (fun i => F.obj (V i))).cech).obj P := by
  refine NatIso.ofComponents (fun n => Limits.Pi.mapIso fun a =>
    P.mapIso (PreservesProduct.iso F (fun i : Fin (n.len + 1) => V (a i))).op.symm) ?_
  intro n m g
  apply Limits.Pi.hom_ext
  intro a
  dsimp [FormalCoproduct.cosimplicialObjectFunctor,
    FormalCoproduct.evalOp, FormalCoproduct.cech, FormalCoproduct.mapPower]
  simp only [Category.assoc, Pi.mapIso_hom_π, Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv,
    limit.lift_π_assoc, Fan.mk_pt, Discrete.functor_obj_eq_as, Fan.mk_π_app, ← Functor.map_comp,
    limit.lift_π, Pi.mapIso_hom_π_assoc, Function.comp_apply]
  congr 2
  apply Subsingleton.elim

end CategoryTheory.Cech
