/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FamilyBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StageSupport.TupleProducts

/-! # Original étale family cochains under actual base change

The native small-étale base-change functor preserves finite limits. Its actual
family tuple comparison therefore induces an isomorphism of original additive
Hom cochains with direct-image coefficients. Direct image here is its original
precomposition presheaf, not a replacement coefficient or a cohomological
comparison hypothesis.

For a descended family, the product comparison is precisely the accepted
geometric model's tuple isomorphism, with the original projection and face
maps retained. The filtered-colimit comparison still needs the separate actual
degree-zero continuity producer; it is not asserted in this file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Presheaf.Cech

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S)
  {W : S.Etale} {W' : T.Etale} {J : Type (u + 1)}
  (U : J → Over W) (V : J → Over W') (e : (siteBaseChange f).obj W ≅ W')
  (eU : ∀ j, (Over.post (siteBaseChange f) ⋙ Over.map e.hom).obj (U j) ≅ V j)

/-- The original additive Hom cochain comparison along actual étale base
change, expressed using the native direct-image sheaf. -/
def familyCochainBaseChangeIso (A : AbelianSheaf.{u, u + 1} T) :
    additiveHomComplex (familyMap V) A.obj ≅
      additiveHomComplex (familyMap U) ((directImage f).obj A).obj :=
  FamilyBaseChange.additiveHomIso (siteBaseChange f) U V e eU A.obj

/-- The isomorphism retains the actual free tuple map in every degree. -/
theorem familyCochainBaseChangeIso_hom_f_apply
    (A : AbelianSheaf.{u, u + 1} T) (n : ℕ)
    (q : (freeComplex (familyMap V)).X n ⟶ A.obj) :
    (familyCochainBaseChangeIso f U V e eU A).hom.f n q =
      Functor.whiskerRight
        (FamilyBaseChange.tupleNatTrans (siteBaseChange f) U V e eU n) AddCommGrpCat.free ≫
          Functor.whiskerLeft (siteBaseChange f).op q :=
  FamilyBaseChange.additiveHomMap_f_apply (siteBaseChange f) U V e eU A.obj n q

namespace StageSupport

variable {I : Type u} [Category.{u} I]
  {X : I ⥤ Scheme.{u}ᵒᵖ} {c : Cocone X} {i : I}
  {W : c.pt.unop.Etale} {J : Type (u + 1)} {U : J → Over W}
  (M : FamilyModel (X := X) (c := c) i U)

/-- The canonical cochain construction uses the existing geometric tuple
isomorphism literally, not an independently chosen model. -/
theorem FamilyModel.cochainTupleIso_eq {n : ℕ} (a : Fin (n + 1) → J) :
    FamilyBaseChange.tupleIso (siteBaseChange (c.ι.app i).unop)
      M.family U M.target.iso M.familyIso a = M.tupleIso a := rfl

/-- Every deletion face and repetition map commutes with the existing tuple
models in the original small étale site. -/
@[reassoc]
theorem FamilyModel.tupleIso_reindex {n m : ℕ} (a : Fin (n + 1) → J)
    (b : Fin (m + 1) → Fin (n + 1)) :
    (M.tupleIso a).hom ≫ (FamilyBaseChange.productReindex (U := U) a b).left =
      (siteBaseChange (c.ι.app i).unop).map
        (FamilyBaseChange.productReindex (U := M.family) a b).left ≫
          (M.tupleIso (a ∘ b)).hom :=
  congrArg (fun k => k.left)
    (FamilyBaseChange.productIso_reindex (siteBaseChange (c.ι.app i).unop)
      M.family U M.target.iso M.familyIso a b)

/-- The actual family-model cochain isomorphism, with the original direct
image of the coefficient on the limit scheme. -/
def FamilyModel.tupleCochainIso (A : AbelianSheaf.{u, u + 1} c.pt.unop) :
    additiveHomComplex (familyMap U) A.obj ≅
      additiveHomComplex (familyMap M.family)
        ((directImage (c.ι.app i).unop).obj A).obj :=
  familyCochainBaseChangeIso (c.ι.app i).unop M.family U M.target.iso M.familyIso A

/-- The actual cochain map evaluates sections along the accepted model's
original tuple isomorphism. -/
theorem FamilyModel.tupleCochainIso_hom_section
    (A : AbelianSheaf.{u, u + 1} c.pt.unop) (n : ℕ)
    (q : (freeComplex (familyMap U)).X n ⟶ A.obj) (a : Fin (n + 1) → J) :
    FamilyBaseChange.tupleHomEquiv M.family
        ((directImage (c.ι.app i).unop).obj A).obj n
        ((M.tupleCochainIso A).hom.f n q) a =
      A.obj.map (M.tupleIso a).hom.op (FamilyBaseChange.tupleHomEquiv U A.obj n q a) :=
  FamilyBaseChange.additiveHomMap_section (siteBaseChange (c.ι.app i).unop)
    M.family U M.target.iso M.familyIso A.obj n q a

end StageSupport

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
