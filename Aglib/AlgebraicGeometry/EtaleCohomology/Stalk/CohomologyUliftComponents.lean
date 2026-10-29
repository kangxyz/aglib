/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.CohomologyDiagramReindex

/-! # Original class formulas for common-universe diagram comparisons -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe r e uI vI uJ vJ uK vK

/-- The common-universe comparison retains the original two stage maps. -/
theorem additiveTwiceReindexUliftIso_apply
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    {K : Type uK} [Category.{vK} K]
    (A : I ⥤ J) (B : J ⥤ K)
    (F : I ⥤ AddCommGrpCat.{e}) (G : K ⥤ AddCommGrpCat.{e})
    (H : K ⥤ AddCommGrpCat.{r}) (α : F ≅ A ⋙ B ⋙ G)
    (β : G ⋙ AddCommGrpCat.uliftFunctor.{r, e} ≅
      H ⋙ AddCommGrpCat.uliftFunctor.{e, r}) (i : I) (x : F.obj i) :
    (additiveTwiceReindexUliftIso A B F G H α β).hom.app i (ULift.up x) =
      β.hom.app (B.obj (A.obj i)) (ULift.up (α.hom.app i x)) :=
  CategoryTheory.additiveTwiceReindexUliftIso_apply A B F G H α β i x

section NativeCohomology
universe u w s t
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{t} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The native lifted presheaf comparison takes an original class to its group-only resize. -/
theorem originalFibreProductUliftIso_apply (U : S.Etaleᵒᵖ)
    (x : Sheaf.H.{t} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q) :
    (originalFibreProductUliftIso f F q).hom.app U (ULift.up x) =
      ULift.up (Shrink.addEquiv.symm x) := rfl
end NativeCohomology

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
