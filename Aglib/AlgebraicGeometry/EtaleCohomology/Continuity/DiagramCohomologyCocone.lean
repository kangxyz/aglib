/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitFunctor

/-! # The original all-degree scheme-limit comparison map

Only the comparison map and its exact cocone equations are constructed here.
No invertibility or scheme-limit continuity theorem is assumed or asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e uI vI
attribute [local instance] hasSheafifyLarge

lemma cohomologyTransfer_triangle {X Y Z : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]
    (f : Y ⟶ X) (p : Z ⟶ X) (q : Z ⟶ Y) (h : q ≫ f = p)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    {H : AbelianSheaf.{u, u + 1} Z}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage q).obj G ⟶ H) (n : ℕ) :
    cohomologyTransfer f φ n ≫ cohomologyTransfer q ψ n =
      cohomologyTransfer p (triangleCoefficientMap f p q h φ ≫ ψ) n := by
  subst p
  simpa only [triangleCoefficientMap, pullbackTriangleIso, Iso.trans_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.assoc] using cohomologyTransfer_comp f q φ ψ n

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  (c : Cocone X) [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  (F : DiagramCoefficientSystem X) (n : ℕ)
  [HasColimit (coneCoefficientFunctor X c F)]

/-- The original stage pullback followed by its coefficient colimit injection. -/
def diagramCohomologyLeg (i : I) : diagramCohomologyObj X F n i ⟶
    AddCommGrpCat.of (Sheaf.H.{e} (colimit (coneCoefficientFunctor X c F)) n) :=
  cohomologyTransfer (X := (X.obj i).unop) (Y := c.pt.unop)
    (c.ι.app i).unop (colimit.ι (coneCoefficientFunctor X c F) i) n

lemma diagramCohomologyLeg_naturality {i j : I} (a : i ⟶ j) :
    diagramCohomologyMap X F n a ≫ diagramCohomologyLeg X c F n j =
      diagramCohomologyLeg X c F n i := by
  rw [diagramCohomologyMap_eq_transfer]
  have ht := cohomologyTransfer_triangle
    (X := (X.obj i).unop) (Y := (X.obj j).unop) (Z := c.pt.unop) (X.map a).unop
    (c.ι.app i).unop (c.ι.app j).unop
    (congrArg (fun k : X.obj i ⟶ c.pt => k.unop) (c.w a))
    (diagramInverseTransition X F a) (colimit.ι (coneCoefficientFunctor X c F) j) n
  exact ht.trans (congrArg (fun k =>
    cohomologyTransfer (X := (X.obj i).unop) (Y := c.pt.unop) (c.ι.app i).unop k n)
      (colimit.w (coneCoefficientFunctor X c F) a))

/-- The canonical cocone on original stage cohomology. -/
def diagramCohomologyCocone : Cocone (diagramCohomologyFunctor X F n) where
  pt := AddCommGrpCat.of (Sheaf.H.{e} (colimit (coneCoefficientFunctor X c F)) n)
  ι :=
    { app := diagramCohomologyLeg X c F n
      naturality := fun _ _ a =>
        (diagramCohomologyLeg_naturality X c F n a).trans (Category.comp_id _).symm }

variable [HasColimit (diagramCohomologyFunctor X F n)]

/-- The literal map induced by the original pullback and coefficient injections. -/
def schemeLimitCohomologyComparison : colimit (diagramCohomologyFunctor X F n) ⟶
    AddCommGrpCat.of (Sheaf.H.{e} (colimit (coneCoefficientFunctor X c F)) n) :=
  colimit.desc _ (diagramCohomologyCocone X c F n)

@[reassoc]
lemma ι_schemeLimitCohomologyComparison (i : I) :
    colimit.ι (diagramCohomologyFunctor X F n) i ≫
        schemeLimitCohomologyComparison X c F n = diagramCohomologyLeg X c F n i :=
  colimit.ι_desc _ i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
