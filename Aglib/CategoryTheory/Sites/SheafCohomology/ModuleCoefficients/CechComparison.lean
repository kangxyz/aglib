/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Cech
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FreeComparison

/-!
# Forgetting scalars in the original tuple Cech complex

The comparison is a degreewise additive isomorphism which commutes with the
original alternating differentials. Acyclicity is transferred along this actual
complex isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace CategoryTheory.Presheaf.Cech

universe r c h

variable {C : Type c} [Category.{h} C] {F G : Cᵒᵖ ⥤ Type r} (f : F ⟶ G)

/-- Additive cochains on the original tuple nerve. -/
def additiveHomComplex (A : Cᵒᵖ ⥤ AddCommGrpCat.{r}) :
    CochainComplex AddCommGrpCat.{max r c} ℕ :=
  ((preadditiveYoneda.obj A).mapHomologicalComplex (.up ℕ)).obj (freeComplex f).op

/-- Injective abelian presheaves are acyclic for the original tuple Cech complex. -/
lemma additiveHomComplex_exactAt_succ_of_injective
    (A : Cᵒᵖ ⥤ AddCommGrpCat.{r}) [Injective A] (n : ℕ) :
    (additiveHomComplex f A).ExactAt (n + 1) := by
  have := freeImageAugmentation_quasiIso f
  have h : (freeComplex f).ExactAt (n + 1) :=
    (exactAt_iff_of_quasiIsoAt (freeImageAugmentation f) (n + 1)).2
      (ChainComplex.exactAt_succ_single_obj _ n)
  rw [HomologicalComplex.exactAt_iff]
  have hm := ((HomologicalComplex.exactAt_iff _ _).1 h.op).map (preadditiveYonedaObj A)
  exact hm.map (forget₂ (ModuleCat.{max r c} (End A)) AddCommGrpCat.{max r c})

end CategoryTheory.Presheaf.Cech

namespace PresheafOfModules.Cech

universe r c h m

variable {C : Type c} [Category.{h} C] (R : Cᵒᵖ ⥤ RingCat.{r})
    {F G : Cᵒᵖ ⥤ Type (max r m)} (f : F ⟶ G) (I : PresheafOfModules.{max r m} R)

set_option backward.isDefEq.respectTransparency false in
/-- The original module-linear and additive tuple cochains are isomorphic. -/
def homComplexForgetIso : homComplex.{r, c, h, m} R f I ≅
    CategoryTheory.Presheaf.Cech.additiveHomComplex f I.presheaf := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n =>
    AddEquiv.toAddCommGrpIso
      (freeAbelianHomAddEquiv.{r, c, h, m} R (CategoryTheory.Presheaf.Cech.tuplePresheaf f n) I)) ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  apply AddCommGrpCat.ext
  intro a
  symm
  change (freeAbelianHomAddEquiv.{r, c, h, m} R _ I)
    ((freeComplex.{r, c, h, m} R f).d (i + 1) i ≫ a) =
    (CategoryTheory.Presheaf.Cech.freeComplex f).d (i + 1) i ≫
      (freeAbelianHomAddEquiv.{r, c, h, m} R _ I) a
  simp only [freeComplex, CategoryTheory.Presheaf.Cech.freeComplex,
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
    Preadditive.sum_comp, Preadditive.zsmul_comp, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact freeAbelianHomEquiv_naturality.{r, c, h, m} R _ I _ a

/-- Underlying additive tuple cochains of an injective module presheaf are exact. -/
lemma additiveHomComplex_exactAt_succ [Injective I] (n : ℕ) :
    (CategoryTheory.Presheaf.Cech.additiveHomComplex f I.presheaf).ExactAt (n + 1) :=
  (homComplex_exactAt_succ.{r, c, h, m} R f I n).of_iso (homComplexForgetIso.{r, c, h, m} R f I)

end PresheafOfModules.Cech
