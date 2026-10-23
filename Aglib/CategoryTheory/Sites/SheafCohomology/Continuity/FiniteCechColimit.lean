/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoefficientNaturality
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.Functor

/-! # Filtered colimits of finite Čech complexes

The original finite Čech complex commutes with the actual filtered-colimit
coefficient functor. The resulting homology comparison is obtained from native
exactness of filtered colimits of abelian groups. This is the finite algebraic
step of cohomological continuity, not a continuity theorem for sheaf cohomology:
the finite-cover basis and the original-cohomology acyclicity argument remain
separate geometric and homological inputs.

The diagram category and abelian groups live in the same explicit universe `w`;
the site object and morphism universes are independent. No Ext universe is fixed
by this complex-level result.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Cech

universe w v u

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {I : Type w} [SmallCategory I] [IsFiltered I]
  {ι : Type w} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ I ⥤ AddCommGrpCat.{w})

/-- Finite Čech cochains commute with the actual filtered-colimit functor. -/
def finiteCechFilteredColimitIso :
    ((colim (J := I) (C := AddCommGrpCat.{w})).mapHomologicalComplex (.up ℕ)).obj
        ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ colim) :=
  finiteCechComplexCoefficientIso colim U P

/-- The complex comparison is built from the original product comparison, so
its degreewise maps preserve the original Čech projections. -/
theorem finiteCechFilteredColimitIso_hom_f (q : ℕ) :
    (finiteCechFilteredColimitIso U P).hom.f q =
      piComparison (colim (J := I) (C := AddCommGrpCat.{w}))
        (fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k)))) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Every finite Čech cohomology degree commutes with filtered colimits of
abelian-group diagrams, through native homology and product comparisons. -/
def finiteCechFilteredColimitHomologyIso (q : ℕ) :
    colimit (((cechComplexFunctor U).obj P).homology q) ≅
      ((cechComplexFunctor U).obj (P ⋙ colim)).homology q :=
  ((((cechComplexFunctor U).obj P).sc q).mapHomologyIso
      (colim (J := I) (C := AddCommGrpCat.{w}))).symm ≪≫
    HomologicalComplex.homologyMapIso (finiteCechFilteredColimitIso U P) q

/-- The cochain comparison respects the native colimit cocone, expressed as
naturality in the coefficient functor rather than a chosen inverse map. -/
theorem finiteCechFilteredColimitIso_cocone (i : I) :
    (NatTrans.mapHomologicalComplex
        (colim.ι (J := I) (C := AddCommGrpCat.{w}) i) (.up ℕ)).app
        ((cechComplexFunctor U).obj P) ≫
      (finiteCechFilteredColimitIso U P).hom =
    (finiteCechComplexCoefficientIso ((evaluation I AddCommGrpCat).obj i) U P).hom ≫
      (cechComplexFunctor U).map
        (Functor.whiskerLeft P (colim.ι (J := I) (C := AddCommGrpCat.{w}) i)) :=
  finiteCechComplexCoefficientIso_naturality_functor
    ((evaluation I AddCommGrpCat).obj i) colim
    (colim.ι (J := I) (C := AddCommGrpCat.{w}) i) U P

end CategoryTheory.Cech
