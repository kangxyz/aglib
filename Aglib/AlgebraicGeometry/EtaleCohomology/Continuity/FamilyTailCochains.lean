/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramRightTail
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.FamilyBaseChange
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteSheafHomCocone
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexCocone
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Original family cochains of the fixed-stage right-image tail

The actual right-image coefficients give a diagram on one fixed site and a
canonical cocone of original family cochains. Its terms are acyclic when the
later coefficients are injective, by the genuine right adjunctions.

The only remaining continuity input is explicitly the colimit certificate for
the original cocone evaluated at every finite tuple product. Those certificates,
not a global sheaf-colimit assertion, produce the cochain colimit and its positive
exactness. For a descended family the existing native base-change isomorphism
transports this cocone and exactness to the original limit-family cochains.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Presheaf.Cech CategoryTheory.Sheaf.ModuleCoefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

/-- The original family Hom cochain functor on one fixed small étale site. -/
def familyCochainFunctor {S : Scheme.{u}} {W : S.Etale} {J : Type (u + 1)}
    (U : J → Over W) :
    AbelianSheaf.{u, u + 1} S ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  sheafToPresheaf S.smallEtaleTopology AddCommGrpCat ⋙
    additiveHomFunctor (freeComplex (familyMap U))

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (i : I)
  {W : (X.obj i).unop.Etale} {J : Type (u + 1)} (U : J → Over W)

/-- The genuine fixed-stage diagram of the original family cochain complexes. -/
def familyTailCochains : Under i ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  diagramRightTail X F i ⋙ familyCochainFunctor U

/-- Every tail term is genuinely acyclic when its original later coefficient
is injective. No inverse image of an injective is used. -/
theorem familyTailCochains_exactAt (a : Under i) [Injective (F.obj a.right)] (n : ℕ) :
    ((familyTailCochains X F i U).obj a).ExactAt (n + 1) :=
  familyCechAcyclic_of_injective ((diagramRightTail X F i).obj a) W J U n

variable (c : Cocone X) [HasColimit (coneCoefficientFunctor X c F)]

/-- The canonical cocone into the original family cochains of the direct image
of the limit coefficient. -/
def familyTailCochainCocone : Cocone (familyTailCochains X F i U) :=
  (familyCochainFunctor U).mapCocone (diagramRightTailCocone X F c i)

/-- Each degree of a leg is postcomposition by the actual right-tail coefficient leg. -/
theorem familyTailCochainCocone_ι_app_f_apply (a : Under i) (n : ℕ)
    (q : (freeComplex (familyMap U)).X n ⟶ ((diagramRightTail X F i).obj a).obj) :
    ((familyTailCochainCocone X F i U c).ι.app a).f n q =
      q ≫ (diagramRightTailLeg X F c a.hom).hom := rfl

variable [Finite J] [HasColimitsOfShape (Under i) AddCommGrpCat.{u + 1}]

/-- Genuine section colimits at the actual tuple products give the original
cochain cocone's colimit certificate, including its face differentials. -/
def familyTailCochainCoconeIsColimit
    (hsec : ∀ (n : ℕ) (a : Fin (n + 1) → J), IsColimit
      (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (∏ᶜ fun k => U (a k)).left)).mapCocone (diagramRightTailCocone X F c i))) :
    IsColimit (familyTailCochainCocone X F i U c) :=
  finiteFamilySheafHomComplexIsColimit U (diagramRightTailCocone X F c i) hsec

/-- Exact filtered colimits of the genuine injective right-image terms yield
positive exactness, with only the original evaluated-cocone input left explicit. -/
theorem familyTailCochainCocone_exactAt [IsFiltered I]
    [∀ j, Injective (F.obj j)]
    (hsec : ∀ (n : ℕ) (a : Fin (n + 1) → J), IsColimit
      (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (∏ᶜ fun k => U (a k)).left)).mapCocone (diagramRightTailCocone X F c i)))
    (n : ℕ) : (familyTailCochainCocone X F i U c).pt.ExactAt (n + 1) := by
  let : HasExactColimitsOfShape (Under i) AddCommGrpCat.{u + 1} :=
    hasExactFilteredColimitsOfShape_addCommGrpCat_of_category (Under i)
  let T := HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u + 1} (.up ℕ) (n + 1)
  let hc := familyTailCochainCoconeIsColimit X F i U c hsec
  exact ShortComplex.exact_of_componentwise_colimit
    (familyTailCochains X F i U ⋙ T) (T.mapCocone (familyTailCochainCocone X F i U c))
    (isColimitOfPreserves
      (HomologicalComplex.eval _ (.up ℕ) ((ComplexShape.up ℕ).prev (n + 1))) hc)
    (isColimitOfPreserves (HomologicalComplex.eval _ (.up ℕ) (n + 1)) hc)
    (isColimitOfPreserves
      (HomologicalComplex.eval _ (.up ℕ) ((ComplexShape.up ℕ).next (n + 1))) hc)
    (fun a => familyTailCochains_exactAt X F i U a n)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.StageSupport

universe u

attribute [local instance] hasSheafifyLarge

variable {I : Type u} [Category.{u} I] {X : I ⥤ Scheme.{u}ᵒᵖ} {c : Cocone X}
  {i : I} {W : c.pt.unop.Etale} {J : Type (u + 1)} {U : J → Over W}
  (M : FamilyModel (X := X) (c := c) i U) (F : DiagramCoefficientSystem X)
  [HasColimit (coneCoefficientFunctor X c F)]

/-- The fixed-stage cochain cocone lands in the original limit family after
the inverse of the accepted native base-change cochain isomorphism. -/
def FamilyModel.tailLimitCochainCocone : Cocone (familyTailCochains X F i M.family) :=
  (familyTailCochainCocone X F i M.family c).extend
    (M.tupleCochainIso (colimit (coneCoefficientFunctor X c F))).inv

@[simp]
theorem FamilyModel.tailLimitCochainCocone_pt :
    (M.tailLimitCochainCocone F).pt =
      additiveHomComplex (familyMap U) (colimit (coneCoefficientFunctor X c F)).obj := rfl

/-- The original map to limit cochains retains both the actual coefficient
leg and the fixed native base-change comparison. -/
theorem FamilyModel.tailLimitCochainCocone_ι_app (a : Under i) :
    (M.tailLimitCochainCocone F).ι.app a =
      (familyTailCochainCocone X F i M.family c).ι.app a ≫
        (M.tupleCochainIso (colimit (coneCoefficientFunctor X c F))).inv := rfl

variable [Finite J] [HasColimitsOfShape (Under i) AddCommGrpCat.{u + 1}]

/-- The remaining evaluated original cocone certificates supply the actual
limit-family cochain colimit, without asserting a sheaf-colimit comparison. -/
def FamilyModel.tailLimitCochainCoconeIsColimit
    (hsec : ∀ (n : ℕ) (a : Fin (n + 1) → J), IsColimit
      (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (∏ᶜ fun k => M.family (a k)).left)).mapCocone
          (diagramRightTailCocone X F c i))) :
    IsColimit (M.tailLimitCochainCocone F) := by
  let e : (familyTailCochainCocone X F i M.family c).pt ≅
      additiveHomComplex (familyMap U) (colimit (coneCoefficientFunctor X c F)).obj :=
    (M.tupleCochainIso (colimit (coneCoefficientFunctor X c F))).symm
  exact IsColimit.extendIso e.hom
    (familyTailCochainCoconeIsColimit X F i M.family c hsec)

/-- Genuine injective tail terms and the original tuple-section cocone
certificates imply positive exactness of the original limit-family cochains. -/
theorem FamilyModel.limitCochains_exactAt [IsFiltered I] [∀ j, Injective (F.obj j)]
    (hsec : ∀ (n : ℕ) (a : Fin (n + 1) → J), IsColimit
      (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (∏ᶜ fun k => M.family (a k)).left)).mapCocone
          (diagramRightTailCocone X F c i))) (n : ℕ) :
    (additiveHomComplex (familyMap U)
      (colimit (coneCoefficientFunctor X c F)).obj).ExactAt (n + 1) :=
  (familyTailCochainCocone_exactAt X F i M.family c hsec n).of_iso
    (M.tupleCochainIso (colimit (coneCoefficientFunctor X c F))).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.StageSupport
