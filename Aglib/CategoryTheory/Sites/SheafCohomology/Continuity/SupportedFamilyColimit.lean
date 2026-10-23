/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.SupportedFamilyAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteFreeHom
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit
public import Mathlib.Algebra.Category.Grp.AB

/-! # Supported-family acyclicity under filtered colimits

Section continuity is needed only at supported tuple products. The ambient
sheaf-to-presheaf functor need not preserve filtered colimits.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {I : Type (max u v)} [SmallCategory I] [IsFiltered I]

/-- Finite-family Hom on SHEAVES preserves filtered colimits if sections at
its components do. No global inclusion-preservation premise is used. -/
abbrev freeFamilySheafHomPreservesColimits {ι : Type (max u v)} [Finite ι]
    (U : ι → C)
    (hsec : ∀ i, PreservesColimitsOfShape I
      ((sheafSections J AddCommGrpCat.{max u v}).obj (op (U i)))) :
    PreservesColimitsOfShape I (sheafToPresheaf J AddCommGrpCat ⋙
      preadditiveCoyoneda.obj
        (op (Presheaf.Cech.familyPresheaf U ⋙ AddCommGrpCat.free))) := by
  let : PreservesColimitsOfShape I
      (sheafToPresheaf J AddCommGrpCat ⋙ (Presheaf.Cech.familyEvaluationDiagram U).flip) :=
    preservesColimitsOfShape_of_evaluation _ _ (fun i => by
      change PreservesColimitsOfShape I
        ((sheafSections J AddCommGrpCat.{max u v}).obj (op (U i.as)))
      exact hsec i.as)
  let : PreservesColimitsOfShape I
      (lim (J := Discrete ι) (C := AddCommGrpCat.{max u v})) :=
    preservesColimitsOfShape_of_natIso HasBiproductsOfShape.colimIsoLim
  let : PreservesColimitsOfShape I
      (sheafToPresheaf J AddCommGrpCat ⋙
        ((Presheaf.Cech.familyEvaluationDiagram U).flip ⋙ lim)) :=
    preservesColimitsOfShape_of_natIso
      (Functor.associator (sheafToPresheaf J AddCommGrpCat)
        (Presheaf.Cech.familyEvaluationDiagram U).flip lim)
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat)
      (Presheaf.Cech.freeFamilyHomProductIso U)).symm

variable (P : C → Prop) [∀ W : C, HasFiniteProducts (Over W)]

/-- Supported tuple products make the original Hom cochain functor commute
with filtered colimits of sheaves. -/
abbrev supportedFamilyHomComplexPreservesColimits
    (hprod : SupportedTupleProducts P)
    (hsec : ∀ X, P X → PreservesColimitsOfShape I
      ((sheafSections J AddCommGrpCat.{max u v}).obj (op X)))
    (W : C) (hW : P W) {ι : Type (max u v)} [Finite ι]
    (U : ι → Over W) (hU : ∀ i, P (U i).left) :
    PreservesColimitsOfShape I
      (sheafToPresheaf J AddCommGrpCat ⋙
        additiveHomFunctor (Presheaf.Cech.freeComplex (Presheaf.Cech.familyMap U))) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape I
    (sheafToPresheaf J AddCommGrpCat ⋙ preadditiveCoyoneda.obj
      (op (Presheaf.Cech.tuplePresheaf (Presheaf.Cech.familyMap U) n ⋙
        AddCommGrpCat.free)))
  let V := fun a : Fin (n + 1) → ι => (∏ᶜ fun i => U (a i)).left
  let : PreservesColimitsOfShape I
      (sheafToPresheaf J AddCommGrpCat ⋙ preadditiveCoyoneda.obj
        (op (Presheaf.Cech.freeFunctor.obj (Presheaf.Cech.familyPresheaf V)))) :=
    freeFamilySheafHomPreservesColimits V
      (fun a => hsec (V a) (hprod W hW ι U hU n a))
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat)
      (preadditiveCoyoneda.mapIso
        (Presheaf.Cech.freeFunctor.mapIso (Presheaf.Cech.tupleProductIso U n)).op))

/-- Supported tuple-cochain acyclicity is closed under filtered colimits. -/
theorem SupportedFamilyCechAcyclic.colimit
    (hprod : SupportedTupleProducts P)
    (hsec : ∀ X, P X → PreservesColimitsOfShape I
      ((sheafSections J AddCommGrpCat.{max u v}).obj (op X)))
    (G : I ⥤ Sheaf J AddCommGrpCat.{max u v}) [HasColimit G]
    (hG : ∀ i, SupportedFamilyCechAcyclic P (G.obj i)) :
    SupportedFamilyCechAcyclic P (Limits.colimit G) := by
  intro W hW ι _ U hU n
  let T := sheafToPresheaf J AddCommGrpCat.{max u v} ⋙
    additiveHomFunctor (Presheaf.Cech.freeComplex (Presheaf.Cech.familyMap U))
  let : PreservesColimitsOfShape I T :=
    supportedFamilyHomComplexPreservesColimits P hprod hsec W hW U hU
  let Q := T ⋙ HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{max u v} (.up ℕ) (n + 1)
  let : PreservesColimit G (Q ⋙ ShortComplex.π₁) := by
    change PreservesColimit G
      (T ⋙ HomologicalComplex.eval _ (.up ℕ) ((ComplexShape.up ℕ).prev (n + 1)))
    infer_instance
  let : PreservesColimit G (Q ⋙ ShortComplex.π₂) := by
    change PreservesColimit G (T ⋙ HomologicalComplex.eval _ (.up ℕ) (n + 1))
    infer_instance
  let : PreservesColimit G (Q ⋙ ShortComplex.π₃) := by
    change PreservesColimit G
      (T ⋙ HomologicalComplex.eval _ (.up ℕ) ((ComplexShape.up ℕ).next (n + 1)))
    infer_instance
  change (Q.obj (Limits.colimit G)).Exact
  exact ShortComplex.exact_obj_colimit Q G (fun i => hG i W hW ι U hU n)

variable [HasSheafify J AddCommGrpCat.{max u v}]

/-- Colimits of original injective sheaves satisfy supported tuple-cochain exactness. -/
theorem supportedFamilyCechAcyclic_colimit_of_injective
    (hprod : SupportedTupleProducts P)
    (hsec : ∀ X, P X → PreservesColimitsOfShape I
      ((sheafSections J AddCommGrpCat.{max u v}).obj (op X)))
    (G : I ⥤ Sheaf J AddCommGrpCat.{max u v}) [HasColimit G]
    [∀ i, Injective (G.obj i)] : SupportedFamilyCechAcyclic P (Limits.colimit G) :=
  SupportedFamilyCechAcyclic.colimit P hprod hsec G
    (fun i => supportedFamilyCechAcyclic_of_injective P (G.obj i))

end CategoryTheory.Sheaf.ModuleCoefficients
