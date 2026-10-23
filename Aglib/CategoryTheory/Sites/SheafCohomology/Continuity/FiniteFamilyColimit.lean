/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteTupleHom
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteFamilyAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.SectionsColimit
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit

/-! # Filtered colimits of finite-family acyclic sheaves

Finite-cover generation supplies actual pointwise filtered colimits. The original
finite tuple Hom cochains preserve those colimits, hence preserve their positive
exactness. This is acyclicity of the actual colimit, not an assumed continuity axiom.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe e v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ W : C, HasFiniteProducts (Over W)]
  (H : J.OneHypercoverFamily.{max u v}) [H.IsGenerating]
  (hfin : ∀ ⦃X : C⦄ (E : J.OneHypercover.{max u v} X), H E →
    Finite E.I₀ ∧ ∀ i j : E.I₀, Finite (E.I₁ i j))
  {I : Type (max u v)} [SmallCategory I] [IsFiltered I]

omit [HasSheafify J AddCommGrpCat.{max u v}] in
include H hfin in
/-- The genuine finite-family acyclicity property is closed under filtered colimits. -/
theorem FiniteFamilyCechAcyclic.colimit
    (G : I ⥤ Sheaf J AddCommGrpCat.{max u v}) [HasColimit G]
    (hG : ∀ i, FiniteFamilyCechAcyclic (G.obj i)) :
    FiniteFamilyCechAcyclic (Limits.colimit G) := by
  let := H.preservesColimitsOfShapeSheafToPresheaf (I := I)
    (A := AddCommGrpCat.{max u v}) hfin
  intro W ι _ U n
  let K := Presheaf.Cech.freeComplex (Presheaf.Cech.familyMap U)
  let T := sheafToPresheaf J AddCommGrpCat.{max u v} ⋙ additiveHomFunctor K
  let : PreservesColimitsOfShape I (additiveHomFunctor K) :=
    Presheaf.Cech.finiteFamilyHomComplexPreservesColimits (I := I) U
  let : PreservesColimitsOfShape I T := by
    dsimp [T]
    infer_instance
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
  exact ShortComplex.exact_obj_colimit Q G (fun i => hG i W ι U n)

include H hfin in
/-- A filtered colimit of actual injective sheaves is finite-family acyclic. -/
theorem finiteFamilyCechAcyclic_colimit_of_injective
    (G : I ⥤ Sheaf J AddCommGrpCat.{max u v}) [HasColimit G]
    [∀ i, Injective (G.obj i)] : FiniteFamilyCechAcyclic (Limits.colimit G) :=
  FiniteFamilyCechAcyclic.colimit H hfin G
    (fun i => finiteFamilyCechAcyclic_of_injective (G.obj i))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]

include H hfin in
/-- Positive original represented Ext vanishes on filtered colimits of injectives. -/
theorem colimit_injective_ext_eq_zero
    (G : I ⥤ Sheaf J AddCommGrpCat.{max u v}) [HasColimit G]
    [∀ i, Injective (G.obj i)] (W : C) (n : ℕ)
    (x : Ext.{e} (Hypercohomology.freeAbelianSheaf.{u} J W) (Limits.colimit G) (n + 1)) :
    x = 0 :=
  (finiteFamilyCechAcyclic_colimit_of_injective H hfin G).ext_eq_zero
    H (fun {_} E hE => (hfin E hE).1) W n x

include H hfin in
/-- Positive original global cohomology vanishes on filtered colimits of injectives. -/
theorem colimit_injective_cohomology_eq_zero
    (G : I ⥤ Sheaf J AddCommGrpCat.{max u v}) [HasColimit G]
    [∀ i, Injective (G.obj i)] {W : C} (hW : IsTerminal W) (n : ℕ)
    (x : Sheaf.H.{e} (Limits.colimit G) (n + 1)) : x = 0 :=
  (finiteFamilyCechAcyclic_colimit_of_injective H hfin G).cohomology_eq_zero
    H (fun {_} E hE => (hfin E hE).1) hW n x

end CategoryTheory.Sheaf.ModuleCoefficients
