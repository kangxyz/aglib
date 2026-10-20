/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Functorial colimits over the actual costructured presentation categories and their universal
natural comparison

No comparison-isomorphism premise is discharged.

Source: `lean/R5Lab/Aglib/CategoryTheory/PresentationColimit.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `e1847e50fac276b8b527391e6d67dc1746ae2aff24c324c5a1394f37cfd8c791`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PresentationColimit
universe vC vD vE uC uD uE
variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]
variable (I : C ⥤ D) (P : C ⥤ E)

abbrev diagram (R : D) : CostructuredArrow I R ⥤ E :=
  CostructuredArrow.proj I R ⋙ P

variable [∀ R, HasColimit (diagram I P R)]

/-- Presentation change induced by an arbitrary map of target objects. -/
def extensionMap {R T : D} (f : R ⟶ T) :
    colimit (diagram I P R) ⟶ colimit (diagram I P T) :=
  colimit.desc (diagram I P R)
    { pt := colimit (diagram I P T)
      ι :=
        { app := fun a => colimit.ι (diagram I P T) ((CostructuredArrow.map f).obj a)
          naturality := fun a b g => by
            simpa using colimit.w (diagram I P T) ((CostructuredArrow.map f).map g) } }

@[reassoc (attr := simp)]
theorem ι_extensionMap {R T : D} (f : R ⟶ T) (a : CostructuredArrow I R) :
    colimit.ι (diagram I P R) a ≫ extensionMap I P f =
      colimit.ι (diagram I P T) ((CostructuredArrow.map f).obj a) := by
  simp [extensionMap]

@[simp]
theorem extensionMap_id (R : D) :
    extensionMap I P (𝟙 R) = 𝟙 (colimit (diagram I P R)) := by
  apply colimit.hom_ext
  intro a
  simp only [ι_extensionMap, Category.comp_id]
  congr 1
  exact CostructuredArrow.map_id

theorem extensionMap_comp {R T U : D} (f : R ⟶ T) (g : T ⟶ U) :
    extensionMap I P (f ≫ g) = extensionMap I P f ≫ extensionMap I P g := by
  apply colimit.hom_ext
  intro a
  simp only [ι_extensionMap, ι_extensionMap_assoc]
  congr 1
  exact CostructuredArrow.map_comp

/-- The canonical presentation colimits form a functor, with all maps supplied
by postcomposition in the actual comma categories. -/
def extensionFunctor : D ⥤ E where
  obj R := colimit (diagram I P R)
  map f := extensionMap I P f
  map_id R := extensionMap_id I P R
  map_comp f g := extensionMap_comp I P f g

variable (Q : D ⥤ E) (alpha : P ⟶ I ⋙ Q)

/-- The finite-stage comparison followed by pullback to the selected target.
This is a genuine cocone; its compatibility is proved from naturality. -/
def comparisonCocone (R : D) : Cocone (diagram I P R) where
  pt := Q.obj R
  ι :=
    { app := fun a => alpha.app a.left ≫ Q.map a.hom
      naturality := fun a b g => by
        dsimp
        rw [← Category.assoc, alpha.naturality g.left]
        simp only [Functor.comp_map, Category.assoc, ← Q.map_comp,
          CostructuredArrow.w, Category.comp_id] }

/-- A constructed map from the colimit of raw finite-stage groups.
No local equivalence or local comparison map is an input. -/
def comparison (R : D) : colimit (diagram I P R) ⟶ Q.obj R :=
  colimit.desc (diagram I P R) (comparisonCocone I P Q alpha R)

@[reassoc (attr := simp)]
theorem ι_comparison (R : D) (a : CostructuredArrow I R) :
    colimit.ι (diagram I P R) a ≫ comparison I P Q alpha R =
      alpha.app a.left ≫ Q.map a.hom := by
  simp [comparison, comparisonCocone]

/-- Arbitrary-map coherence is a consequence of the colimit construction. -/
theorem comparison_naturality {R T : D} (f : R ⟶ T) :
    extensionMap I P f ≫ comparison I P Q alpha T =
      comparison I P Q alpha R ≫ Q.map f := by
  apply colimit.hom_ext
  intro a
  simp only [ι_extensionMap_assoc, ι_comparison, ι_comparison_assoc]
  simp [CostructuredArrow.map, Q.map_comp]

/-- The finite-stage triangles determine the comparison uniquely. -/
theorem comparison_unique (R : D) (c : colimit (diagram I P R) ⟶ Q.obj R)
    (hc : ∀ a : CostructuredArrow I R,
      colimit.ι (diagram I P R) a ≫ c = alpha.app a.left ≫ Q.map a.hom) :
    c = comparison I P Q alpha R := by
  apply colimit.hom_ext
  intro a
  exact (hc a).trans (ι_comparison I P Q alpha R a).symm

/-- Naturality packaged after the objectwise construction and its proof. -/
def comparisonNatTrans : extensionFunctor I P ⟶ Q where
  app R := comparison I P Q alpha R
  naturality _R _T f := comparison_naturality I P Q alpha f

end CategoryTheory.PresentationColimit
