/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctorPlus
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Section values of actual extended resolution lifts

The component of a supplied resolution lift, extended by zero, transports the
ordinary section value of the original source morphism. The Hom-to-sections
comparison and its underived source-map value law are the supplied native ones.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.InjectiveResolution.ExactFunctor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- A supplied ordinary source-map value gives the section value of the actual
extended lift, with the original integer-degree term identifications. -/
theorem extendedLift_sections (L : C ⥤ D) [L.Additive]
    {A : C} {B : D} (I : InjectiveResolution A) (J : InjectiveResolution B)
    (φ : mappedResolution L I ⟶ J.cocomplex) {T : C} {U : D}
    (c : U ⟶ L.obj T) (S : D ⥤ AddCommGrpCat.{v₂})
    (e : preadditiveCoyoneda.obj (op U) ≅ S) (q : ℕ)
    (a : T ⟶ I.cocomplex.X q)
    (s : S.obj (L.obj (I.cochainComplex.X (q : ℤ))))
    (hvalue : e.hom.app _
      (c ≫ L.map (a ≫ (I.cochainComplexXIso q q rfl).inv)) = s) :
    e.hom.app _ ((c ≫ L.map a ≫ φ.f q) ≫ (J.cochainComplexXIso q q rfl).inv) =
      S.map ((extendedLift L I J φ).f (q : ℤ)) s := by
  let a' := c ≫ L.map (a ≫ (I.cochainComplexXIso q q rfl).inv)
  have hn := ConcreteCategory.congr_hom
    (e.hom.naturality ((extendedLift L I J φ).f (q : ℤ))) a'
  change e.hom.app _ (a' ≫ (extendedLift L I J φ).f (q : ℤ)) =
    S.map ((extendedLift L I J φ).f (q : ℤ)) (e.hom.app _ a') at hn
  have hterm :
      ((c ≫ L.map a ≫ φ.f q) ≫ (J.cochainComplexXIso q q rfl).inv) =
        a' ≫ (extendedLift L I J φ).f (q : ℤ) := by
    dsimp only [a']
    rw [extendedLift_f, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (congrArg (e.hom.app (J.cochainComplex.X (q : ℤ))) hterm).trans
    (hn.trans (congrArg (fun z => S.map ((extendedLift L I J φ).f (q : ℤ)) z) hvalue))

end CategoryTheory.InjectiveResolution.ExactFunctor
