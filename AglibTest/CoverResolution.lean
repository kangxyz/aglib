/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoverResolutionNaturality

/-! Public-interface checks for free Čech resolutions and actual tuple primitives. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Presheaf CategoryTheory.Presheaf.Cech
open CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex

universe u v w z

variable {C : Type u} [Category.{v} C]

section ArbitraryUniverse

variable {F₁ G₁ F₂ G₂ : Cᵒᵖ ⥤ Type w} {f₁ : F₁ ⟶ G₁} {f₂ : F₂ ⟶ G₂}
    (sq : Arrow.mk f₁ ⟶ Arrow.mk f₂)
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

example (n : ℕ) {A : Sheaf J AddCommGrpCat.{w}}
    (c : tuplePresheaf f₂ n ⟶ A.obj ⋙ forget AddCommGrpCat) :
    (resolutionMap sq J).f (-(n : ℤ)) ≫ resolutionTupleLift f₂ J c =
      resolutionTupleLift f₁ J (tupleMap sq n ≫ c) :=
  resolutionTupleLift_precomp sq J c

example : resolutionMap sq J ≫ resolutionAugmentation f₂ J =
    resolutionAugmentation f₁ J ≫
      (CochainComplex.singleFunctor _ 0).map (targetMap sq J) :=
  resolutionAugmentation_naturality sq J

end ArbitraryUniverse

section LiteralPrimitive

variable {F G : Cᵒᵖ ⥤ Type (max u v)} (f : F ⟶ G)
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v}]

-- Neither a locally surjective map nor a derived category is needed for this homotopy.
example {A : Sheaf J AddCommGrpCat.{max u v}}
    (p : tuplePresheaf f 1 ⟶ A.obj ⋙ forget AddCommGrpCat)
    (c : tuplePresheaf f 2 ⟶ A.obj ⋙ forget AddCommGrpCat)
    (hc : ∀ (U : Cᵒᵖ) (a : Tuple f 3 U),
      ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • c.app U (tupleReindex f i.succAbove a) = 0)
    (hp : ∀ (U : Cᵒᵖ) (a : Tuple f 2 U),
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • p.app U (tupleReindex f i.succAbove a) =
        c.app U a) :
    Nonempty (Homotopy
      (Cocycle.equivHomShift.symm
        (degreeTwoCocycle f J (resolutionTupleLift f J c)
          (resolutionTupleLift_closed f J c hc))) 0) :=
  degreeTwoCocycle_nullHomotopic f J _ _ (resolutionTupleLift f J p)
    (resolutionTupleLift_differential_eq J p c hp)

end LiteralPrimitive

section DerivedNaturality

variable {F₁ G₁ F₂ G₂ : Cᵒᵖ ⥤ Type (max u v)} {f₁ : F₁ ⟶ G₁} {f₂ : F₂ ⟶ G₂}
    (sq : Arrow.mk f₁ ⟶ Arrow.mk f₂)
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v}]
    [IsLocallySurjective J f₁] [IsLocallySurjective J f₂]
    [HasDerivedCategory.{z} (Sheaf J AddCommGrpCat.{max u v})]

example {A : Sheaf J AddCommGrpCat.{max u v}}
    (c : (resolution f₂ J).X (-2) ⟶ A)
    (hc : (resolution f₂ J).d (-3) (-2) ≫ c = 0) :
    degreeTwoClass f₁ J ((resolutionMap sq J).f (-2) ≫ c)
        (by simp only [← HomologicalComplex.Hom.comm_assoc, hc, comp_zero]) =
      (DerivedCategory.singleFunctor _ 0).map (targetMap sq J) ≫
        degreeTwoClass f₂ J c hc :=
  degreeTwoClass_precomp sq J c hc

end DerivedNaturality
