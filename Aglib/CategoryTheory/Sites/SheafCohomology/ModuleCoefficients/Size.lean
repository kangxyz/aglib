/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Free
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Module sheaves with larger coefficient universes

The site object and morphism universes need not agree. Lifted representables
supply a separating family in the original presheaf-module category. Exact
sheafification transfers the resulting Grothendieck structure to the original
module-sheaf category. Both the native aligned-ring construction and the
independent-scalar construction retain the original site. The latter uses
finitely supported functions over the unchanged scalar presheaf.

The generator and AB5 arguments extend the native Mathlib constructions in
`Presheaf.Generator` and `GrothendieckAxioms.SheafOfModules`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v t

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{max u v t})

/-- Free modules on the genuinely lifted representables of the original site. -/
def largeFreeYonedaFunctor : C ⥤ PresheafOfModules.{max u v t} R :=
  uliftYoneda.{max u t} ⋙ free R

/-- The lifted free module still represents evaluation on the original site. -/
def largeFreeYonedaEquiv (M : PresheafOfModules.{max u v t} R) (X : C) :
    ((largeFreeYonedaFunctor.{u, v, t} R).obj X ⟶ M) ≃ M.obj (Opposite.op X) :=
  freeHomEquiv.trans uliftYonedaEquiv

/-- The representing equivalence keeps the original coefficient map. -/
theorem largeFreeYonedaEquiv_comp {M N : PresheafOfModules.{max u v t} R}
    (X : C) (f : (largeFreeYonedaFunctor.{u, v, t} R).obj X ⟶ M) (g : M ⟶ N) :
    largeFreeYonedaEquiv.{u, v, t} R N X (f ≫ g) =
      g.app (Opposite.op X) (largeFreeYonedaEquiv.{u, v, t} R M X f) := rfl

/-- Lifted free representables separate maps without changing the site. -/
theorem largeFreeYoneda_isSeparating :
    ObjectProperty.IsSeparating (.ofObj (largeFreeYonedaFunctor.{u, v, t} R).obj) := by
  intro M N f g h
  ext ⟨X⟩ m
  obtain ⟨a, rfl⟩ := (largeFreeYonedaEquiv.{u, v, t} R M X).surjective m
  exact congrArg (largeFreeYonedaEquiv.{u, v, t} R N X) (h _ ⟨X⟩ a)

/-- A separator at the larger coefficient size on the original site. -/
theorem hasSeparatorLarge : HasSeparator (PresheafOfModules.{max u v t} R) :=
  ⟨_, (largeFreeYoneda_isSeparating.{u, v, t} R).isSeparator_coproduct⟩

/-- The native presheaf-module category is Grothendieck at the stated size. -/
theorem isGrothendieckAbelianLarge :
    IsGrothendieckAbelian.{max u v t} (PresheafOfModules.{max u v t} R) where
  hasSeparator := hasSeparatorLarge.{u, v, t} R
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun K _ _ ↦ ⟨⟨fun D _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := K) ⋙ PresheafOfModules.toPresheaf R) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (toPresheaf R)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf R)⟩⟩⟩⟩

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{max u v t})
  [HasSheafify J AddCommGrpCat.{max u v t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v t}]

/-- Exact sheafification gives Grothendieck module sheaves at the larger size. -/
theorem isGrothendieckAbelianLarge :
    IsGrothendieckAbelian.{max u v t} (SheafOfModules.{max u v t} R) := by
  let := PresheafOfModules.isGrothendieckAbelianLarge.{u, v, t} R.obj
  exact
    { hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
      ab5OfSize := ⟨fun K _ _ ↦
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K⟩
      hasSeparator :=
        .of_adjunction (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) }

/-- Enough injectives follows in the original larger-universe module-sheaf category. -/
theorem enoughInjectivesLarge : EnoughInjectives (SheafOfModules.{max u v t} R) := by
  let := isGrothendieckAbelianLarge.{u, v, t} R
  infer_instance

end SheafOfModules

universe r

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{r})

/-- Free modules on the genuinely lifted representables of the original site. -/
def largeFreeYonedaFunctorOverSmallScalars : C ⥤ PresheafOfModules.{max u v r t} R :=
  uliftYoneda.{max u r t} ⋙ freeWide.{r, max u v r t, u, v} R

/-- The lifted free module still represents evaluation on the original site. -/
def largeFreeYonedaEquivOverSmallScalars (M : PresheafOfModules.{max u v r t} R) (X : C) :
    ((largeFreeYonedaFunctorOverSmallScalars.{u, v, t, r} R).obj X ⟶ M) ≃ M.obj (Opposite.op X) :=
  freeWideHomEquiv.{r, max u v t, u, v}.trans uliftYonedaEquiv

/-- The representing equivalence keeps the original coefficient map. -/
theorem largeFreeYonedaEquiv_compOverSmallScalars {M N : PresheafOfModules.{max u v r t} R}
    (X : C) (f : (largeFreeYonedaFunctorOverSmallScalars.{u, v, t, r} R).obj X ⟶ M) (g : M ⟶ N) :
    largeFreeYonedaEquivOverSmallScalars.{u, v, t, r} R N X (f ≫ g) =
      g.app (Opposite.op X) (largeFreeYonedaEquivOverSmallScalars.{u, v, t, r} R M X f) := rfl

/-- Lifted free representables separate maps without changing the site. -/
theorem largeFreeYoneda_isSeparatingOverSmallScalars :
    ObjectProperty.IsSeparating
      (.ofObj (largeFreeYonedaFunctorOverSmallScalars.{u, v, t, r} R).obj) := by
  intro M N f g h
  ext ⟨X⟩ m
  obtain ⟨a, rfl⟩ := (largeFreeYonedaEquivOverSmallScalars.{u, v, t, r} R M X).surjective m
  exact congrArg (largeFreeYonedaEquivOverSmallScalars.{u, v, t, r} R N X) (h _ ⟨X⟩ a)

/-- A separator at the larger coefficient size on the original site. -/
theorem hasSeparatorLargeOverSmallScalars : HasSeparator (PresheafOfModules.{max u v r t} R) :=
  ⟨_, (largeFreeYoneda_isSeparatingOverSmallScalars.{u, v, t, r} R).isSeparator_coproduct⟩

/-- The native presheaf-module category is Grothendieck at the stated size. -/
theorem isGrothendieckAbelianLargeOverSmallScalars :
    IsGrothendieckAbelian.{max u v r t} (PresheafOfModules.{max u v r t} R) where
  hasSeparator := hasSeparatorLargeOverSmallScalars.{u, v, t, r} R
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun K _ _ ↦ ⟨⟨fun D _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := K) ⋙ PresheafOfModules.toPresheaf R) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (toPresheaf R)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf R)⟩⟩⟩⟩

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r t}]

/-- Exact sheafification gives Grothendieck module sheaves at the larger size. -/
theorem isGrothendieckAbelianLargeOverSmallScalars :
    IsGrothendieckAbelian.{max u v r t} (SheafOfModules.{max u v r t} R) := by
  let := PresheafOfModules.isGrothendieckAbelianLargeOverSmallScalars.{u, v, t, r} R.obj
  exact
    { hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
      ab5OfSize := ⟨fun K _ _ ↦
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K⟩
      hasSeparator :=
        .of_adjunction (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) }

/-- Enough injectives follows in the original larger-universe module-sheaf category. -/
theorem enoughInjectivesLargeOverSmallScalars :
    EnoughInjectives (SheafOfModules.{max u v r t} R) := by
  let := isGrothendieckAbelianLargeOverSmallScalars.{u, v, t, r} R
  infer_instance

end SheafOfModules
