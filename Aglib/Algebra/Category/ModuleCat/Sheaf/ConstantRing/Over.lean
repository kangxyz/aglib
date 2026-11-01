/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Images
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# The original constant ring on an actual slice site

The existing `constantRingMap` along `Over.forget U` is invertible. Its original
unit factorization identifies it with the sheafification of the restricted
constant unit, which remains locally bijective. Native ringed over-restriction
followed by scalar restriction through this same map is the existing native
module direct image. No arbitrary identification of the two ring sheaves is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r w

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  (Λ : Type r) [Ring Λ]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify (J.over U) RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [(J.over U).WEqualsLocallyBijective RingCat.{r}]
  [(J.over U).HasSheafCompose (CategoryTheory.forget RingCat.{r})]

/-- The original constant-ring morphism to the actual over-restriction is invertible. -/
instance constantRingMap_over_isIso : IsIso (constantRingMap (Over.forget U) (J.over U) J Λ) := by
  let η := Functor.whiskerLeft (Over.forget U).op (constantRingUnit J Λ)
  let : Presheaf.IsLocallySurjective (J.over U) η :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) (constantRingUnit J Λ)
  let : Presheaf.IsLocallyInjective (J.over U) η :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) (constantRingUnit J Λ)
  have hη : (J.over U).W η := (J.over U).W_of_isLocallyBijective η
  have hβ : (J.over U).W (constantRingMap (Over.forget U) (J.over U) J Λ).hom :=
    (J.over U).W.of_precomp (W' := (J.over U).W)
      (constantRingUnit (J.over U) Λ) _
      ((J.over U).W_toSheafify ((Functor.const (Over U)ᵒᵖ).obj (RingCat.of Λ)))
      (by rw [constantRingUnit_comp_constantRingMap]; exact hη)
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp
    ⟨hβ.isLocallyInjective, hβ.isLocallySurjective⟩

/-- The actual constant ring on the slice, through the already specified original ring map. -/
def overRingIso : constantRing (J.over U) Λ ≅ (constantRing J Λ).over U :=
  asIso (constantRingMap (Over.forget U) (J.over U) J Λ)

/-- The slice ring isomorphism retains the original constant-ring morphism. -/
theorem overRingIso_hom : (overRingIso J U Λ).hom =
    constantRingMap (Over.forget U) (J.over U) J Λ := rfl

/-- Its original constant unit is the restriction of the original base constant unit. -/
theorem overRingIso_unit :
    constantRingUnit (J.over U) Λ ≫ (overRingIso J U Λ).hom.hom =
      Functor.whiskerLeft (Over.forget U).op (constantRingUnit J Λ) :=
  constantRingUnit_comp_constantRingMap (Over.forget U) (J.over U) J Λ

/-- Native over-restriction followed by the specified scalar restriction is native direct image. -/
def overFunctorRestrictScalarsIso :
    SheafOfModules.overFunctor.{w} (constantRing J Λ) U ⋙
        SheafOfModules.restrictScalars.{w} (overRingIso J U Λ).hom ≅
      moduleDirectImage (Over.forget U) (J.over U) J Λ := Iso.refl _

/-- The original comparison acts as identity on the original section carrier. -/
theorem overFunctorRestrictScalarsIso_hom_app
    (M : ModuleSheaf.{u, v, r, w} J Λ) (V : (Over U)ᵒᵖ)
    (x : M.val.obj (op V.unop.left)) :
    ((overFunctorRestrictScalarsIso J U Λ).hom.app M).val.app V x = x := rfl

end ModuleCat.Sheaf.ConstantRing
