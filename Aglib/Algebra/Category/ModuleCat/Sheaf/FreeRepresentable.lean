/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Free
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Native free module sheaves representing original sections

The existing independent-universe free module functor, original representable
presheaf and original sheafification give one fixed free module sheaf. Scalars
need not commute. The section equivalence retains the original coefficient
maps; the value universe contains the site and scalar universes explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace ModuleCat

universe r w

/-- The original independent-scalar free module represents functions from
its original basis, without replacing the coefficient ring. -/
def freeWideHomEquiv {R : Type r} [Ring R] {X : Type (max r w)}
    {M : ModuleCat.{max r w} R} :
    (freeWide R X ⟶ M) ≃ (X ⟶ (forget (ModuleCat.{max r w} R)).obj M) where
  toFun f := ↾fun x => f (Finsupp.single x 1)
  invFun f := freeWideDesc f
  left_inv f := by
    apply freeWide_hom_ext
    intro x
    exact freeWideDesc_single _ _
  right_inv f := by
    ext x
    exact freeWideDesc_single _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The existing free-module functor is left adjoint to the original
forgetful functor at any value universe containing the scalars. -/
def freeWideForgetAdjunction (R : Type r) [Ring R] :
    freeWideFunctor.{r, max r w} R ⊣ forget (ModuleCat.{max r w} R) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ => freeWideHomEquiv
    homEquiv_naturality_left_symm := by
      intro X Y M f g
      apply freeWide_hom_ext
      intro x
      change freeWideDesc (fun y => g (f y)) (Finsupp.single x 1) =
        freeWideDesc (fun y => g y)
          (freeWideDesc (fun y => Finsupp.single (f y) (1 : R)) (Finsupp.single x 1))
      rw [freeWideDesc_single, freeWideDesc_single, freeWideDesc_single] }

/-- The original independent-scalar free functor is a left adjoint. -/
instance freeWideFunctor_isLeftAdjoint (R : Type r) [Ring R] :
    (freeWideFunctor.{r, max r w} R).IsLeftAdjoint :=
  (freeWideForgetAdjunction R).isLeftAdjoint

namespace Sheaf

universe c h t

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Type r) [Ring R]
    [HasSheafify J (ModuleCat.{max c h r t} R)]

/-- The original representable, original free-module functor and original
sheafification, functorially in the original site object. -/
def freeRepresentableFunctor : C ⥤ Sheaf J (ModuleCat.{max c h r t} R) :=
  uliftYoneda.{max c r t} ⋙
    (Functor.whiskeringRight _ _ _).obj (freeWideFunctor.{r, max c h r t} R) ⋙
      presheafToSheaf J (ModuleCat.{max c h r t} R)

/-- The selected native free module sheaf on the actual representable. -/
abbrev freeRepresentable (U : C) : Sheaf J (ModuleCat.{max c h r t} R) :=
  (freeRepresentableFunctor J R).obj U

/-- Original module sections are represented by the selected original free
module sheaf, over an arbitrary possibly noncommutative ring. -/
def freeRepresentableSectionsEquiv (U : C) (F : Sheaf J (ModuleCat.{max c h r t} R)) :
    (freeRepresentable J R U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction J (ModuleCat.{max c h r t} R)).homEquiv _ F).trans
    ((((freeWideForgetAdjunction.{r, max c h t} R).whiskerRight Cᵒᵖ).homEquiv _ F.obj).trans
      uliftYonedaEquiv)

/-- The section representation retains the literal original coefficient map. -/
theorem freeRepresentableSectionsEquiv_naturality
    (U : C) {F G : Sheaf J (ModuleCat.{max c h r t} R)}
    (a : freeRepresentable J R U ⟶ F) (b : F ⟶ G) :
    freeRepresentableSectionsEquiv J R U G (a ≫ b) =
      b.hom.app (op U) (freeRepresentableSectionsEquiv J R U F a) := rfl

/-- Evaluation of the original module sheaf at the original site object. -/
abbrev evaluation (U : C) : Sheaf J (ModuleCat.{max c h r t} R) ⥤
    Type (max c h r t) :=
  (sheafSections J (ModuleCat.{max c h r t} R)).obj (op U) ⋙
    forget (ModuleCat.{max c h r t} R)

/-- The native free module sheaf represents original evaluation, including
its original maps, in the honest common Hom and section universe. -/
def freeRepresentableEvaluationIso (U : C) :
    coyoneda.obj (op (freeRepresentable J R U)) ≅ evaluation J R U :=
  NatIso.ofComponents
    (fun F => (freeRepresentableSectionsEquiv J R U F).toIso)
    (by
      intro F G q
      ext a
      exact freeRepresentableSectionsEquiv_naturality J R U a q)

end Sheaf
end ModuleCat
