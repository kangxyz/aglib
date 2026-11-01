/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsors.Represented

/-! # Actual equivariant categorical isomorphisms on represented sheaf torsors

The existing reverse torsor construction sends the supplied actual equivariant
carrier isomorphism to its original lifted Yoneda map. Both torsor carriers and
actions stay those of the selected represented construction; no comparison
isomorphism or equivariance conclusion is introduced as an existence premise.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Sheaf.Torsor.Represented

universe w uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {J : GrothendieckTopology C} {H : Grp D} [IsCommMonObj H.X]
  {hH : Presheaf.IsSheaf J (CommutativeGroupSections.testPresheaf.{w} F H)}
  (Y Z : D)
  {hY : Presheaf.IsSheaf J (LiftedRestrictedYoneda.presheaf.{w} F Y)}
  {hZ : Presheaf.IsSheaf J (LiftedRestrictedYoneda.presheaf.{w} F Z)}
  (τ : TorsorAction H (toUnit Y)) (σ : TorsorAction H (toUnit Z))
  (locY : ∀ U : C, nonemptySieve (LiftedRestrictedYoneda.sheaf.{w} F J Y hY) U ∈ J U)
  (locZ : ∀ U : C, nonemptySieve (LiftedRestrictedYoneda.sheaf.{w} F J Z hZ) U ∈ J U)
  (q : Y ≅ Z)
  (hq : ∀ {T : D} (a : T ⟶ H.X) (x : T ⟶ Y),
    τ.act a x ≫ q.hom = σ.act a (x ≫ q.hom))

/-- Whole reverse-map assembly on the original represented carriers and actions. -/
def ofCategoricalIso :
    Torsor.Iso (ofCategoricalAction (hH := hH) Y τ locY)
      (ofCategoricalAction (hH := hH) Z σ locZ) where
  carrierIso := LiftedRestrictedYoneda.sheafMapIso.{w} F J hY hZ q
  equivariant _U a t := congrArg ULift.up (hq a.down.toMul t.down)

/-- The actual carrier map is precisely the original lifted postcomposition. -/
@[simp] theorem ofCategoricalIso_hom_app (U : Cᵒᵖ) (x : F.obj U.unop ⟶ Y) :
    (ofCategoricalIso (hH := hH) Y Z τ σ locY locZ q hq).carrierIso.hom.hom.app U
        (ULift.up x) =
      ULift.up (x ≫ q.hom) := rfl

end CategoryTheory.Sheaf.Torsor.Represented
