/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Classification

/-! The original extension boundary of a torsor lifted over a section. -/

open CategoryTheory CategoryTheory.Limits Opposite

@[expose] public noncomputable section

namespace CategoryTheory.Sheaf

universe u v w e

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]
  {L E F : Sheaf J AddCommGrpCat.{w}}
  (P : Torsor L) (r : P.carrier ⟶ underlyingSetSheaf E)
  (g : E ⟶ F) (z : constantIntegerSheaf J ⟶ F)
  (hover : ∀ U t, g.hom.app U (r.hom.app U t) =
    z.hom.app U ((constantIntegerOne J).hom.app U PUnit.unit))

include hover in
/-- A lift over the given section respects the original augmentation on free generators. -/
private theorem torsorFreeLiftPresheaf_projection_of_section :
    torsorFreeLiftPresheaf P r ≫ g.hom = torsorAugmentationPresheaf P ≫
      toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ))) ≫ z.hom := by
  ext U x
  let G := FreeAbelianGroup (P.carrier.obj.obj U)
  let h := (toSheafify J ((Functor.const Cᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{w} ℤ)))).app U
  let l : G →+ F.obj.obj U := (g.hom.app U).hom.comp
    (FreeAbelianGroup.lift (fun t => (show E.obj.obj U from r.hom.app U t)))
  let r' : G →+ F.obj.obj U := (z.hom.app U).hom.comp
    (h.hom.comp (FreeAbelianGroup.lift (fun _ => (1 : ULift.{w} ℤ))))
  have he : l = r' := by
    apply FreeAbelianGroup.lift_ext
    intro t
    change g.hom.app U
        (FreeAbelianGroup.lift (fun t => (show E.obj.obj U from r.hom.app U t))
          (FreeAbelianGroup.of t)) =
      z.hom.app U (h (FreeAbelianGroup.lift (fun _ => (1 : ULift.{w} ℤ))
        (FreeAbelianGroup.of t)))
    rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      hover, constantIntegerOne_app]
    rfl
  exact DFunLike.congr_fun he x

include hover in
/-- The original sheafified augmentation lies over the given section. -/
private theorem torsorFreeLiftSheaf_projection_of_section :
    torsorFreeLiftSheaf P r ≫ g = torsorAugmentation P ≫ z := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  let A := torsorFreePresheaf P
  let l := (adj.homEquiv A E).symm (torsorFreeLiftPresheaf P r)
  let aug : (presheafToSheaf J AddCommGrpCat.{w}).obj A ⟶ constantIntegerSheaf J :=
    torsorAugmentation P
  apply (adj.homEquiv A F).injective
  change adj.homEquiv A F (l ≫ g) = adj.homEquiv A F (aug ≫ z)
  rw [adj.homEquiv_naturality_right l g, adj.homEquiv_naturality_right aug z]
  change adj.homEquiv A E ((adj.homEquiv A E).symm (torsorFreeLiftPresheaf P r)) ≫ g.hom =
    (toSheafify J A ≫ (torsorAugmentation P).hom) ≫ z.hom
  rw [Equiv.apply_symm_apply]
  exact (torsorFreeLiftPresheaf_projection_of_section P r g z hover).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ z.hom) (toSheafify_naturality J (torsorAugmentationPresheaf P))))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- A lift of the original torsor over a section identifies its original
class with the extension boundary at that section. -/
theorem torsorExtClass_of_extensionLift_of_section
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    (a : constantIntegerSheaf J ⟶ S.X₃)
    (P₀ : Torsor S.X₁) (r₀ : P₀.carrier ⟶ underlyingSetSheaf S.X₂)
    (heq : ∀ U b t, r₀.hom.app U (P₀.action U b t) =
      S.f.hom.app U b + (show S.X₂.obj.obj U from r₀.hom.app U t))
    (hsec : ∀ U t, S.g.hom.app U (r₀.hom.app U t) =
      a.hom.app U ((constantIntegerOne J).hom.app U PUnit.unit)) :
    torsorExtClass P₀ = (Abelian.Ext.mk₀ a).comp hS.extClass (zero_add 1) := by
  let f : torsorAugmentationComplex P₀ ⟶ S :=
    { τ₁ := torsorDifferenceSheafMap P₀
      τ₂ := torsorFreeLiftSheaf P₀ r₀
      τ₃ := a
      comm₁₂ := (torsorFreeLiftSheaf_kernel P₀ r₀ S.f heq).symm
      comm₂₃ := torsorFreeLiftSheaf_projection_of_section P₀ r₀ S.g a hsec }
  have h := ShortComplex.ShortExact.extClass_naturality (torsorAugmentation_shortExact P₀) hS f
  exact (torsorExtClass_eq P₀).trans h

/-- The original fibre torsor at a section has the original extension class
precomposed with that same section. -/
theorem torsorExtClass_extensionFiber_section
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    (a : constantIntegerSheaf J ⟶ S.X₃) :
    torsorExtClass
        (extensionFiberTorsor S (constantIntegerOne J ≫
          (sheafCompose J (forget AddCommGrpCat.{w})).map a) hS) =
      (Abelian.Ext.mk₀ a).comp hS.extClass (zero_add 1) := by
  let z₀ := constantIntegerOne J ≫ (sheafCompose J (forget AddCommGrpCat.{w})).map a
  let P₀ := extensionFiberTorsor S z₀ hS
  let r₀ := extensionFiberInclusion S z₀
  exact torsorExtClass_of_extensionLift_of_section S hS a P₀ r₀
    (fun _ _ _ => rfl) (fun _ t => t.property)

end CategoryTheory.Sheaf
