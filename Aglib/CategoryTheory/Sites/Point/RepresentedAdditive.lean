/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.Cartesian.CommutativeGroupSections
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Original additive represented fibres at a supplied point

Evaluation descends composition of the actual point arrow with a section. When
the coefficient object is an actual object of the full site inclusion, the germ
of its identity gives the inverse. The supplied point and its original colimit
are used throughout; independent point, Hom and lifted value worlds remain.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.GrothendieckTopology.Point.RepresentedAdditive

universe w uC vC uD vD p e

/-- Evaluate a whole native additive-map equality while the three group objects are variables. -/
private theorem comp_value_of_eq {S T V : AddCommGrpCat.{e}}
    (f : S ⟶ T) (g : T ⟶ V) (r : S ⟶ V) (h : f ≫ g = r) (a : S) :
    g (f a) = r a := by
  have hh := congrArg (fun k : S ⟶ V => k.hom) h
  simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] using
    DFunLike.congr_fun hh a

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [CartesianMonoidalCategory D] [BraidedCategory D] {J : GrothendieckTopology C}
  (Φ : Point.{p} J) (inclusion : C ⥤ D) (P : D)
  (point : ∀ U : C, Φ.fiber.obj U ≃ (P ⟶ inclusion.obj U))
  (point_naturality : ∀ {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U),
    point V (Φ.fiber.map f x) = point U x ≫ inclusion.map f)
  (H : Grp D) [IsCommMonObj H.X]
  [HasColimitsOfSize.{p, p} AddCommGrpCat.{max vD w}]

/-- The original section functor restricted by the actual site inclusion. -/
abbrev presheaf : Cᵒᵖ ⥤ AddCommGrpCat.{max vD w} :=
  inclusion.op ⋙ CommutativeGroupSections.functor.{w} H

/-- Descend actual point-arrow composition on the original section presheaf. -/
def evaluation : (Φ.presheafFiber (A := AddCommGrpCat.{max vD w})).obj (presheaf.{w} inclusion H) ⟶
    AddCommGrpCat.of (CommutativeGroupSections.Sections.{w} H P) :=
  Φ.presheafFiberDesc
    (fun U x => AddCommGrpCat.ofHom (CommutativeGroupSections.pullback.{w} H (point U x)))
    (by
      intro U V f x
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      change ULift.up (Additive.ofMul (point U x ≫ (inclusion.map f ≫ a.down.toMul))) =
        ULift.up (Additive.ofMul (point V (Φ.fiber.map f x) ≫ a.down.toMul))
      rw [point_naturality, Category.assoc])

/-- The whole germ leg is the original additive precomposition map. -/
@[reassoc]
theorem germ_evaluation_hom (U : C) (x : Φ.fiber.obj U) :
    Φ.toPresheafFiber U x (presheaf.{w} inclusion H) ≫
        evaluation.{w} Φ inclusion P point point_naturality H =
      AddCommGrpCat.ofHom (CommutativeGroupSections.pullback.{w} H (point U x)) :=
  Φ.toPresheafFiber_presheafFiberDesc _ _ U x

/-- Evaluation keeps the original point and section on every native germ. -/
theorem evaluation_germ (U : C) (x : Φ.fiber.obj U)
    (a : CommutativeGroupSections.Sections.{w} H (inclusion.obj U)) :
    evaluation.{w} Φ inclusion P point point_naturality H
        (Φ.toPresheafFiber U x (presheaf.{w} inclusion H) a) =
      ULift.up (Additive.ofMul (point U x ≫ a.down.toMul)) := by
  have h := comp_value_of_eq
    (Φ.toPresheafFiber U x (presheaf.{w} inclusion H))
    (evaluation.{w} Φ inclusion P point point_naturality H)
    (AddCommGrpCat.ofHom (CommutativeGroupSections.pullback.{w} H (point U x)))
    (germ_evaluation_hom.{w} Φ inclusion P point point_naturality H U x) a
  refine h.trans ?_
  exact (AddCommGrpCat.ofHom_apply
    (CommutativeGroupSections.pullback.{w} H (point U x)) a).trans
      (CommutativeGroupSections.pullback_apply.{w} H (point U x) a)

variable (V : C) (eH : inclusion.obj V ≅ H.X)

/-- The inverse uses the germ of the identity under the actual coefficient-object comparison. -/
def germ (a : CommutativeGroupSections.Sections.{w} H P) :
    (Φ.presheafFiber (A := AddCommGrpCat.{max vD w})).obj
      (presheaf.{w} inclusion H) :=
  Φ.toPresheafFiber V ((point V).symm (a.down.toMul ≫ eH.inv))
    (presheaf.{w} inclusion H) (ULift.up (Additive.ofMul eH.hom))

/-- The actual identity germ evaluates to its original coefficient point. -/
theorem evaluation_germ_self (a : CommutativeGroupSections.Sections.{w} H P) :
    evaluation.{w} Φ inclusion P point point_naturality H
      (germ.{w} Φ inclusion P point H V eH a) = a := by
  rw [germ, evaluation_germ, Equiv.apply_symm_apply]
  apply ULift.ext
  change Additive.ofMul ((a.down.toMul ≫ eH.inv) ≫ eH.hom) = a.down
  rw [Category.assoc, eH.inv_hom_id, Category.comp_id]
  rfl

variable [inclusion.Full] [LocallySmall.{p} C]
  [PreservesFilteredColimitsOfSize.{p, p} (CategoryTheory.forget AddCommGrpCat.{max vD w})]

/-- Native germ naturality proves the other inverse law on the original representative. -/
theorem germ_evaluation
    (z : (Φ.presheafFiber (A := AddCommGrpCat.{max vD w})).obj
      (presheaf.{w} inclusion H)) :
    germ.{w} Φ inclusion P point H V eH
      (evaluation.{w} Φ inclusion P point point_naturality H z) = z := by
  obtain ⟨U, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
    (A := AddCommGrpCat.{max vD w}) (P := presheaf.{w} inclusion H) z
  have hv := evaluation_germ.{w} Φ inclusion P point point_naturality H U x a
  refine (congrArg (germ.{w} Φ inclusion P point H V eH) hv).trans ?_
  let f : U ⟶ V := inclusion.preimage (a.down.toMul ≫ eH.inv)
  have hf : inclusion.map f = a.down.toMul ≫ eH.inv := inclusion.map_preimage _
  have hp : Φ.fiber.map f x =
      (point V).symm ((point U x ≫ a.down.toMul) ≫ eH.inv) := by
    apply (point V).injective
    rw [point_naturality, Equiv.apply_symm_apply, hf, Category.assoc]
  have ha : (presheaf.{w} inclusion H).map f.op (ULift.up (Additive.ofMul eH.hom)) = a := by
    apply ULift.ext
    change Additive.ofMul (inclusion.map f ≫ eH.hom) = a.down
    rw [hf, Category.assoc, eH.inv_hom_id, Category.comp_id]
    rfl
  have h := comp_value_of_eq
    ((presheaf.{w} inclusion H).map f.op)
    (Φ.toPresheafFiber U x (presheaf.{w} inclusion H))
    (Φ.toPresheafFiber V (Φ.fiber.map f x) (presheaf.{w} inclusion H))
    (Φ.toPresheafFiber_w f x (presheaf.{w} inclusion H))
    (ULift.up (Additive.ofMul eH.hom))
  rw [ha, hp] at h
  exact h.symm

/-- The original evaluation and identity germ identify the actual additive fibre. -/
def iso : (Φ.presheafFiber (A := AddCommGrpCat.{max vD w})).obj
    (presheaf.{w} inclusion H) ≅
    AddCommGrpCat.of (CommutativeGroupSections.Sections.{w} H P) :=
  AddEquiv.toAddCommGrpIso (AddEquiv.ofBijective
    (evaluation.{w} Φ inclusion P point point_naturality H).hom
    ⟨Function.LeftInverse.injective
        (germ_evaluation.{w} Φ inclusion P point point_naturality H V eH),
      Function.RightInverse.surjective
        (evaluation_germ_self.{w} Φ inclusion P point point_naturality H V eH)⟩)

/-- The whole comparison has the original evaluation homomorphism. -/
theorem iso_hom : (iso.{w} Φ inclusion P point point_naturality H V eH).hom =
    evaluation.{w} Φ inclusion P point point_naturality H := rfl

end CategoryTheory.GrothendieckTopology.Point.RepresentedAdditive
