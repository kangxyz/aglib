/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Aglib.CategoryTheory.Sites.ConstantSheaf.Unit

/-! # Original finite constant sections over a one-point scheme

The canonical constant-adjunction unit is bijective. This uses actual trivial
finite covers and preserves the original sheafification and section maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.FiniteEtale

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

attribute [local instance] hasSheafifyLarge

/-- The original trivial-cover isomorphism sends the original constant unit to labels. -/
theorem trivialCoverConstant_unit (X : Scheme.{u}) (A : Type u) [Finite A] :
    toSheafify (smallEtaleTopology X) ((Functor.const X.Etaleᵒᵖ).obj (ULift.{u+1} A)) ≫
      (trivialCoverConstantIso X A).inv.hom = constantTrivialPresheafMap X A := by
  change toSheafify (smallEtaleTopology X) _ ≫
    (sheafifyMap (smallEtaleTopology X) (constantTrivialPresheafMap X A) ≫
      ((sheafificationAdjunction (smallEtaleTopology X) (Type (u+1))).counit.app
        (finiteCoverSectionSheaf (trivialCover X A))).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    sheafificationAdjunction_counit_app_val, toSheafify_sheafifyLift, Category.comp_id]

/-- The additive constant coefficient has the same literal label normalization. -/
theorem setRepresentationIso_presheaf_unit (X : Scheme.{u})
    (A : Type u) [AddCommGroup A] [Finite A] :
    Functor.whiskerRight
      (toSheafify (smallEtaleTopology X) ((Functor.const X.Etaleᵒᵖ).obj (value A)))
      (CategoryTheory.forget AddCommGrpCat.{u+1}) ≫ (setRepresentationIso A X).inv.hom =
        constantTrivialPresheafMap X A := by
  change Functor.whiskerRight (toSheafify (smallEtaleTopology X) _)
      (CategoryTheory.forget AddCommGrpCat.{u+1}) ≫
    (((constantCommuteCompose (smallEtaleTopology X)
      (CategoryTheory.forget AddCommGrpCat.{u+1})).hom.app (value A)).hom ≫
        (trivialCoverConstantIso X A).inv.hom) = _
  rw [← Category.assoc, constantCommuteCompose_toSheafify, Category.assoc,
    trivialCoverConstant_unit]
  rfl

/-- The actual constant-adjunction unit sends each original value to its labelled section. -/
theorem setRepresentationIso_unit_apply (X : Scheme.{u})
    (A : Type u) [AddCommGroup A] [Finite A] (a : value A) :
    (setRepresentationIso A X).inv.hom.app (op (etaleTerminal X))
      (((constantAdjunction X).unit.app (value A)) a) =
        ULift.up (trivialCoverSection X A (etaleTerminal X) a.down) := by
  exact ConcreteCategory.congr_hom
    (congr_app (setRepresentationIso_presheaf_unit X A) (op (etaleTerminal X))) a

variable (X : Scheme.{u}) [Nonempty X] [Subsingleton X]

/-- The canonical constant set-sheaf unit is bijective on the original terminal chart. -/
theorem constantSetUnit_bijective (A : Type u) [Finite A] : Function.Bijective
    ((toSheafify (smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (ULift.{u+1} A))).app (op (etaleTerminal X))) := by
  let T := op (etaleTerminal X)
  let η := (toSheafify (smallEtaleTopology X)
    ((Functor.const X.Etaleᵒᵖ).obj (ULift.{u+1} A))).app T
  let e := (trivialCoverConstantIso X A).inv.hom.app T
  have hm : Function.Bijective ((constantTrivialPresheafMap X A).app T) := by
    have hb := trivialCoverSection_terminal_bijective X A
    constructor
    · intro a b h
      apply ULift.ext
      exact hb.injective (congrArg ULift.down h)
    · intro s
      obtain ⟨a, ha⟩ := hb.surjective s.down
      exact ⟨ULift.up a, congrArg ULift.up ha⟩
  have heq : (fun a => e (η a)) = (fun a => (constantTrivialPresheafMap X A).app T a) := by
    funext a
    exact ConcreteCategory.congr_hom (congr_app (trivialCoverConstant_unit X A) T) a
  apply (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso e) η).mp
  change Function.Bijective (fun a => e (η a))
  rw [heq]
  exact hm

/-- The actual finite additive constant unit has no extra sections on a one-point base. -/
theorem constantUnit_bijective (A : Type u) [AddCommGroup A] [Finite A] :
    Function.Bijective ((constantAdjunction X).unit.app (value A)) := by
  let J := smallEtaleTopology X
  let T := op (etaleTerminal X)
  let η := (toSheafify J ((Functor.const X.Etaleᵒᵖ).obj (value A))).app T
  let e := ((constantCommuteCompose J (CategoryTheory.forget AddCommGrpCat.{u+1})).hom.app
    (value A)).hom.app T
  change Function.Bijective η
  apply (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso e) η).mp
  have heq : (fun a => e (η a)) =
      (fun a => (toSheafify J ((Functor.const X.Etaleᵒᵖ).obj (ULift.{u+1} A))).app T a) := by
    funext a
    exact ConcreteCategory.congr_hom
      (congr_app (constantCommuteCompose_toSheafify J (CategoryTheory.forget AddCommGrpCat.{u+1})
        (value A)) T) a
  change Function.Bijective (fun a => e (η a))
  rw [heq]
  exact constantSetUnit_bijective X A

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
