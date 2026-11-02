/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The actual function-field extension of a finite radicial morphism -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Universal injectivity of a finite dominant map passes to its original
function-field map through the canonical generic-fibre isomorphism. -/
theorem functionFieldMap_universallyInjective
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] [UniversallyInjective f] :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (functionFieldMap f))) := by
  have : IsIso (genericFibreMap f) := genericFibreMap_isIso f
  have h : UniversallyInjective (pullback.snd f (Y.fromSpecStalk (genericPoint Y))) :=
    MorphismProperty.pullback_snd (P := @UniversallyInjective) _ _ inferInstance
  rw [← show genericFibreMap f ≫ pullback.snd f (Y.fromSpecStalk (genericPoint Y)) =
    Spec.map (CommRingCat.ofHom (functionFieldMap f)) from pullback.lift_snd _ _ _]
  exact MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance h

/-- The original generic-stalk field extension of a finite dominant radicial map
is purely inseparable. No normality, characteristic, perfection or Noetherian
hypothesis is imposed. Finiteness is the existing `functionFieldMap_finite`. -/
theorem functionFieldMap_isPurelyInseparable
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] [UniversallyInjective f] :
    (functionFieldMap f).IsPurelyInseparable := by
  let : Algebra Y.functionField X.functionField := functionFieldMapAlgebra f
  change IsPurelyInseparable Y.functionField X.functionField
  have hrad := functionFieldMap_universallyInjective f
  have hinj : ∀ (L : Type u) [Field L], Function.Injective
      (fun a : Spec (.of L) ⟶ Spec X.functionField =>
        a ≫ Spec.map (CommRingCat.ofHom (functionFieldMap f))) :=
    ((tfae_universallyInjective
      (Spec.map (CommRingCat.ofHom (functionFieldMap f)))).out 1 2).mp hrad
  have : Nonempty (X.functionField →+* AlgebraicClosure X.functionField) :=
    ⟨algebraMap _ _⟩
  apply IsPurelyInseparable.of_injective_comp_algebraMap
    Y.functionField X.functionField (AlgebraicClosure X.functionField)
  intro a b hab
  have hab' : CommRingCat.ofHom (functionFieldMap f) ≫ CommRingCat.ofHom a =
      CommRingCat.ofHom (functionFieldMap f) ≫ CommRingCat.ofHom b :=
    CommRingCat.hom_ext hab
  have he : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := by
    apply hinj (AlgebraicClosure X.functionField)
    simpa only [Spec.map_comp] using congrArg Spec.map hab'
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

end AlgebraicGeometry.Scheme
