/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FieldGaloisObject
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisBaseChange

/-! # The original function fields of an integral Galois cover

The canonical generic-fibre map identifies the unchanged generic pullback with
its original function-field spectrum. Connected base change and the actual
spectrum correspondence then give field Galoisness and the original deck
cardinality. No normality or auxiliary field realization is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericGalois

universe u

variable {X : Scheme.{u}} [IsIntegral X] (Y : FiniteEtale X) [IsIntegral Y.obj.left]

/-- An integral finite-etale cover is dominant, by openness and nonemptiness. -/
theorem dominant : IsDominant Y.obj.hom :=
  ⟨Y.obj.hom.isOpenMap.denseRange_of_isPreirreducibleSpace⟩

attribute [local instance] dominant

/-- The algebra structure is exactly the original generic-stalk map. -/
@[instance_reducible] def algebra : Algebra X.functionField Y.obj.left.functionField :=
  (functionFieldMap Y.obj.hom).toAlgebra

attribute [local instance] algebra

/-- The actual function-field spectrum is finite etale over the original generic field. -/
theorem functionField_finiteEtale :
    Module.Finite X.functionField Y.obj.left.functionField ∧
      Algebra.Etale X.functionField Y.obj.left.functionField := by
  let : IsIso (genericFibreMap Y.obj.hom) := genericFibreMap_isIso Y.obj.hom
  have heq : genericFibreMap Y.obj.hom ≫
      pullback.snd Y.obj.hom (X.fromSpecStalk (genericPoint X)) =
      Spec.map (CommRingCat.ofHom (functionFieldMap Y.obj.hom)) :=
    pullback.lift_snd _ _ _
  have hf : IsFinite (Spec.map (CommRingCat.ofHom (functionFieldMap Y.obj.hom))) := by
    rw [← heq]
    infer_instance
  have he : Etale (Spec.map (CommRingCat.ofHom (functionFieldMap Y.obj.hom))) := by
    rw [← heq]
    infer_instance
  exact ⟨RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf),
    RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp he)⟩

local instance : Module.Finite X.functionField Y.obj.left.functionField :=
  (functionField_finiteEtale Y).1
local instance : Algebra.Etale X.functionField Y.obj.left.functionField :=
  (functionField_finiteEtale Y).2

/-- The original generic-fibre lift, as an isomorphism of finite-etale objects. -/
def fieldSpectrumIso :
    (finiteEtaleSpecFunctor X.functionField).obj
        (op (CommAlgCat.FiniteEtale.of X.functionField Y.obj.left.functionField)) ≅
      (baseChange (X.fromSpecStalk (genericPoint X))).obj Y := by
  let : IsIso (genericFibreMap Y.obj.hom) := genericFibreMap_isIso Y.obj.hom
  apply ObjectProperty.isoMk _
  let e : Spec Y.obj.left.functionField ≅
      pullback Y.obj.hom (X.fromSpecStalk (genericPoint X)) :=
    asIso (genericFibreMap Y.obj.hom)
  exact Over.isoMk e (pullback.lift_snd _ _ _)

/-- The actual generic pullback is integral, not merely categorically connected. -/
theorem genericPullback_isIntegral :
    IsIntegral ((baseChange (X.fromSpecStalk (genericPoint X))).obj Y).obj.left := by
  let : IsIso (genericFibreMap Y.obj.hom) := genericFibreMap_isIso Y.obj.hom
  exact @IsIntegral.of_isIso (Spec Y.obj.left.functionField)
    (pullback Y.obj.hom (X.fromSpecStalk (genericPoint X))) inferInstance
    (genericFibreMap Y.obj.hom) (genericFibreMap_isIso Y.obj.hom)

variable [IsGalois Y]

/-- A categorical integral Galois cover gives a Galois extension of its original
function fields, with precisely the original function-field map as algebra. -/
theorem functionField_isGalois : _root_.IsGalois X.functionField Y.obj.left.functionField := by
  let : IsIntegral ((baseChange (X.fromSpecStalk (genericPoint X))).obj Y).obj.left :=
    genericPullback_isIntegral Y
  let : IsGalois ((baseChange (X.fromSpecStalk (genericPoint X))).obj Y) :=
    baseChange_isGalois_of_connected _ Y
  exact isGalois_of_iso_fieldSpectrum X.functionField Y.obj.left.functionField _
    (fieldSpectrumIso Y).symm

/-- The field automorphisms of the original function-field extension have the
same cardinal as the original cover's deck automorphisms. -/
theorem card_functionFieldAut :
    Nat.card (Y.obj.left.functionField ≃ₐ[X.functionField] Y.obj.left.functionField) =
      Nat.card (Aut Y) := by
  let : IsIntegral ((baseChange (X.fromSpecStalk (genericPoint X))).obj Y).obj.left :=
    genericPullback_isIntegral Y
  exact (card_fieldAut_of_iso_fieldSpectrum X.functionField Y.obj.left.functionField _
    (fieldSpectrumIso Y).symm).trans (baseChange_card_aut_of_connected _ Y)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericGalois
