/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Retract

/-!
# Testing tensor exactness on actual commutative ring extensions

An actual coefficient retraction descends exactness of the original two tensor
differentials. Every module is a split summand of its native square-zero
extension. Consequently exactness after every commutative ring scalar
extension implies exactness after every module tensor product. No flatness
or independently supplied universal module exactness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{v} R))

/-- A native coefficient retraction descends exactness of the original tensor
differentials, with independent coefficient and original module universes. -/
theorem lTensor_exact_of_coefficient_retract {M N : ModuleCat.{w} R}
    (r : Retract M N)
    (h : Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N)) :
    Function.Exact (S.f.hom.lTensor M) (S.g.hom.lTensor M) := by
  have hi : (S.g.hom.lTensor N).comp (r.i.hom.rTensor S.X₂) =
      (r.i.hom.rTensor S.X₃).comp (S.g.hom.lTensor M) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hp : (S.f.hom.lTensor M).comp (r.r.hom.rTensor S.X₁) =
      (r.r.hom.rTensor S.X₂).comp (S.f.hom.lTensor N) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hri : r.r.hom.comp r.i.hom = LinearMap.id :=
    congrArg ModuleCat.Hom.hom r.retract
  intro x
  constructor
  · intro hx
    have hxN : (S.g.hom.lTensor N) ((r.i.hom.rTensor S.X₂) x) = 0 := by
      change ((S.g.hom.lTensor N).comp (r.i.hom.rTensor S.X₂)) x = 0
      rw [hi]
      simp only [LinearMap.comp_apply, hx, map_zero]
    obtain ⟨y, hy⟩ := (h _).mp hxN
    refine ⟨(r.r.hom.rTensor S.X₁) y, ?_⟩
    change ((S.f.hom.lTensor M).comp (r.r.hom.rTensor S.X₁)) y = x
    rw [hp]
    change (r.r.hom.rTensor S.X₂) ((S.f.hom.lTensor N) y) = x
    rw [hy]
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hri,
      LinearMap.rTensor_id, LinearMap.id_apply]
  · rintro ⟨y, rfl⟩
    have hw : S.g.hom.comp S.f.hom = 0 := by
      ext z
      exact S.moduleCat_zero_apply z
    change ((S.g.hom.lTensor M).comp (S.f.hom.lTensor M)) y = 0
    rw [← LinearMap.lTensor_comp, hw]
    simp

/-- Testing exactness after every original native commutative-ring scalar
extension suffices for exactness after every module tensor product. The test
module is the actual split summand in its native square-zero extension. -/
theorem universally_lTensor_exact_of_extendScalars_exact
    (h : ∀ (B : Type u) [CommRing B] (σ : R →+* B),
      (S.map (ModuleCat.extendScalars.{u, u, v} σ)).Exact)
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N) := by
  let : Module Rᵐᵒᵖ N := Module.compHom N (RingEquiv.toOpposite R).symm.toRingHom
  let : IsCentralScalar R N := ⟨fun _ _ => rfl⟩
  let B := TrivSqZeroExt R N
  let σ : R →+* B := algebraMap R B
  let B' := (ModuleCat.restrictScalars σ).obj (ModuleCat.of B B)
  let e : ModuleCat.of R B ≃ₗ[R] B' :=
    { __ := AddEquiv.refl B
      map_smul' r b := by
        change r • b = σ r * b
        exact Algebra.smul_def r b }
  let r : Retract (ModuleCat.of R N) B' :=
    { i := ModuleCat.ofHom (X := ModuleCat.of R N) (Y := B')
        (e.toLinearMap.comp (TrivSqZeroExt.inrHom R N))
      r := ModuleCat.ofHom (X := B') (Y := ModuleCat.of R N)
        ((TrivSqZeroExt.sndHom R N).comp e.symm.toLinearMap)
      retract := by ext n; rfl }
  have hB : Function.Exact (S.f.hom.lTensor B') (S.g.hom.lTensor B') :=
    (ShortExact.moduleCat_exact_iff_function_exact
      (S.map (ModuleCat.extendScalars σ))).mp (h B σ)
  exact S.lTensor_exact_of_coefficient_retract r hB

end CategoryTheory.ShortComplex
