/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Maps between integral closures after changing the coefficient ring

An actual ambient algebra map induces a map from the original integral closure
into the integral closure over a larger coefficient ring. This constructs only
the map, not a base-change isomorphism. Finiteness is inherited from finiteness
over the larger coefficient ring and its finiteness over the original base.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace integralClosure

section Map

variable (R T L A : Type*) [CommRing R] [CommRing T] [CommRing L] [CommRing A]
  [Algebra R T] [Algebra R L] [Algebra R A] [Algebra T A] [IsScalarTower R T A]

/-- Restrict an actual ambient map while enlarging the coefficient ring. -/
def changeBaseMap (i : L →ₐ[R] A) : integralClosure R L →ₐ[R] integralClosure T A where
  toFun c := ⟨i (c : L), (c.property.map i).tower_top⟩
  map_one' := Subtype.ext (map_one i)
  map_mul' x y := Subtype.ext (map_mul i (x : L) (y : L))
  map_zero' := Subtype.ext (map_zero i)
  map_add' x y := Subtype.ext (map_add i (x : L) (y : L))
  commutes' r := Subtype.ext (i.commutes r)

@[simp] theorem changeBaseMap_coe (i : L →ₐ[R] A) (c : integralClosure R L) :
    (changeBaseMap R T L A i c : A) = i (c : L) := rfl

theorem changeBaseMap_algebraMap (i : L →ₐ[R] A) (r : R) :
    changeBaseMap R T L A i (algebraMap R (integralClosure R L) r) =
      algebraMap R (integralClosure T A) r :=
  (changeBaseMap R T L A i).commutes r

/-- Injectivity retains the original ambient embedding. -/
theorem changeBaseMap_injective (i : L →ₐ[R] A) (hi : Function.Injective i) :
    Function.Injective (changeBaseMap R T L A i) := by
  intro x y h
  apply Subtype.ext
  exact hi (congrArg (fun b : integralClosure T A => (b : A)) h)

/-- The action is induced by the specified map, not a separately selected action. -/
@[instance_reducible]
def changeBaseMapAlgebra (i : L →ₐ[R] A) :
    Algebra (integralClosure R L) (integralClosure T A) :=
  (changeBaseMap R T L A i).toRingHom.toAlgebra

/-- The constructed action preserves the original coefficient action. -/
theorem changeBaseMap_isScalarTower (i : L →ₐ[R] A) :
    letI := changeBaseMapAlgebra R T L A i
    IsScalarTower R (integralClosure R L) (integralClosure T A) := by
  let := changeBaseMapAlgebra R T L A i
  apply IsScalarTower.of_algebraMap_eq'
  exact (changeBaseMap R T L A i).comp_algebraMap.symm

/-- Finiteness over the original coefficient ring implies finiteness over the
original integral closure with precisely the constructed action. -/
theorem changeBaseMap_finite (i : L →ₐ[R] A)
    [Module.Finite R T] [Module.Finite T (integralClosure T A)] :
    letI := changeBaseMapAlgebra R T L A i
    Module.Finite (integralClosure R L) (integralClosure T A) := by
  let := changeBaseMapAlgebra R T L A i
  let := changeBaseMap_isScalarTower R T L A i
  let : Module.Finite R (integralClosure T A) :=
    Module.Finite.trans T (integralClosure T A)
  exact Module.Finite.of_restrictScalars_finite R (integralClosure R L) _

end Map

section Tensor

variable (R T K F L : Type*) [CommRing R] [CommRing T] [Field K] [Field F]
  [CommRing L] [Algebra R T] [Algebra K F] [Algebra K L]
  [Algebra R K] [Algebra R F] [Algebra R L]
  [IsScalarTower R K F] [IsScalarTower R K L]
  [Algebra T (F ⊗[K] L)] [IsScalarTower R T (F ⊗[K] L)]

/-- The original right tensor inclusion induces the change-of-base closure map. -/
def tensorChangeBaseMap :
    integralClosure R L →ₐ[R] integralClosure T (F ⊗[K] L) :=
  changeBaseMap R T L (F ⊗[K] L)
    ((Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L).restrictScalars R)

@[simp] theorem tensorChangeBaseMap_coe (c : integralClosure R L) :
    (tensorChangeBaseMap R T K F L c : F ⊗[K] L) = (1 : F) ⊗ₜ[K] (c : L) := rfl

/-- No nontriviality or field hypothesis on the original right algebra is needed. -/
theorem tensorChangeBaseMap_injective :
    Function.Injective (tensorChangeBaseMap R T K F L) :=
  changeBaseMap_injective R T L (F ⊗[K] L) _
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap K F)))

end Tensor

end integralClosure
