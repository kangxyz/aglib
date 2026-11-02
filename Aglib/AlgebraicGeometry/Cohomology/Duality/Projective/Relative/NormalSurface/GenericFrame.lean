/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.StalkGorenstein
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# A chosen frame of the original canonical generic stalk

The original function field is the stalk at the generic point. Its native
field structure supplies self-injective dimension zero, so the existing
canonical-stalk comparison gives a chosen frame there. No singular stalk
is assumed Gorenstein, and no canonical frame or generic rank is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
  (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
  [IsDominant (i ≫ toSpec R ι)]
  (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι i).Finite)

/-- A chosen frame of the original canonical stalk at the generic point,
linear over the original function field. This frame is not canonically normalized. -/
def normalSurfaceCanonicalGenericFrame :
    ((moduleStalk X (genericPoint X)).obj (normalSurfaceCanonicalModule R ι i n)) ≃ₗ[
      X.functionField] X.functionField := by
  let : Module.Injective X.functionField X.functionField :=
    Module.injective_of_isSemisimpleRing _ _
  let : Injective (ModuleCat.of X.functionField X.functionField) :=
    Module.injective_object_of_injective_module _ _
  let : HasInjectiveDimensionLE (ModuleCat.of X.functionField X.functionField) 0 :=
    (injective_iff_hasInjectiveDimensionLE_zero _).mp inferInstance
  exact normalSurfaceCanonicalStalkLinearEquivOfSelfInjectiveDimension
    R ι i hX hXdim n e hfin (genericPoint X) 0

end AlgebraicGeometry.Scheme.Cohomology
