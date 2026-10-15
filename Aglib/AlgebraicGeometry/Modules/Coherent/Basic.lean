/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Mathlib.AlgebraicGeometry.Noetherian
/-!
# Affine-locally quasicoherent sheaves of finite type

The predicate is defined for every scheme and tests every actual affine open chart.
Under local noetherianity the full category is abelian, its standard exact
structure agrees with ambient sheaf exactness, and the inclusion is exact.
Its stated size bound is the sheaf-object universe `u+1`.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Every affine chart of a locally noetherian scheme has a noetherian ring. -/
theorem noetherian_affineChart {X : Scheme.{u}} [IsLocallyNoetherian X]
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j] : IsNoetherianRing R := by
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion j
  exact isLocallyNoetherian_Spec.mp this

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

instance affineLocallyFiniteType_containsZero : (affineLocallyFiniteType X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun R j _ => by
    let : IsNoetherianRing R := noetherian_affineChart R j
    exact (affineFiniteSheaf R).prop_of_isZero
      ((Scheme.Modules.restrictFunctor j).map_isZero (isZero_zero _))⟩

instance affineLocallyFiniteType_finiteLimits : (affineLocallyFiniteType
  X).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ :=
    { limitsOfShape_le := by
        rintro M ⟨p⟩ R j _
        let : IsNoetherianRing R := noetherian_affineChart R j
        exact (affineFiniteSheaf R).prop_of_isLimit
          (isLimitOfPreserves (Scheme.Modules.restrictFunctor j) p.isLimit)
          (fun i => p.prop_diag_obj i R j) }

instance affineLocallyFiniteType_finiteColimits : (affineLocallyFiniteType
  X).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ :=
    { colimitsOfShape_le := by
        rintro M ⟨p⟩ R j _
        let : IsNoetherianRing R := noetherian_affineChart R j
        exact (affineFiniteSheaf R).prop_of_isColimit
          (isColimitOfPreserves (Scheme.Modules.restrictFunctor j) p.isColimit)
          (fun i => p.prop_diag_obj i R j) }

instance affineLocallyFiniteType_kernels : (affineLocallyFiniteType X).IsClosedUnderKernels where
  kernels_le := by
    rintro M ⟨f, k, hk, h⟩
    exact (affineLocallyFiniteType X).prop_of_isLimit hk
      (by rintro (_ | _) <;> first | exact h.1 | exact h.2)

instance affineLocallyFiniteType_cokernels : (affineLocallyFiniteType X).IsClosedUnderCokernels
  where
  cokernels_le := by
    rintro M ⟨f, k, hk, h⟩
    exact (affineLocallyFiniteType X).prop_of_isColimit hk
      (by rintro (_ | _) <;> first | exact h.1 | exact h.2)

instance instAbelianCoherent : Abelian (FiniteTypeSheaves X) := inferInstance

end AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme

/-- Coherent sheaves on a locally Noetherian scheme, represented by the
actual affine-locally finite-type quasicoherent module sheaves. The explicit
Noetherian hypothesis guards this identification. -/
-- The instance enforces the coherent domain of this finite-type category alias.
@[nolint unusedArguments]
abbrev CoherentSheaf (X : Scheme.{u}) [IsLocallyNoetherian X] :=
  Modules.QuasiCoherent.FiniteTypeSheaves X

end AlgebraicGeometry.Scheme
