/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineEffectivityHom
public import Aglib.RingTheory.AdicCompletion.BoundedReconstruction

/-!
# Separation of actual affine formal coefficients and cokernels

Finite completed coefficients supply separation of the actual cokernel,
not merely separation of its target. This is the geometric input needed to
recover bounds from the original finite-stage maps. No adic condition on a
kernel or cokernel system is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u

variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} (F : AdicSystem (Spec B) K)

/-- The original compatible-family module is separated over the original
chart ring, even though it is generally finite only over its completion. -/
theorem affineFormalSections_isHausdorff :
    IsHausdorff (affineIdeal B K) F.affineFormalSections := by
  let : IsAdicComplete (affineIdeal B K) F.affineFormalSections :=
    F.affineSections_isCompatibleSystem.sections_isAdicComplete
      (IsNoetherian.noetherian _)
  infer_instance

variable {F} {G : AdicSystem (Spec B) K} (φ : F ⟶ G)

/-- The actual cokernel of the original completed-linear formal morphism
is separated for the original ideal after restriction of scalars. -/
theorem affineFormalSectionsMap_cokernel_isHausdorff :
    let := F.affineFormalSectionsModule
    let := G.affineFormalSectionsModule
    let := F.affineSections_isCompatibleSystem.sectionsScalarTower
    let := G.affineSections_isCompatibleSystem.sectionsScalarTower
    IsHausdorff (affineIdeal B K)
      (G.affineFormalSections ⧸ ((affineFormalSectionsMap φ).restrictScalars B).range) := by
  let := F.affineFormalSectionsModule
  let := G.affineFormalSectionsModule
  let := F.affineSections_isCompatibleSystem.sectionsScalarTower
  let := G.affineSections_isCompatibleSystem.sectionsScalarTower
  let : Module.Finite (AdicCompletion (affineIdeal B K) B) G.affineFormalSections :=
    G.affineFormalSections_finite
  let f := affineFormalSectionsMap φ
  let C := G.affineFormalSections ⧸ f.range
  let : IsAdicComplete (affineIdeal B K) C :=
    AdicCompletion.isAdicComplete_of_finite_completed (affineIdeal B K)
  change IsHausdorff (affineIdeal B K)
    (G.affineFormalSections ⧸ (f.restrictScalars B).range)
  rw [LinearMap.range_restrictScalars]
  let e := Submodule.Quotient.restrictScalarsEquiv B f.range
  refine ⟨fun x hx => ?_⟩
  apply e.injective
  rw [map_zero]
  apply IsHausdorff.haus' (I := affineIdeal B K)
  intro n
  apply SModEq.zero.mpr
  exact Submodule.smul_top_le_comap_smul_top ((affineIdeal B K) ^ n)
    e.toLinearMap (SModEq.zero.mp (hx n))

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
