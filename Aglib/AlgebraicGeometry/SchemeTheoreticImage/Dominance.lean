/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Schematic dominance of the native image factor

Every quasi-compact map is schematically dominant onto its actual schematic
image, without reducedness assumptions. This proof is extracted unchanged
from `Descent.FinitePresentation.Properties` for lower geometric consumers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TensorProduct Topology TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The native map to the scheme-theoretic image is schematically dominant
for every quasi-compact morphism. -/
theorem isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  have hinj (U : f.image.Opens) : Function.Injective (f.toImage.app U) :=
    TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
      (F := f.image.sheaf) f.toImage.c U
        (fun x _ => f.stalkFunctor_toImage_injective x)
  constructor
  apply Scheme.IdealSheafData.ext
  funext U
  simpa only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using
    ((RingHom.injective_iff_ker_eq_bot (f.toImage.app U.1).hom).mp (hinj U.1))

end AlgebraicGeometry.Scheme
