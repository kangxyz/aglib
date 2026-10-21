/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.BaseChange

/-! # Scalar-extension coordinates and original pure tensors -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {M N : ModuleCat.{u} R} {P : ModuleCat.{u} S}
  (d : (extendScalars (algebraMap R S)).obj M ≅ P) (e : M ≅ N)

/-- Combine the specified scalar-extension comparison with original module coordinates. -/
def scalarExtensionCoordinatesIso : P ≅ ModuleCat.of S (S ⊗[R] N) :=
  d.symm ≪≫ (extendScalars (algebraMap R S)).mapIso e ≪≫
    extendScalarsAlgebraIso R S N

/-- The inverse coordinate map retains the original pure tensor and comparison. -/
theorem scalarExtensionCoordinatesIso_inv_tmul (s : S) (n : N) :
    (scalarExtensionCoordinatesIso d e).inv (s ⊗ₜ[R] n) =
      d.hom (s ⊗ₜ[R,algebraMap R S] e.inv n) := by
  change d.hom (((extendScalars (algebraMap R S)).map e.inv)
    ((extendScalarsAlgebraIso R S N).inv (s ⊗ₜ[R] n))) = _
  rw [extendScalarsAlgebraIso_inv_tmul]
  rfl

end ModuleCat
