/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Localization of Néron modifications

The actual coefficient comparison is a localization of the original modification.
Its algebra structure is induced by that comparison, not an independently chosen action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Algebra.NeronModification

variable {B B' ι : Type*} [CommRing B] [CommRing B'] [Algebra B B']
variable (p : B) (g : ι → B) (S : Submonoid B) [IsLocalization S B']

local notation "M" => Modification p g
local notation "N" => Modification (algebraMap B B' p) (fun i => algebraMap B B' (g i))

/-- Localizing the coefficient ring localizes the actual modification at the old scalars. -/
theorem isLocalization_baseChangeOriginal :
    letI : Algebra M N := @RingHom.toAlgebra M N inferInstance inferInstance
      (baseChangeOriginal (B' := B') p g).toRingHom
    IsLocalization (R := M) (Algebra.algebraMapSubmonoid M S) N := by
  let : Algebra M N := @RingHom.toAlgebra M N inferInstance inferInstance
      (baseChangeOriginal (B' := B') p g).toRingHom
  let : Module.Flat B B' := IsLocalization.flat B' S
  let T := B' ⊗[B] M
  let : CommRing T := Algebra.TensorProduct.instCommRing (R := B) (A := B') (B := M)
  let : CommSemiring T := CommRing.toCommSemiring
  let : Semiring T := CommSemiring.toSemiring
  let : Algebra M T :=
    Algebra.TensorProduct.rightAlgebra (R := B) (A := B') (B := M)
  let e : T ≃ₐ[M] N :=
    { (baseChangeAlgEquiv (B' := B') p g).toRingEquiv with
      commutes' := fun m => by
        change baseChangeForward p g ((1 : B') ⊗ₜ[B] m) = baseChangeOriginal p g m
        rw [baseChangeForward_tmul, map_one, one_mul] }
  have : IsLocalization (R := M) (Algebra.algebraMapSubmonoid M S) T := by
    with_reducible_and_instances
      exact IsLocalization.tensorRight (R := B) (S := M) B' S
  exact IsLocalization.isLocalization_of_algEquiv (Algebra.algebraMapSubmonoid M S) e

end Algebra.NeronModification
