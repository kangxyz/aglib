/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.BaseChange
public import Mathlib.RingTheory.Etale.Basic

/-! # Formally étale comparison of Néron modifications

Flat formally étale coefficient extension makes the actual comparison of
modifications formally étale. The algebra action is induced by
`baseChangeOriginal`, not an independently supplied comparison map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Algebra.NeronModification

variable {B B' ι : Type*} [CommRing B] [CommRing B'] [Algebra B B']
  [Module.Flat B B'] [Algebra.FormallyEtale B B'] (p : B) (g : ι → B)

local notation "M" => Modification p g
local notation "N" => Modification (algebraMap B B' p) (fun i => algebraMap B B' (g i))

/-- The actual comparison of modifications is formally étale whenever the
coefficient map is flat and formally étale. -/
theorem formallyEtale_baseChangeOriginal :
    letI : Algebra M N := @RingHom.toAlgebra M N inferInstance inferInstance
      (baseChangeOriginal (B' := B') p g).toRingHom
    Algebra.FormallyEtale M N := by
  let : Algebra M N := @RingHom.toAlgebra M N inferInstance inferInstance
    (baseChangeOriginal (B' := B') p g).toRingHom
  let : CommSemiring M := CommRing.toCommSemiring
  let : Semiring M := CommSemiring.toSemiring
  let V := M ⊗[B] B'
  let : CommRing V := Algebra.TensorProduct.instCommRing (R := B) (A := M) (B := B')
  let : CommSemiring V := CommRing.toCommSemiring
  let : Semiring V := CommSemiring.toSemiring
  let : Algebra M V :=
    Algebra.TensorProduct.leftAlgebra (R := B) (S := M) (A := M) (B := B')
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
  let : Algebra.FormallyEtale M T := by
    with_reducible_and_instances
      exact Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.commRight B M B')
  exact Algebra.FormallyEtale.of_equiv e

end Algebra.NeronModification
