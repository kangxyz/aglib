/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.FormallyEtale
public import Aglib.RingTheory.NeronModification.ChangeGenerators

/-! # Formally étale modification comparison after changing centre generators

The comparison is the composite of the actual coefficient-extension map and
the actual equivalence supplied by equality of centre ideals.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Algebra.NeronModification

variable {B B' ι κ : Type*} [CommRing B] [CommRing B'] [Algebra B B']
  (p : B) (g : ι → B) (h : κ → B')
  (hcentre : Ideal.span (insert (algebraMap B B' p)
    (Set.range (fun i => algebraMap B B' (g i)))) =
    Ideal.span (insert (algebraMap B B' p) (Set.range h)))

local notation "M" => Modification p g
local notation "N" => Modification (algebraMap B B' p) (fun i => algebraMap B B' (g i))
local notation "C" => Modification (algebraMap B B' p) h

/-- The actual original modification maps to the modification of any generating
family for the extended centre. -/
def baseChangeOfCentreEq : M →ₐ[B] C :=
  ((changeGeneratorsEquiv (algebraMap B B' p)
    (fun i => algebraMap B B' (g i)) h hcentre).toAlgHom.restrictScalars B).comp
      (baseChangeOriginal (B' := B') p g)

/-- The composite comparison preserves the original coefficients. -/
@[simp] theorem baseChangeOfCentreEq_of (b : B) :
    baseChangeOfCentreEq p g h hcentre (of p g b) =
      of (algebraMap B B' p) h (algebraMap B B' b) := by
  change changeGeneratorsEquiv (algebraMap B B' p)
    (fun i => algebraMap B B' (g i)) h hcentre (baseChangeOriginal p g (of p g b)) = _
  rw [baseChangeOriginal_of, changeGeneratorsEquiv_of]

/-- The actual composite comparison is formally étale under flat formally
étale coefficient extension. No domain hypothesis is imposed on either source. -/
theorem formallyEtale_baseChangeOfCentreEq [Module.Flat B B'] [Algebra.FormallyEtale B B'] :
    letI : Algebra M C := @RingHom.toAlgebra M C inferInstance inferInstance
      (baseChangeOfCentreEq p g h hcentre).toRingHom
    Algebra.FormallyEtale M C := by
  let : CommSemiring M := CommRing.toCommSemiring
  let : Semiring M := CommSemiring.toSemiring
  let : CommSemiring N := CommRing.toCommSemiring
  let : Semiring N := CommSemiring.toSemiring
  let : CommSemiring C := CommRing.toCommSemiring
  let : Semiring C := CommSemiring.toSemiring
  let : Algebra M N := @RingHom.toAlgebra M N inferInstance inferInstance
    (baseChangeOriginal (B' := B') p g).toRingHom
  let : Algebra M C := @RingHom.toAlgebra M C inferInstance inferInstance
    (baseChangeOfCentreEq p g h hcentre).toRingHom
  let e : N ≃ₐ[M] C :=
    { (changeGeneratorsEquiv (algebraMap B B' p)
        (fun i => algebraMap B B' (g i)) h hcentre).toRingEquiv with
      commutes' := fun _ => rfl }
  let : Algebra.FormallyEtale M N := formallyEtale_baseChangeOriginal p g
  exact Algebra.FormallyEtale.of_equiv e

end Algebra.NeronModification
