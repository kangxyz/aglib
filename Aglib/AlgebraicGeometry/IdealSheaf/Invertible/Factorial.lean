/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.StalkKernel
public import Aglib.RingTheory.Ideal.RegularPrincipal
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Ideal.UFD

/-!
# Height-one integral closed subschemes with factorial ambient stalks

Pointwise native domain and unique-factorization data on the actual ambient
stalks make height-one actual closed-immersion stalk kernels principal. Their
nonzero generators give actual singleton ideal bases. The shared stalk-kernel
criterion then supplies local rank one of the actual ideal module, without a
dimension bound.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Hom

variable {C X : Scheme.{u}}

/-- Height-one integral closed subschemes of a locally Noetherian scheme with
factorial actual stalks have locally rank-one actual kernel ideal modules.
Domain and unique-factorization hypotheses refer to the actual ambient stalks. -/
theorem idealModule_isLocallyRankOne_of_factorialStalks
    [IsLocallyNoetherian X] [IsIntegral C] (i : C ⟶ X) [IsClosedImmersion i]
    (hdomain : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (hfactorial : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (hheight : ∀ c : C, (RingHom.ker (i.stalkMap c).hom).height = 1) :
    IsLocallyRankOne X (idealModule i) := by
  apply idealModule_isLocallyRankOne_of_stalkKernelBasis i
  intro c
  let S := X.presheaf.stalk (i c)
  let : IsDomain S := hdomain (i c)
  let : UniqueFactorizationMonoid S := hfactorial (i c)
  have : (RingHom.ker (i.stalkMap c).hom).IsPrime := RingHom.ker_isPrime _
  have hprincipal : (RingHom.ker (i.stalkMap c).hom).IsPrincipal :=
    UniqueFactorizationMonoid.isPrincipal_of_height_eq_one (hheight c)
  obtain ⟨a, hspan⟩ := hprincipal
  have ha : RingHom.ker (i.stalkMap c).hom = Ideal.span {a} := hspan
  have ha0 : a ≠ 0 := by
    intro hzero
    exact (Ideal.ne_bot_of_height_eq_one (hheight c))
      (by rw [ha, hzero, Ideal.span_singleton_zero])
  refine ⟨Ideal.regularPrincipalIdealBasis _ a ?_ ha⟩
  exact IsSMulRegular.of_right_eq_zero_of_smul fun b hb ↦
    (mul_eq_zero.mp hb).resolve_left ha0

end AlgebraicGeometry.Scheme.Hom
