/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Basic

/-! # Original scalar isomorphisms across nilpotent thickenings

A formally etale algebra which has the same reduced quotient as its base,
through the specified original algebra map, is the base itself. Formal
smoothness constructs an inverse and formal unramifiedness proves its whole
original composite. No finite-presentation or Noetherian hypothesis is used.
-/

@[expose] public noncomputable section

namespace Algebra.FormallyEtale

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [FormallyEtale R S]

/-- A nilpotent quotient comparison constructs an inverse to the original scalar map. -/
def scalarEquivOfNilpotentQuotient (I : Ideal R) (hI : IsNilpotent I)
    (g : S →ₐ[R] R ⧸ I) (hg : IsNilpotent (RingHom.ker g.toRingHom)) : R ≃ₐ[R] S := by
  let l := FormallySmooth.lift I hI g
  let f := Algebra.ofId R S
  have hl : l.comp f = AlgHom.id R R := by
    exact Subsingleton.elim _ _
  have hf : f.comp l = AlgHom.id R S := by
    apply FormallyUnramified.lift_unique' g hg
    ext s
    change g (algebraMap R S (l s)) = g s
    rw [g.commutes]
    exact FormallySmooth.mk_lift I hI g s
  exact AlgEquiv.ofAlgHom f l hf hl

/-- The equivalence uses the unchanged scalar map, not a selected conjugate. -/
@[simp] theorem scalarEquivOfNilpotentQuotient_apply (I : Ideal R) (hI : IsNilpotent I)
    (g : S →ₐ[R] R ⧸ I) (hg : IsNilpotent (RingHom.ker g.toRingHom)) (r : R) :
    scalarEquivOfNilpotentQuotient I hI g hg r = algebraMap R S r := rfl

/-- The inverse reduces to the given original quotient comparison. -/
theorem scalarEquivOfNilpotentQuotient_symm_reduce (I : Ideal R) (hI : IsNilpotent I)
    (g : S →ₐ[R] R ⧸ I) (hg : IsNilpotent (RingHom.ker g.toRingHom)) :
    (Ideal.Quotient.mkₐ R I).comp
      (scalarEquivOfNilpotentQuotient I hI g hg).symm.toAlgHom = g :=
  FormallySmooth.comp_lift I hI g

end Algebra.FormallyEtale
