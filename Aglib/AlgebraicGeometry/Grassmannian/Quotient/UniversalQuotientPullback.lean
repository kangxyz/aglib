/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.UniversalKernel

/-!
# The classifying map of the pulled-back universal quotient

For a morphism `φ : T ⟶ schemeOver R k n` over `Spec R` to the Grassmannian of rank-`k` quotients
of `𝒪^n`, the classifying map of the pullback of the universal quotient representative along `φ`
is `φ` (`classifyingMap_pullback_universalQuotientRep`, from `mk_pullback_universalQuotientRep`).
Premise: `BaseChangeMkQFormula`, as in `Grassmannian/Quotient/UniversalKernel`. Consumer: the
Grassmannian point of a pulled-back universal family
(`HilbertScheme/PulledBackGrassmannianPoint`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

variable {R : CommRingCat.{u}} {k n : ℕ}
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- **The classifying map of the pulled-back universal quotient is the given map**: for
`φ : T ⟶ G` to the Grassmannian of rank-`k` quotients of `𝒪^n`,
`classifyingMap (φ^* Q_univ) = φ`. -/
theorem classifyingMap_pullback_universalQuotientRep {T : Over (Spec R)}
    (φ : T ⟶ schemeOver R k n) :
    classifyingMap ((universalQuotientRep R k n).pullback φ.left) = φ := by
  rw [classifyingMap, mk_pullback_universalQuotientRep, Equiv.symm_apply_apply]

end AlgebraicGeometry.Grassmannian
