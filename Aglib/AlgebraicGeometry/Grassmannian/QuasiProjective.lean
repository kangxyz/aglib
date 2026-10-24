/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.PluckerClosedImmersion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-!
# The Grassmannian is projective over its base

For a commutative ring `R` and natural numbers `k` and `n`, the Grassmannian `Gr(R^n, k)` of
rank-`k` quotients of `R^n` is H-projective over `Spec R` (`Grassmannian.isHProjective_toBase`):
the Plücker morphism `Grassmannian.pluckerProjective R k n` is a closed immersion into the
projective space `P(⋀^k R^n)` with the finitely many Plücker coordinates `p_S`, `S` a `k`-subset of
`Fin n` (`Grassmannian.isClosedImmersion_pluckerProjective`). Hence `Gr(R^n, k)` is also
H-quasi-projective, and a quasi-compact immersion into it, for example a Hilbert scheme of
`Aglib.AlgebraicGeometry.HilbertScheme.Representability` over a Noetherian ring, is
H-quasi-projective (`isHQuasiProjective_comp`, `IsHQuasiProjective.comp_of_isImmersion`).

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, p. 9
("Projective embedding" of the Grassmannian by the Plücker sections); the definition of
H-projective is Stacks, Definition 29.44.1 (Tag 01W8), as in
`Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Grassmannian

variable (R : CommRingCat.{u}) (k n : ℕ)

/-- **The Grassmannian is H-projective over its base**, by the Plücker closed immersion into
projective space with the Plücker coordinates. -/
instance isHProjective_toBase : IsHProjective (toBase R k n) :=
  ⟨ULift.{u} (Set.powersetCard (Fin n) k), inferInstance, (pluckerProjective R k n).left,
    inferInstance, Over.w (pluckerProjective R k n)⟩

/-- The structure morphism of the Grassmannian as an object over `Spec R` is H-projective. -/
instance isHProjective_schemeOver_hom : IsHProjective (schemeOver R k n).hom :=
  isHProjective_toBase R k n

end AlgebraicGeometry.Grassmannian
