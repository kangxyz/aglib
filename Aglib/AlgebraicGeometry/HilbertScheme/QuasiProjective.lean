/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Representability
public import Aglib.AlgebraicGeometry.Grassmannian.QuasiProjective

/-!
# The Hilbert scheme of projective space is quasi-projective

For a Noetherian ring `A`, the Hilbert scheme `hilbertScheme ι n e A Φ r` of `P^n_A`
(`Aglib.AlgebraicGeometry.HilbertScheme.Representability`) is H-quasi-projective over `Spec A`
(`ProjectiveSpace.isHQuasiProjective_hilbertSchemeOver_hom`): `hilbertSchemeι` is an immersion
into the Grassmannian `Gr(A^N, ⌊Φ(r)⌋₊)`, quasi-compact because the Hilbert scheme is Noetherian,
and the Grassmannian is H-projective over `Spec A` by the Plücker embedding
(`Grassmannian.isHProjective_toBase`). In particular the Hilbert scheme is separated and of finite
type over `Spec A`.

This is the strongly quasi-projective representation in Nitsure, *Construction of Hilbert and
Quot schemes*, arXiv:math/0504590v1, §5, Theorem 5.3 (p. 24; the locally closed embedding is
reached on p. 27) for `X = P^n_A` and `E = 𝒪`, without the projectivity step (the valuative
criterion, p. 27); H-quasi-projective is Stacks, Definition 29.41.1 (Tag 01VW), over the affine
base `Spec A`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped Polynomial

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (Φ : ℚ[X]) (r : ℕ)

/-- **The Hilbert scheme of `P^n_A` is H-quasi-projective over `Spec A`**: it is a locally closed
subscheme of a Grassmannian, which the Plücker embedding places in projective space. -/
instance isHQuasiProjective_hilbertSchemeOver_hom :
    IsHQuasiProjective (hilbertSchemeOver ι n e A Φ r).obj.hom :=
  inferInstanceAs (IsHQuasiProjective (hilbertSchemeι ι n e A Φ r ≫
    (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom))

end AlgebraicGeometry.ProjectiveSpace
