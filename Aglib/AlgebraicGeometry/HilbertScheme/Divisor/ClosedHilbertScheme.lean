/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Divisor.Representability
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.ClosedImmersion

/-!
# `Div^θ_X` for a closed subscheme `X ⊆ P^n_A`, through its closed Hilbert scheme

Let `A` be a Noetherian ring, `e : ι ≃ Fin (n + 1)`, `i : X ⟶ P^n_A = ProjectiveSpace A ι` a closed
immersion over `Spec A` (`hi : i ≫ toSpec A ι = πX`) with `X` flat over `A`, and `θ ∈ ℚ[X]`.

`exists_locallyNoetherianRelativeDivisorFunctor_representableBy`: **`Div^θ_X` is represented on
locally Noetherian test schemes by an H-quasi-projective Noetherian scheme over `Spec A`** (Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, Thm 3.7, statement p. 23, proof p. 24, with fibre
Hilbert polynomial `θ`). The witness is `divisorSchemeOver E`
(`HilbertScheme/Divisor/Representability`), the open divisor locus of the closed Hilbert scheme of
`C = i.ker` for the representation
`E = locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion …` of the Hilbert
functor of `X` (`HilbertScheme/Immersed/ClosedImmersion`), for a large `r` and sections of `𝒪(r)`
cutting out `C`. It is H-quasi-projective as an open subscheme of the H-quasi-projective closed
Hilbert scheme (`isHQuasiProjective_divisorSchemeOver_hom`,
`isHQuasiProjective_closedHilbertSchemeOver_hom`), hence Noetherian.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] {X : Scheme.{u}} {πX : X ⟶ Spec (CommRingCat.of A)}
  (i : X ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πX) [IsClosedImmersion i] (θ : ℚ[X])

include e in
/-- **`Div^θ_X` is representable by an H-quasi-projective Noetherian scheme** (Kleiman,
arXiv:math/0504020v1, Thm 3.7, statement p. 23, proof p. 24, with fibre Hilbert polynomial `θ`, on
locally Noetherian test schemes): for a Noetherian ring `A`, `e : ι ≃ Fin (n + 1)`, a closed
immersion `i : X ⟶ P^n_A` with `X` flat over `A` and `θ ∈ ℚ[X]`, the functor `Div^θ_X` of relative
effective Cartier divisors with fibre Hilbert polynomial `θ` is represented by an
H-quasi-projective, hence Noetherian, scheme over `Spec A`. The witness is `divisorSchemeOver E`,
the open divisor locus of the closed Hilbert scheme representing `Hilb^θ_X`; its openness there
(`isOpenImmersion_divisorSchemeι`) is not part of this statement. -/
theorem exists_locallyNoetherianRelativeDivisorFunctor_representableBy [Flat πX] :
    ∃ D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)),
      IsHQuasiProjective D.obj.hom ∧ IsNoetherian D.obj.left ∧
        Nonempty ((locallyNoetherianRelativeDivisorFunctor i hi θ).RepresentableBy D) := by
  obtain ⟨H, hH, ⟨E⟩⟩ :=
    exists_locallyNoetherianImmersedHilbertFunctor_representableBy_of_isClosedImmersion ι n e A i hi
      θ
  have : Finite ι := Finite.of_equiv _ e.symm
  exact ⟨divisorSchemeOver E, inferInstance,
    IsHQuasiProjective.isNoetherian (divisorSchemeOver E).obj.hom,
    ⟨locallyNoetherianRelativeDivisorFunctorRepresentableBy E⟩⟩

end AlgebraicGeometry.ProjectiveSpace
