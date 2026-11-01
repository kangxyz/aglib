/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import Aglib.Logic.Function.SquareTransport

/-! # Original cohomology pullback under coefficient isomorphisms

The complete original coefficient-naturality square transports injectivity
and surjectivity, keeping independent source and target Ext universes. These
formal laws have no properness or projective-line dependency.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eX eS

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]

/-- An actual coefficient isomorphism transports surjectivity of the
literal original cohomology pullback. -/
theorem cohomologyPullback_surjective_of_iso (g : S ⟶ X)
    {F G : AbelianSheaf.{u, u + 1} X} (e : F ≅ G) (q : ℕ)
    (hF : Function.Surjective (cohomologyPullback.{u, eX, eS} g F q)) :
    Function.Surjective (cohomologyPullback.{u, eX, eS} g G q) :=
  Function.surjective_of_commutative_square
    (funext (cohomologyPullback_coefficientMap g e.hom q))
    (cohomologyMapIso_bijective ((inverseImage g).mapIso e) q).surjective hF

/-- The same original coefficient square transports injectivity without
any surjectivity premise on the pullback itself. -/
theorem cohomologyPullback_injective_of_iso (g : S ⟶ X)
    {F G : AbelianSheaf.{u, u + 1} X} (e : F ≅ G) (q : ℕ)
    (hF : Function.Injective (cohomologyPullback.{u, eX, eS} g F q)) :
    Function.Injective (cohomologyPullback.{u, eX, eS} g G q) :=
  Function.injective_of_commutative_square
    (funext (cohomologyPullback_coefficientMap g e.hom q))
    (cohomologyMapIso_bijective ((inverseImage g).mapIso e) q).injective
    (cohomologyMapIso_bijective e q).surjective hF


end AlgebraicGeometry.Scheme.EtaleCohomology
