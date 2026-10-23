/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor

/-!
# Degree-zero cohomology maps on sections over `⊤`

Under `Sheaf.H.equiv₀ : H^0(X, M) ≃ Γ(M, ⊤)`, the linear coefficient maps of degree-zero
cohomology are the maps on global sections:

* `Scheme.Cohomology.equiv₀_moduleCohomologyMapOfHom`, for `moduleCohomologyMapOfHom X α g 0`;
* `Scheme.Cohomology.equiv₀_moduleCohomologyFunctorOfHom_mapIso`, for the image of an
  isomorphism under `moduleCohomologyFunctorOfHom X α 0`.

Both are `Sheaf.H.equiv₀_naturality`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Degree-zero cohomology maps, on sections over `⊤`. -/
theorem equiv₀_moduleCohomologyMapOfHom {X : Scheme.{u}} {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) {M N : X.Modules} (g : M ⟶ N)
    (y : Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) :
    Sheaf.H.equiv₀ (moduleAddSheaf X N) Limits.isTerminalTop (moduleCohomologyMapOfHom X α g 0 y) =
      g.val.app (op ⊤) (Sheaf.H.equiv₀ (moduleAddSheaf X M) Limits.isTerminalTop y) :=
  (Sheaf.H.equiv₀_naturality Limits.isTerminalTop ((SheafOfModules.toSheaf _).map g) y).symm

/-- Degree-zero cohomology maps of isomorphisms, on sections over `⊤`. -/
theorem equiv₀_moduleCohomologyFunctorOfHom_mapIso {X : Scheme.{u}} {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) {M N : X.Modules} (i : M ≅ N)
    (y : Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) :
    Sheaf.H.equiv₀ (moduleAddSheaf X N) Limits.isTerminalTop
        (((moduleCohomologyFunctorOfHom X α 0).mapIso i).toLinearEquiv y) =
      i.hom.val.app (op ⊤) (Sheaf.H.equiv₀ (moduleAddSheaf X M) Limits.isTerminalTop y) :=
  (Sheaf.H.equiv₀_naturality Limits.isTerminalTop ((SheafOfModules.toSheaf _).map i.hom) y).symm

end AlgebraicGeometry.Scheme.Cohomology
