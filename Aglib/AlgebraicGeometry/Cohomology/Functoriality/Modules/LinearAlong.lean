/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules

/-!
# Linearity of module cohomology maps for a prescribed target action

`moduleCohomologyMapAlongLinear f α φ n` is linear for the action of `R` on `H^n(Y, M)` through
`α : R →+* Γ(Y, ⊤)` and on `H^n(X, N)` through the induced map `f.appTop ∘ α`. When the target
action is given by another ring map `α'` that is only propositionally equal to `f.appTop ∘ α`
(for instance the structural map of a scheme over a base, compared through a commutative
triangle), `moduleCohomologyMapAlongLinearOfEq` is the same map, linear for `α'`;
`moduleCohomologyPullbackLinearOfEq` is the case of module pullback, `moduleCohomologyPullback`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `moduleCohomologyMapAlong f φ n` as an `R`-linear map, for the action through
`α : R →+* Γ(Y, ⊤)` on the source and through any `α'` equal to `f.appTop ∘ α` on the
target. -/
def moduleCohomologyMapAlongLinearOfEq {R : Type u} [CommRing R] (α : R →+* Γ(Y, ⊤))
    (α' : R →+* Γ(X, ⊤)) (h : f.appTop.hom.comp α = α') {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom Y α M n
    letI := moduleCohomologyModuleOfHom X α' N n
    Sheaf.H.{u + 1} (moduleAddSheaf Y M) n →ₗ[R] Sheaf.H.{u + 1} (moduleAddSheaf X N) n := by
  subst h
  exact moduleCohomologyMapAlongLinear f α φ n

theorem moduleCohomologyMapAlongLinearOfEq_apply {R : Type u} [CommRing R] (α : R →+* Γ(Y, ⊤))
    (α' : R →+* Γ(X, ⊤)) (h : f.appTop.hom.comp α = α') {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) n) :
    moduleCohomologyMapAlongLinearOfEq f α α' h φ n x = moduleCohomologyMapAlong f φ n x := by
  subst h
  rfl

/-- Module pullback on cohomology, `moduleCohomologyPullback f M n`, as an `R`-linear map for the
action through `α : R →+* Γ(Y, ⊤)` on the source and through any `α'` equal to `f.appTop ∘ α`
on the target. -/
def moduleCohomologyPullbackLinearOfEq {R : Type u} [CommRing R] (α : R →+* Γ(Y, ⊤))
    (α' : R →+* Γ(X, ⊤)) (h : f.appTop.hom.comp α = α') (M : Y.Modules) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom Y α M n
    letI := moduleCohomologyModuleOfHom X α' ((Scheme.Modules.pullback f).obj M) n
    Sheaf.H.{u + 1} (moduleAddSheaf Y M) n →ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X ((Scheme.Modules.pullback f).obj M)) n :=
  moduleCohomologyMapAlongLinearOfEq f α α' h
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) n

theorem moduleCohomologyPullbackLinearOfEq_apply {R : Type u} [CommRing R]
    (α : R →+* Γ(Y, ⊤)) (α' : R →+* Γ(X, ⊤)) (h : f.appTop.hom.comp α = α') (M : Y.Modules)
    (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) n) :
    moduleCohomologyPullbackLinearOfEq f α α' h M n x = moduleCohomologyPullback f M n x :=
  moduleCohomologyMapAlongLinearOfEq_apply f α α' h _ n x

end AlgebraicGeometry.Scheme.Cohomology
