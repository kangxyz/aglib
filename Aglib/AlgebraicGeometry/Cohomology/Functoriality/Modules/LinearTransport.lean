/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.LinearAlong
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso

/-! # The original composite linear cohomology transport

Construct the same coefficient map composed with scalar-compatible pullback,
and its bijectivity witness, before supplying concrete schemes and modules.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original coefficient cohomology map after original scalar-compatible
pullback, as one linear equivalence. The target scalar action is supplied by
its actual equality with the induced action; the underlying map remains the
literal composite, rather than changing to a different scalar-restriction mate. -/
def moduleCohomologyPullbackCoefficientLinearEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {R : Type u} [CommRing R] (α : R →+* Γ(Y, ⊤)) (β : R →+* Γ(X, ⊤))
    (h : f.appTop.hom.comp α = β) (M : Y.Modules) {N : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N) (q : ℕ) :
    letI := moduleCohomologyModuleOfHom Y α M q
    letI := moduleCohomologyModuleOfHom X β N q
    Sheaf.H.{u + 1} (moduleAddSheaf Y M) q ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X N) q :=
  LinearEquiv.ofBijective
    ((moduleCohomologyMapOfHom X β e.hom q).comp
      (moduleCohomologyPullbackLinearOfEq f α β h M q))
    (by
      refine (Function.Bijective.of_comp_iff' (bijective_sheafH_map_of_iso e q) _).mpr ?_
      have hb := moduleCohomologyPullback_bijective f M q
      rw [← funext (moduleCohomologyPullbackLinearOfEq_apply f α β h M q)] at hb
      exact hb)

/-- The complete transport retains the same original additive pullback and
coefficient map pointwise, including the original scalar-action equality. -/
theorem moduleCohomologyPullbackCoefficientLinearEquiv_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {R : Type u} [CommRing R] (α : R →+* Γ(Y, ⊤)) (β : R →+* Γ(X, ⊤))
    (h : f.appTop.hom.comp α = β) (M : Y.Modules) {N : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N) (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) q) :
    moduleCohomologyPullbackCoefficientLinearEquiv f α β h M e q x =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) q
        (moduleCohomologyPullback f M q x) := by
  change moduleCohomologyMapOfHom X β e.hom q
    (moduleCohomologyPullbackLinearOfEq f α β h M q x) = _
  rw [moduleCohomologyPullbackLinearOfEq_apply]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
