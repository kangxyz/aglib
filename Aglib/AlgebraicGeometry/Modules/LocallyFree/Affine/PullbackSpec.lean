/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback

/-!
# Finite local freeness of a quasi-coherent pullback to an affine scheme

For a map of commutative rings `φ : R ⟶ S` and a quasi-coherent `E` on `Spec R`, the pullback
`(Spec φ)^* E` is the sheaf associated with `S ⊗_R Γ(E)` (`pullbackSpecMapIsoTilde`, from
`tildePullbackIso`). Hence, for `S` Noetherian and `Γ(E)` finite over `R`, `(Spec φ)^* E` is
finite locally free if and only if `S ⊗_R Γ(E)` is a projective `S`-module
(`isFiniteLocallyFree_pullback_specMap_iff_projective`, from
`finiteLocallyFree_tilde_iff_projective`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The pullback of a quasi-coherent sheaf along `Spec φ` is the sheaf associated with the
extension of scalars of its global sections. -/
def pullbackSpecMapIsoTilde (E : (Spec R).Modules) [E.IsQuasicoherent] :
    (Scheme.Modules.pullback (Spec.map φ)).obj E ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj E)) :=
  (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso E.fromTildeΓ).symm ≪≫
    (tildePullbackIso φ).app (moduleSpecΓFunctor.obj E)

/-- **Finite local freeness of an affine pullback is projectivity of the base-changed sections**:
for `S` Noetherian and `E` quasi-coherent on `Spec R` with finite global sections,
`(Spec φ)^* E` is finite locally free if and only if `S ⊗_R Γ(E)` is a projective `S`-module. -/
theorem isFiniteLocallyFree_pullback_specMap_iff_projective [IsNoetherianRing S]
    (E : (Spec R).Modules) [E.IsQuasicoherent] [Module.Finite R (moduleSpecΓFunctor.obj E)] :
    IsFiniteLocallyFree (Spec S) ((Scheme.Modules.pullback (Spec.map φ)).obj E) ↔
      Module.Projective S ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj E)) := by
  have := ModuleCat.finite_extendScalars φ.hom (moduleSpecΓFunctor.obj E)
  rw [← finiteLocallyFree_tilde_iff_projective S]
  constructor
  · intro h
    exact finiteLocallyFree_of_iso (pullbackSpecMapIsoTilde φ E)
  · intro h
    exact finiteLocallyFree_of_iso (pullbackSpecMapIsoTilde φ E).symm

end AlgebraicGeometry.Scheme.Modules
