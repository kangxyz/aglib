/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Projective
public import Aglib.AlgebraicGeometry.Cohomology.Projective.ClosedImmersion
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Finite global sections of reduced proper schemes

The actual Chow modification has a closed immersion into one polynomial
projective space. Its structure-module H0 is finite by the projective theorem.
Reducedness of the original source makes pullback of its actual global sections
injective. Noetherian submodule finiteness then applies to the original structural
ring map. No general proper-cohomology or higher base-change theorem is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme

/-- The literal structural coefficient map of a reduced proper scheme over a
Noetherian ring is finite. The source need not be integral or nonempty. -/
theorem finite_structuralCoefficients_of_isReduced
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).Finite := by
  obtain ⟨Y, p, m, j, V, hp, hsurj, hj, hbase, _, _⟩ :=
    Chow.exists_projective_modification R f
  let : IsProper p := hp
  let : Surjective p := hsurj
  let : IsClosedImmersion j := hj
  let : IsSchemeTheoreticallyDominant p :=
    IsSchemeTheoreticallyDominant.of_isDominant p
  let α : R →+* Γ(X, ⊤) :=
    f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let β : R →+* Γ(Y, ⊤) :=
    (p ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let := α.toAlgebra
  let := β.toAlgebra
  let := moduleCohomologyModuleOfHom Y β O 0
  let : Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf Y O) 0) :=
    moduleCohomology_finite_of_projectiveEmbedding R
      (ULift.{u} (Fin (m + 1))) j m Equiv.ulift (p ≫ f) hbase O
      (affineLocallyFiniteType_unit Y) 0
  let : Module.Finite R Γ(Y, ⊤) :=
    Module.Finite.equiv (moduleH0EquivOfHom Y β O)
  have hβ : β = p.appTop.hom.comp α := by
    dsimp only [β, α]
    rw [Scheme.Hom.comp_appTop]
    rfl
  let a : Γ(X, ⊤) →ₐ[R] Γ(Y, ⊤) :=
    { __ := p.appTop.hom
      commutes' := fun r => by
        change p.appTop.hom (α r) = β r
        rw [hβ]
        rfl }
  exact Module.Finite.of_injective a.toLinearMap (p.app_injective ⊤)

end AlgebraicGeometry.Scheme
