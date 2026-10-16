/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Base change of projective complex models

The native extension-of-scalars functor preserves finite projective terms. More
importantly, it preserves every comparison quasi-isomorphism between bounded-above
complexes of projective modules, even for a non-flat ring map. The latter statement
follows by mapping the actual homotopy equivalence supplied by K-projectivity.

This does not assert that tensor product commutes with the homology of an arbitrary
projective complex. It ensures that a computation after arbitrary base change is
independent of the chosen bounded projective complex model and comparison map.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex
open scoped TensorProduct

universe u v w

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- Any additive functor preserves a quasi-isomorphism between K-projective
complexes: the actual comparison map is a homotopy equivalence. -/
theorem quasiIso_mapHomologicalComplex_of_isKProjective (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} [K.IsKProjective] [L.IsKProjective]
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  exact homotopyEquivalences_le_quasiIso _ _ _
    (F.homotopyEquivalences_mapHomologicalComplex_map f
      ((CochainComplex.IsKProjective.quasiIso_iff f).mp inferInstance))

/-- In particular, an additive functor preserves a quasi-isomorphism between
bounded-above complexes of projective objects, without exactness of the functor. -/
theorem quasiIso_mapHomologicalComplex_of_projective (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b]
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let : K.IsKProjective := CochainComplex.isKProjective_of_projective K a
  let : L.IsKProjective := CochainComplex.isKProjective_of_projective L b
  exact F.quasiIso_mapHomologicalComplex_of_isKProjective f

end CategoryTheory.Functor

namespace CochainComplex

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]

/-- Finite terms in the actual base-changed complex require no flatness. -/
theorem finite_X_extendScalars (φ : R →+* S) (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) [Module.Finite R (K.X n)] :
    Module.Finite S
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K).X n) :=
  ModuleCat.finite_extendScalars φ (K.X n)

/-- Projective terms in the actual base-changed complex require no flatness. -/
theorem projective_X_extendScalars (φ : R →+* S)
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) [Module.Projective R (K.X n)] :
    Module.Projective S
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K).X n) :=
  ModuleCat.projective_extendScalars φ (K.X n)

/-- Arbitrary ring base change preserves the actual comparison quasi-isomorphism
between bounded-above projective module-complex models. -/
theorem quasiIso_extendScalars_of_projective (φ : R →+* S)
    {K L : CochainComplex (ModuleCat.{v} R) ℤ} (a b : ℤ)
    [K.IsStrictlyLE a] [L.IsStrictlyLE b]
    [∀ n, Module.Projective R (K.X n)] [∀ n, Module.Projective R (L.X n)]
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map f) := by
  have (n : ℤ) : Projective (K.X n) := inferInstance
  have (n : ℤ) : Projective (L.X n) := inferInstance
  exact (ModuleCat.extendScalars φ).quasiIso_mapHomologicalComplex_of_projective a b f

end CochainComplex
