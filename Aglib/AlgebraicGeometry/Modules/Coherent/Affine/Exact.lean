/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
/-! # Exactness of the actual affine sheaf functors

The tilde functor preserves monomorphisms because its sections are locally
fractional families and localization preserves injectivity. Together with its
existing left adjoint structure, this proves exactness. Thus the abelian
structure on affine quasicoherent sheaves agrees with the ambient sheaf exact
structure, rather than merely being an abstractly transported structure.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u})

variable [IsNoetherianRing R]

instance affineCoherentToQuasicoherent_preservesFiniteLimits :
    PreservesFiniteLimits (affineFiniteType R).ι := by
  have := (affineFiniteType R).preservesKernels_ι
  exact Functor.preservesFiniteLimits_of_preservesKernels _

instance affineCoherentToQuasicoherent_preservesFiniteColimits :
    PreservesFiniteColimits (affineFiniteType R).ι := by
  have := (affineFiniteType R).preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

instance affineFiniteTypeToModules_preservesFiniteLimits :
    PreservesFiniteLimits (affineFiniteTypeToModules R) :=
  comp_preservesFiniteLimits (affineFiniteType R).ι
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι

instance affineFiniteTypeToModules_preservesFiniteColimits :
    PreservesFiniteColimits (affineFiniteTypeToModules R) :=
  comp_preservesFiniteColimits (affineFiniteType R).ι
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι

instance affineFiniteTypeToModules_additive : (affineFiniteTypeToModules R).Additive :=
  inferInstanceAs (Functor.Additive (_ ⋙ _))

/-- The actual inclusion of affine coherent sheaves preserves sheaf short
exact sequences and therefore is an exact functor. -/
def affineCoherentInclusion :
    ExactFunctor (affineCoherentExactStructure R) (abelianExactStructure (Spec R).Modules) where
  toFunctor := affineFiniteTypeToModules R
  map_conflation _ h := h.map_of_exact _

/-- Exactness in the coherent category is exactly ambient sheaf exactness. -/
theorem affineCoherent_shortExact_iff (S : ShortComplex (AffineFiniteType R)) :
    S.ShortExact ↔ (S.map (affineFiniteTypeToModules R)).ShortExact := by
  constructor
  · exact fun h => h.map_of_exact _
  · intro h
    have := h.mono_f
    have := h.epi_g
    exact { exact := Functor.reflects_exact_of_faithful (affineFiniteTypeToModules R) S h.exact
            mono_f := Functor.mono_of_mono_map (affineFiniteTypeToModules R) h.mono_f
            epi_g := Functor.epi_of_epi_map (affineFiniteTypeToModules R) h.epi_g }

/- The following generic comparison declarations are extracted from
Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/GTheory.lean:33–43, revision
83629578a3d70787d41ec631f5234af8758716af. -/
instance affineGlobalSections_additive : (affineFiniteTypeModuleEquivalence R).functor.Additive :=
  by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (affineFiniteTypeModuleEquivalence
    R).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The actual global-sections equivalence as an exact functor. -/
def affineGlobalSectionsExact :
    ExactFunctor (affineCoherentExactStructure R) (finiteModuleExactStructure.{u, u} R) where
  toFunctor := (affineFiniteTypeModuleEquivalence R).functor
  map_conflation _ h := h.map_of_exact _


end AlgebraicGeometry.Scheme.Modules.Coherent
