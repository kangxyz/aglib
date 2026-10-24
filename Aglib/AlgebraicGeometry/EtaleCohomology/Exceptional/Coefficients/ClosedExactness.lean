/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Exactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.FiniteDirectImageExactness
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Exact direct image for finite constant-ring module sheaves

Additive forgetting preserves epimorphisms because epimorphisms of module-valued
sheaves are locally surjective. The actual underlying direct-image comparison
then transfers finite abelian direct-image exactness to native ringed modules.
In particular this applies to closed immersions. No preservation of injective
objects by coefficient forgetting is asserted or used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- Additive forgetting of module-valued sheaves preserves local surjections and epimorphisms. -/
instance moduleValuedForget_preservesEpimorphisms :
    (sheafCompose (Scheme.smallEtaleTopology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).PreservesEpimorphisms where
  preserves {M N} α hα := by
    let J := Scheme.smallEtaleTopology X
    have h : Sheaf.IsLocallySurjective α :=
      (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u + 1} Λ) α).mpr hα
    apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} _).mp
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight α.hom (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    apply (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
    exact (Presheaf.isLocallySurjective_iff_whisker_forget J α.hom).mp h

/-- The original additive sheaf of a native module sheaf preserves epimorphisms. -/
instance moduleUnderlying_preservesEpimorphisms :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).PreservesEpimorphisms :=
  Functor.PreservesEpimorphisms.of_iso (moduleSheafInverseUnderlyingIso X Λ)

/-- The original additive underlying sheaf functor is exact. -/
instance moduleUnderlying_preservesHomology :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

variable {X} {S : Scheme.{u}} (f : S ⟶ X) [IsFinite f]

/-- Finite direct image preserves epimorphisms in the genuine constant-ring module category. -/
instance finiteModuleDirectImage_preservesEpimorphisms :
    (moduleDirectImage f Λ).PreservesEpimorphisms := by
  let : (moduleDirectImage f Λ ⋙
      SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso (moduleDirectImageUnderlyingIso f Λ).symm
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    (moduleDirectImage f Λ) (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ))

/-- Finite direct image, hence closed direct image, preserves the original module homology. -/
instance finiteModuleDirectImage_preservesHomology :
    (moduleDirectImage f Λ).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Exactness is on the native module sheaves and their original direct-image maps. -/
theorem shortExact_finiteModuleDirectImage {T : ShortComplex (ModuleSheaf S Λ)}
    (hT : T.ShortExact) : (T.map (moduleDirectImage f Λ)).ShortExact := by
  let := hT.mono_f
  let := hT.epi_g
  exact hT.map (moduleDirectImage f Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
