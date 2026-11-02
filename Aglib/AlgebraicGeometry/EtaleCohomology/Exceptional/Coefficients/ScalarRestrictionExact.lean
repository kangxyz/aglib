/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ClosedExactness

/-! # Exact native restriction of constant coefficient scalars

Restriction changes only the scalar action. Its underlying abelian sheaf is
unchanged, so exactness follows from the original conservative underlying
functor. No preservation of injectives or flatness assumption is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

variable (X : Scheme.{u}) {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ]
  (φ : Λ →+* Γ)

/-- The original underlying abelian sheaf is unchanged by scalar restriction. -/
def moduleRestrictScalarsUnderlyingIso :
    moduleRestrictScalars X φ ⋙ SheafOfModules.toSheaf (constantRing X Λ) ≅
      SheafOfModules.toSheaf (constantRing X Γ) := Iso.refl _

instance moduleRestrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (moduleRestrictScalars X φ) := by
  let : PreservesFiniteLimits (moduleRestrictScalars X φ ⋙
      SheafOfModules.toSheaf (constantRing X Λ)) :=
    preservesFiniteLimits_of_natIso (moduleRestrictScalarsUnderlyingIso X φ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleRestrictScalars X φ) (SheafOfModules.toSheaf (constantRing X Λ))

instance moduleRestrictScalars_additive : (moduleRestrictScalars X φ).Additive where
  map_add := by intros; rfl

instance moduleRestrictScalars_preservesEpimorphisms :
    (moduleRestrictScalars X φ).PreservesEpimorphisms := by
  let : (moduleRestrictScalars X φ ⋙
      SheafOfModules.toSheaf (constantRing X Λ)).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso (moduleRestrictScalarsUnderlyingIso X φ).symm
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    (moduleRestrictScalars X φ) (SheafOfModules.toSheaf (constantRing X Λ))

instance moduleRestrictScalars_preservesHomology :
    (moduleRestrictScalars X φ).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance moduleRestrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (moduleRestrictScalars X φ) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The actual ring restriction sends original short exact sequences to short exact sequences. -/
theorem shortExact_moduleRestrictScalars {T : ShortComplex (ModuleSheaf X Γ)}
    (hT : T.ShortExact) : (T.map (moduleRestrictScalars X φ)).ShortExact := by
  let := hT.mono_f
  let := hT.epi_g
  exact hT.map (moduleRestrictScalars X φ)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
