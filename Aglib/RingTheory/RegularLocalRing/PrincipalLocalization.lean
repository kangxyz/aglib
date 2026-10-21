/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.BaseChange
public import Aglib.Algebra.Category.ModuleCat.StablyFreeBaseChange
public import Aglib.LinearAlgebra.FreeModule.StableRankOne
public import Aglib.RingTheory.RegularLocalRing.FiniteProjectiveDimension
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Projective localized ideals over regular local rings are principal

A finite ideal of a regular local ring has bounded projective dimension.
If its localization in a domain is projective, the same localized ideal
has a finite free stable complement. Rank-one cancellation makes it
principal. The comparison uses the actual ideal extension and its native
localized-submodule map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory IsLocalRing
open scoped TensorProduct

namespace IsRegularLocalRing

/-- A projective extension of an ideal to a domain localization of a regular
local ring is principal. The projectivity concerns the actual mapped ideal. -/
theorem isPrincipal_map_of_projective_localization
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (W : Submonoid R) (S : Type u) [CommRing S] [IsDomain S]
    [Algebra R S] [IsLocalization W S]
    (I : Ideal R) [Module.Projective S (I.map (algebraMap R S))] :
    (I.map (algebraMap R S)).IsPrincipal := by
  classical
  by_cases hz : I.map (algebraMap R S) = ⊥
  · rw [hz]
    infer_instance
  let J : Ideal S := I.localized' S W (Algebra.linearMap R S)
  have hJ : J = I.map (algebraMap R S) := by
    change I.localized' S W (Algebra.linearMap R S) = I.map (algebraMap R S)
    rw [Ideal.map, Ideal.span, Submodule.localized'_eq_span, Algebra.coe_linearMap]
  have : Module.Projective S J := hJ.symm ▸ inferInstance
  let M := ModuleCat.of R I
  let e : ((ModuleCat.extendScalars (algebraMap R S)).obj M) ≃ₗ[S] J :=
    (ModuleCat.extendScalarsAlgebraIso R S M).toLinearEquiv ≪≫ₗ
      (IsLocalizedModule.isBaseChange W S
        (I.toLocalized' S W (Algebra.linearMap R S))).equiv
  have : Module.Projective S ((ModuleCat.extendScalars (algebraMap R S)).obj M) :=
    Module.Projective.of_equiv e.symm
  let d := (maximalIdeal R).spanFinrank
  have : HasProjectiveDimensionLE M d :=
    (projectiveDimension_le_iff M d).mp
      (projectiveDimension_le_dimension d R spanFinrank_maximalIdeal.symm M)
  have hf : (algebraMap R S).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S W)
  obtain ⟨P, hPfree, hPfinite, hfree⟩ :=
    ModuleCat.exists_free_prod_of_projective_extendScalars (algebraMap R S) hf M d
  have : Module.Finite S ((ModuleCat.extendScalars (algebraMap R S)).obj M) :=
    ModuleCat.finite_extendScalars (algebraMap R S) M
  have : Module.Free S (J × P) :=
    Module.Free.of_equiv (e.prodCongr (LinearEquiv.refl S P))
  have : Module.Finite S (J × P) :=
    Module.Finite.of_surjective
      (e.prodCongr (LinearEquiv.refl S P)).toLinearMap
      (e.prodCongr (LinearEquiv.refl S P)).surjective
  exact hJ ▸ J.isPrincipal_of_free_prod (by simpa only [hJ] using hz) P

end IsRegularLocalRing
