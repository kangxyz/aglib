/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Reflexive.SecondSyzygy
public import Aglib.RingTheory.RegularLocalRing.FiniteProjectiveDimension

/-!
# Projective dimension of finite reflexive modules

The native bidual second-syzygy presentation and the finite-module bound over a
regular local ring give a two-step improvement of projective dimension.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace Module

/-- Over a regular local ring of dimension at most `d + 2`, a finite reflexive module
has projective dimension at most `d`. -/
theorem projectiveDimension_le_of_isReflexive (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ) (hd : ringKrullDim R ≤ (d + 2 : ℕ))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsReflexive R M] : projectiveDimension (ModuleCat.of R M) ≤ (d : ℕ) := by
  obtain ⟨F₀, F₁, _, _, _, _, _, _, _, _, f, g, hf, hfg⟩ :=
    exists_finite_free_second_syzygy R M
  have hex : Function.Exact f g.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, hfg]
  let S := ModuleCat.shortComplexOfCompEqZero f g.rangeRestrict
    hex.linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hex hf
    g.surjective_rangeRestrict
  have hext : Function.Exact g.range.subtype g.range.mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  let T := ModuleCat.shortComplexOfCompEqZero g.range.subtype g.range.mkQ
    hext.linearMap_comp_eq_zero
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T hext
    g.range.subtype_injective g.range.mkQ_surjective
  have : Module.Finite R T.X₃ := inferInstanceAs (Module.Finite R (F₁ ⧸ g.range))
  have hbound : projectiveDimension T.X₃ ≤ ringKrullDim R := by
    simpa only [IsRegularLocalRing.spanFinrank_maximalIdeal] using
      (IsRegularLocalRing.projectiveDimension_le_dimension
        (IsLocalRing.maximalIdeal R).spanFinrank R
        IsRegularLocalRing.spanFinrank_maximalIdeal.symm T.X₃)
  have : HasProjectiveDimensionLE T.X₃ (d + 2) :=
    (projectiveDimension_le_iff _ _).mp (hbound.trans hd)
  have : HasProjectiveDimensionLE T.X₁ (d + 1) :=
    hT.hasProjectiveDimensionLT_X₁ (d + 2)
      (hasProjectiveDimensionLT_of_ge T.X₂ 1 (d + 2) (by omega)) inferInstance
  exact (projectiveDimension_le_iff _ _).mpr
    (hS.hasProjectiveDimensionLT_X₁ (d + 1)
      (hasProjectiveDimensionLT_of_ge S.X₂ 1 (d + 1) (by omega)) inferInstance)

/-- Finite reflexive modules over regular local rings of dimension at most two
are free. The dimension bound includes dimensions zero and one. -/
theorem free_of_isReflexive_of_dimension_le_two (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R ≤ 2)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsReflexive R M] : Module.Free R M := by
  have : HasProjectiveDimensionLE (ModuleCat.of R M) 0 :=
    (projectiveDimension_le_iff _ _).mp
      (projectiveDimension_le_of_isReflexive R 0 (by simpa using hd) M)
  have : CategoryTheory.Projective (ModuleCat.of R M) :=
    (projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R M)).mpr inferInstance
  have : Module.Projective R M :=
    ModuleCat.projective_of_module_projective (ModuleCat.of R M)
  exact Module.free_of_flat_of_isLocalRing

end Module
