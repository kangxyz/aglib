/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.BaseChange.Projective
public import Aglib.Algebra.Category.ModuleCat.FinitePresentation
public import Aglib.Algebra.Category.ModuleCat.Localization.Projective
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Basic-open neighbourhoods with arbitrary native homology base change

Each point in the original outgoing cokernel's free locus has a basic
neighbourhood on which that cokernel is projective. If the original final
term is finite projective, the native homology mate after localization is
therefore invertible after every further ring map. The maps are the original
scalar-extension mates and original cokernels. Neither reducedness nor
Noetherianity is assumed. Identification of the free locus with the
original residue-field surjectivity locus is a separate normalization step.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module

namespace CategoryTheory.ShortComplex

universe u v w

variable {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{max u v w} R))
    [Module.Finite R S.X₂] [Module.FinitePresentation R S.X₃] [Module.Projective R S.X₃]

/-- A basic open in the native cokernel free locus gives arbitrary original homology
base change after localization to that open. The subsequent ring map need not be flat. -/
theorem homologyBaseChangeMap_isIso_of_basicOpen_subset_freeLocus
    (r : R) (h : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
      Module.freeLocus R (cokernel S.g : ModuleCat.{max u v w} R))
    {B : Type w} [CommRing B] (σ : Localization.Away r →+* B) :
    IsIso (ModuleCat.homologyBaseChangeMap.{u, max u v, w} σ
      (S.map (ModuleCat.extendScalars (algebraMap R (Localization.Away r)) :
        ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} (Localization.Away r)))) := by
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} (Localization.Away r) :=
    ModuleCat.extendScalars (algebraMap R (Localization.Away r))
  let : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v w, u, u}
      (algebraMap R (Localization.Away r))).isLeftAdjoint
  let : Module.FinitePresentation R (cokernel S.g : ModuleCat.{max u v w} R) :=
    ModuleCat.finitePresentation_cokernel S.g
  let : Module.Projective (Localization.Away r) (S.map F).X₃ := by
    change Module.Projective (Localization.Away r) (F.obj S.X₃)
    exact ModuleCat.projective_extendScalars (algebraMap R (Localization.Away r)) S.X₃
  let : Module.Projective (Localization.Away r) (F.obj (cokernel S.g)) :=
    ModuleCat.projective_extendScalars_away_of_basicOpen_subset_freeLocus.{u, max v w}
      (cokernel S.g) r h
  let : Module.Projective (Localization.Away r)
      (cokernel (S.map F).g : ModuleCat.{max u v w} (Localization.Away r)) := by
    change Module.Projective (Localization.Away r)
      (cokernel (F.map S.g) : ModuleCat.{max u v w} (Localization.Away r))
    exact Module.Projective.of_equiv' (PreservesCokernel.iso F S.g).toLinearEquiv
  exact ModuleCat.homologyBaseChangeMap_isIso_of_projective_cokernel.{u, max u v, w}
    σ (S.map F)

/-- Every point in the original outgoing cokernel's free locus has a basic
neighbourhood where the original localized homology mate is invertible after every
further ring map, with an independent target-ring universe. -/
theorem exists_basicOpen_homologyBaseChangeMap_isIso_of_mem_freeLocus (p : PrimeSpectrum R)
    (hp : p ∈ Module.freeLocus R (cokernel S.g : ModuleCat.{max u v w} R)) :
    ∃ r ∉ p.asIdeal,
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
          Module.freeLocus R (cokernel S.g : ModuleCat.{max u v w} R) ∧
      ∀ (B : Type w) [CommRing B] (σ : Localization.Away r →+* B),
        IsIso (ModuleCat.homologyBaseChangeMap.{u, max u v, w} σ
          (S.map (ModuleCat.extendScalars (algebraMap R (Localization.Away r)) :
            ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} (Localization.Away r)))) := by
  let : Module.FinitePresentation R (cokernel S.g : ModuleCat.{max u v w} R) :=
    ModuleCat.finitePresentation_cokernel S.g
  obtain ⟨_, ⟨r, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
      (Module.isOpen_freeLocus (R := R) (M := (cokernel S.g : ModuleCat.{max u v w} R))) p hp
  refine ⟨r, hpr, hr, fun B _ σ => ?_⟩
  exact S.homologyBaseChangeMap_isIso_of_basicOpen_subset_freeLocus r hr σ

end CategoryTheory.ShortComplex
