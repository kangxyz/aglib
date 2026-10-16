/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.BaseChange.Local
public import Aglib.Algebra.Category.ModuleCat.FinitePresentation
public import Aglib.Algebra.Category.ModuleCat.Localization.Projective
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Flat
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology.Composition
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Basic-open neighbourhoods with arbitrary native homology base change

Each point in the original outgoing cokernel's free locus has a basic
neighbourhood on which that cokernel is projective. If the original final
term is finite projective, the native homology mate after localization is
therefore invertible after every further ring map. The maps are the original
scalar-extension mates and original cokernels. Neither reducedness nor
Noetherianity is assumed. The native composition identity identifies this
free locus with surjectivity of the original map to the actual residue
field at the prime, through the localization at that same prime.
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

/-- The original map to the actual residue field at a prime is surjective exactly
on the original outgoing cokernel's native free locus. Localization and its actual
residue map are compared by the unchanged native homology-mate composition identity. -/
theorem epi_residue_homologyBaseChangeMap_iff_mem_freeLocus
    (S : ShortComplex (ModuleCat.{max u v} R))
    [Module.Finite R S.X₂] [Module.FinitePresentation R S.X₃] [Module.Projective R S.X₃]
    (p : PrimeSpectrum R) :
    Epi (ModuleCat.homologyBaseChangeMap.{u, v, u}
      (algebraMap R p.asIdeal.ResidueField) S) ↔
      p ∈ Module.freeLocus R (cokernel S.g : ModuleCat.{max u v} R) := by
  rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField]
  let Rₚ := Localization.AtPrime p.asIdeal
  let κ := p.asIdeal.ResidueField
  let σ : R →+* Rₚ := algebraMap R Rₚ
  let τ : Rₚ →+* κ := algebraMap Rₚ κ
  let F : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} Rₚ :=
    ModuleCat.extendScalars σ
  let G : ModuleCat.{max u v} Rₚ ⥤ ModuleCat.{max u v} κ :=
    ModuleCat.extendScalars τ
  let T := S.map F
  let : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u} σ).isLeftAdjoint
  let : G.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u} τ).isLeftAdjoint
  let : PreservesFiniteLimits F :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Rₚ p.asIdeal.primeCompl))
  let : IsIso (ModuleCat.homologyBaseChangeMap.{u, v, u} σ S) := by
    rw [ModuleCat.homologyBaseChangeMap_eq_mapHomologyIso_inv.{u, v, u}]
    infer_instance
  let χ := S.mapNatTrans (ModuleCat.extendScalarsComp.{u, v} σ τ).hom
  let : IsIso χ := inferInstanceAs
    (IsIso (S.mapNatIso (ModuleCat.extendScalarsComp.{u, v} σ τ)).hom)
  let a := ModuleCat.homologyBaseChangeMap.{u, v, u} (τ.comp σ) S
  let b := ModuleCat.homologyBaseChangeMap.{u, v, u} τ T
  let α := (ModuleCat.extendScalarsComp.{u, v} σ τ).hom.app S.homology ≫
    G.map (ModuleCat.homologyBaseChangeMap.{u, v, u} σ S)
  let δ := homologyMap χ
  let : IsIso α := by dsimp [α]; infer_instance
  let : IsIso δ := inferInstance
  have hc : α ≫ b = a ≫ δ := by
    simpa only [α, b, a, δ, χ, T, F, G, Category.assoc] using
      ModuleCat.homologyBaseChangeMap_comp.{u, v} σ τ S
  have he : Epi a ↔ Epi b := by
    calc
      Epi a ↔ Epi (a ≫ δ) := (epi_comp_iff_of_isIso a δ).symm
      _ ↔ Epi (α ≫ b) := by rw [hc]
      _ ↔ Epi b := epi_comp_iff_of_epi α b
  let : Module.Finite Rₚ T.X₂ := ModuleCat.finite_extendScalars σ S.X₂
  let : Module.Finite Rₚ T.X₃ := ModuleCat.finite_extendScalars σ S.X₃
  let : Module.Projective Rₚ T.X₃ := ModuleCat.projective_extendScalars σ S.X₃
  change Epi a ↔ _
  rw [he, epi_residue_homologyBaseChangeMap_iff_free_cokernel.{u, v} T,
    ModuleCat.mem_freeLocus_iff_free_extendScalars_atPrime.{u, v}]
  exact (Module.Free.iff_of_equiv (PreservesCokernel.iso F S.g).toLinearEquiv).symm

variable (S : ShortComplex (ModuleCat.{max u v w} R))
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

/-- Surjectivity of the original map to the actual residue field at a prime gives
a basic-open neighbourhood with arbitrary original homology base change after
localization. The further ring map is arbitrary, with an independent target universe. -/
theorem exists_basicOpen_homologyBaseChangeMap_isIso_of_epi_residue (p : PrimeSpectrum R)
    (hp : Epi (ModuleCat.homologyBaseChangeMap.{u, max v w, u}
      (algebraMap R p.asIdeal.ResidueField) S)) :
    ∃ r ∉ p.asIdeal,
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
          Module.freeLocus R (cokernel S.g : ModuleCat.{max u v w} R) ∧
      ∀ (B : Type w) [CommRing B] (σ : Localization.Away r →+* B),
        IsIso (ModuleCat.homologyBaseChangeMap.{u, max u v, w} σ
          (S.map (ModuleCat.extendScalars (algebraMap R (Localization.Away r)) :
            ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} (Localization.Away r)))) :=
  exists_basicOpen_homologyBaseChangeMap_isIso_of_mem_freeLocus.{u, v, w} S p
    ((epi_residue_homologyBaseChangeMap_iff_mem_freeLocus.{u, max v w} S p).mp hp)

/-- On a basic open in the original outgoing cokernel's free locus, the original
mate for the composite ring map is invertible. The native composition identity
compares it with localization and the further mate on that same short complex. -/
theorem homologyBaseChangeMap_comp_isIso_of_basicOpen_subset_freeLocus
    (S : ShortComplex (ModuleCat.{max u v} R))
    [Module.Finite R S.X₂] [Module.FinitePresentation R S.X₃] [Module.Projective R S.X₃]
    (r : R) (h : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
      Module.freeLocus R (cokernel S.g : ModuleCat.{max u v} R))
    {B : Type u} [CommRing B] (τ : Localization.Away r →+* B) :
    IsIso (ModuleCat.homologyBaseChangeMap.{u, v, u}
      (τ.comp (algebraMap R (Localization.Away r))) S) := by
  let σ : R →+* Localization.Away r := algebraMap R (Localization.Away r)
  let F : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} (Localization.Away r) :=
    ModuleCat.extendScalars σ
  let : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u} σ).isLeftAdjoint
  let : PreservesFiniteLimits F :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away r) (Submonoid.powers r)))
  let : IsIso (ModuleCat.homologyBaseChangeMap.{u, v, u} σ S) := by
    rw [ModuleCat.homologyBaseChangeMap_eq_mapHomologyIso_inv.{u, v, u}]
    infer_instance
  let : IsIso (ModuleCat.homologyBaseChangeMap.{u, v, u} τ (S.map F)) :=
    homologyBaseChangeMap_isIso_of_basicOpen_subset_freeLocus.{u, v, u} S r h τ
  let χ := S.mapNatTrans (ModuleCat.extendScalarsComp.{u, v} σ τ).hom
  let : IsIso χ := inferInstanceAs
    (IsIso (S.mapNatIso (ModuleCat.extendScalarsComp.{u, v} σ τ)).hom)
  have hc := ModuleCat.homologyBaseChangeMap_comp.{u, v} σ τ S
  let : IsIso (ModuleCat.homologyBaseChangeMap.{u, v, u} (τ.comp σ) S ≫ homologyMap χ) := by
    rw [← hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (homologyMap χ)

end CategoryTheory.ShortComplex
