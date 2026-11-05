/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstantFinitePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteAffineTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleCover
public import Aglib.CategoryTheory.Filtered.FiniteGeneration

/-! # Finite generation of actual locally constant module coefficients

Finite affine trivializing charts turn the original filtered cocone into
finitely many cocones with compact constant apex. One original stage is
therefore epimorphic. This is finite generation, not global finite presentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r v

variable (R : Type r) [Ring R]

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge
  Cardinal.fact_isRegular_aleph0

local instance finiteGenerationHasFiniteLimits : HasFiniteLimits (ModuleCat.{u + 1} R) where
  out _ _ _ := ModuleCat.hasLimitsOfShape.{0, 0, u + 1, r}

local instance finiteGenerationHasLimits :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, r}

local instance finiteGenerationInverseImageLeftAdjoint {X S : Scheme.{u}} (f : S ⟶ X) :
    (moduleInverseImage R f).IsLeftAdjoint := (moduleImageAdjunction R f).isLeftAdjoint

/-- Actual module inverse images on a jointly surjective étale family are jointly faithful. -/
theorem jointlyFaithful_moduleEtaleInverseImages {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Etale)
    (hU : ∀ x : X, ∃ (i : ι) (y : (U i).left), (U i).hom y = x) :
    JointlyFaithful (fun i => moduleInverseImage R (U i).hom) := by
  let h : JointlyReflectIsomorphisms (fun i => moduleInverseImage R (U i).hom) :=
    { isIso := by
        intro F G a ha
        have : IsIso ((moduleUnderlying R X).map a) := by
          apply isIso_of_etale_inverseImages U hU
          intro i
          apply (NatIso.isIso_map_iff (moduleInverseImageUnderlyingIso R (U i).hom) a).mp
          change IsIso ((moduleUnderlying R (U i).left).map
            ((moduleInverseImage R (U i).hom).map a))
          infer_instance
        exact isIso_of_reflects_iso a (moduleUnderlying R X) }
  exact h.jointlyFaithful

/-- A filtered colimit with finite-type locally constant apex over a left
Noetherian coefficient ring has an epimorphic original cocone leg. -/
theorem exists_epi_of_isColimit_of_isFiniteTypeLocallyConstant
    [IsNoetherianRing R] {X : Scheme.{u}} [CompactSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ ModuleSheaf R X} {c : Cocone D} (hc : IsColimit c)
    (hF : IsFiniteTypeLocallyConstant c.pt) : ∃ i, Epi (c.ι.app i) := by
  obtain ⟨t⟩ := hF
  obtain ⟨s, hfin, haff⟩ := t.exists_finite_affine
  let : Finite s.index := hfin
  let (i : s.index) : IsAffine (s.chart i).left := haff i
  let (i : s.index) : Module.Finite R (s.value i) := s.finite_value i
  have hcompact (i : s.index) : IsFinitelyPresentable.{u + 1}
      ((moduleInverseImage R (s.chart i).hom).obj c.pt) := by
    let : IsFinitelyPresentable.{u + 1}
        ((constantSheaf (s.chart i).left.smallEtaleTopology
          (ModuleCat.{u + 1} R)).obj (s.value i)) :=
      isFinitelyPresentable_constant_of_finite R (s.chart i).left (s.value i)
    exact isCardinalPresentable_of_iso (s.trivialization i).symm Cardinal.aleph0.{u + 1}
  exact @JointlyFaithful.exists_epi_of_isColimit _ _ _ _ _ _
    (fun i => moduleInverseImage R (s.chart i).hom)
    (jointlyFaithful_moduleEtaleInverseImages R s.chart s.covers)
    I _ _ D c hc (fun _ => inferInstance) hcompact

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
