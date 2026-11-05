/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.StalkFiniteness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstructibleStages
public import Aglib.Algebra.Category.ModuleCat.FinitePresentable
public import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Native constructible stages capturing module geometric stalks

A subsheaf of a constructible module coefficient has finitely generated
geometric stalks over a left Noetherian ring. Finite presentation over that
same ring factors the identity through an original filtered stage, producing
an actual constructible coefficient with an epimorphic geometric-stalk map.
No finiteness of the additive carrier or replacement of the ring is involved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

variable (R : Type (u + 1)) [Ring R] [IsNoetherianRing R]

local instance genericImageHasFiniteLimits : HasFiniteLimits (ModuleCat.{u + 1} R) where
  out _ _ _ := ModuleCat.hasLimitsOfShape.{0, 0, u + 1, u + 1}

local instance genericImageHasLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

/-- One original constructible finite-colimit stage maps epimorphically onto
any chosen geometric stalk of an arbitrary subsheaf of a constructible target. -/
theorem exists_constructible_geometricStalk_epi_of_mono
    {X : Scheme.{u}} [IsAffine X]
    {F G : ModuleSheaf R X} (f : F ⟶ G) [Mono f]
    (hG : IsConstructible G) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ X) :
    ∃ (P : ModuleSheaf R X) (q : P ⟶ F),
      IsConstructible P ∧
        Epi (((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).map q) := by
  obtain ⟨I, hI, hfilt, D, c, hcF, hc, hstage⟩ :=
    NativeFreePresentation.exists_filtered_presentation R X F
  let := hI
  let := hfilt
  subst F
  let T := (pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)
  let : LocallySmall.{u} X.Etale := inferInstance
  let : HasFilteredColimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} (ModuleCat.{u + 1} R) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : PreservesFiniteLimits T := inferInstanceAs
    (PreservesFiniteLimits ((pointSmallEtale η).sheafFiber
      (A := ModuleCat.{u + 1} R)))
  let : T.PreservesMonomorphisms := inferInstance
  let : Module.Finite R (T.obj G) := moduleGeometricStalk_finite_of_isConstructible R η hG
  let : Module.Finite R (T.obj c.pt) := Module.Finite.of_injective (T.map f).hom
    ((ModuleCat.mono_iff_injective (T.map f)).mp inferInstance)
  let : PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    ModuleCat.Sheaf.forget_preservesFilteredColimits R
  let : Module.FinitePresentation R (T.obj c.pt) :=
    Module.finitePresentation_of_finite R (T.obj c.pt)
  let : IsFinitelyPresentable.{u + 1} (T.obj c.pt) :=
    ModuleCat.isFinitelyPresentable_of_finitePresentation _
  obtain ⟨i, a, ha⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (X := T.obj c.pt) (isColimitOfPreserves T hc.some) (𝟙 (T.obj c.pt))
  refine ⟨D.obj i, c.ι.app i,
    NativeFreePresentation.finiteColimitStage_isConstructible R _ (hstage i), ?_⟩
  exact epi_of_epi_fac ha

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
