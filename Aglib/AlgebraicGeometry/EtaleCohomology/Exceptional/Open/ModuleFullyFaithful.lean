/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Triple

/-! # Fully faithful genuine constant-ring module extension by zero -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ]

/-- The literal chart restriction/direct-image counit is invertible for an open immersion. -/
instance moduleValuedRestrictionDirectImage_counit_isIso_of_open :
    IsIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
      (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
      (Scheme.smallEtaleTopology X)).counit) := by
  have h (F : ModuleValuedSheaf U Λ) :
      IsIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X)).counit.app F) := by
    have hV (V : U.Etaleᵒᵖ) :
        IsIso ((((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
          (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
          (Scheme.smallEtaleTopology X)).counit.app F).hom.app V) := by
      change IsIso (F.obj.map ((siteEtalePostcomposeAdj j).unit.app V.unop).op)
      infer_instance
    let : IsIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X)).counit.app F).hom :=
      NatIso.isIso_of_isIso_app _
    let : IsIso ((sheafToPresheaf (Scheme.smallEtaleTopology U) (ModuleCat.{u + 1} Λ)).map
        (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
          (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
          (Scheme.smallEtaleTopology X)).counit.app F)) := by
      change IsIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X)).counit.app F).hom
      infer_instance
    exact isIso_of_reflects_iso _ (sheafToPresheaf (Scheme.smallEtaleTopology U)
      (ModuleCat.{u + 1} Λ))
  exact NatIso.isIso_of_isIso_app _

/-- The original inverse-image/direct-image counit is invertible for an open immersion. -/
instance moduleValuedInverseImageAdjunction_counit_isIso_of_open :
    IsIso (moduleValuedInverseImageAdjunction j Λ).counit := by
  let : IsIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
      (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
      (Scheme.smallEtaleTopology X)).counit) :=
    moduleValuedRestrictionDirectImage_counit_isIso_of_open j Λ
  have h (F : ModuleValuedSheaf U Λ) :
      IsIso ((moduleValuedInverseImageAdjunction j Λ).counit.app F) := by
    rw [← Adjunction.leftAdjointUniq_hom_app_counit (moduleValuedInverseImageAdjunction j Λ)
      ((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X)) F]
    let e := (moduleValuedInverseImageAdjunction j Λ).leftAdjointUniq
      ((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X))
    let c := asIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
      (E := ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology U)
      (Scheme.smallEtaleTopology X)).counit)
    exact inferInstanceAs
      (IsIso (((e.app ((moduleValuedDirectImage j Λ).obj F)) ≪≫ c.app F).hom))
  exact NatIso.isIso_of_isIso_app _

/-- The actual module-valued extension/restriction/direct-image adjoint triple. -/
def moduleValuedLowerShriekTriple :
    Adjunction.Triple (moduleValuedLowerShriek j Λ) (moduleValuedInverseImage j Λ)
      (moduleValuedDirectImage j Λ) :=
  ⟨moduleValuedLowerShriekAdjunction j Λ, moduleValuedInverseImageAdjunction j Λ⟩

instance moduleValuedLowerShriek_unit_isIso_of_open :
    IsIso (moduleValuedLowerShriekAdjunction j Λ).unit :=
  (moduleValuedLowerShriekTriple j Λ).isIso_unit_iff_isIso_counit.mpr
    (moduleValuedInverseImageAdjunction_counit_isIso_of_open j Λ)

/-- Full faithfulness before the genuine constant-ring equivalence. -/
def moduleValuedLowerShriekFullyFaithful : (moduleValuedLowerShriek j Λ).FullyFaithful :=
  (moduleValuedLowerShriekAdjunction j Λ).fullyFaithfulLOfIsIsoUnit

instance moduleValuedLowerShriek_full_of_open : (moduleValuedLowerShriek j Λ).Full :=
  (moduleValuedLowerShriekFullyFaithful j Λ).full

instance moduleValuedLowerShriek_faithful_of_open : (moduleValuedLowerShriek j Λ).Faithful :=
  (moduleValuedLowerShriekFullyFaithful j Λ).faithful

instance moduleLowerShriek_full_of_open : (moduleLowerShriek j Λ).Full := by
  unfold moduleLowerShriek
  infer_instance

instance moduleLowerShriek_faithful_of_open : (moduleLowerShriek j Λ).Faithful := by
  unfold moduleLowerShriek
  infer_instance

/-- The genuine native lower-shriek unit is invertible. -/
instance moduleLowerShriek_unit_isIso_of_open : IsIso (moduleLowerShriekAdjunction j Λ).unit :=
  Adjunction.unit_isIso_of_L_fully_faithful _

/-- Restriction of genuine module extension by zero is the identity via its actual unit. -/
def moduleLowerShriekInverseImageIso :
    moduleLowerShriek j Λ ⋙ moduleInverseImage j Λ ≅ 𝟭 _ :=
  (asIso (moduleLowerShriekAdjunction j Λ).unit).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
