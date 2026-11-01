/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PrincipalNeighborhoodLimit

/-! # The actual principal-neighborhood limit after base change

The original localization spectrum and its native principal diagram are
pulled back along the supplied scheme map. Every stage is identified with
its literal inverse-image open, retaining the original projection to the
scheme. No replacement localization or covering model is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

universe u

variable {R : Type u} [CommRing R] (M : Submonoid R)
  (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

/-- The original principal stages over the supplied scheme. -/
def schemeDiagram : (Finset M)ᵒᵖ ⥤ Over X := baseDiagram M ⋙ Over.pullback p

/-- The pulled original localization cone over the supplied scheme. -/
def schemeCone : Cone (schemeDiagram M p) := (Over.pullback p).mapCone (baseCone M S)

/-- Base change preserves the original localization limit. -/
def schemeConeIsLimit : IsLimit (schemeCone M S p) :=
  isLimitOfPreserves (Over.pullback p) (baseConeIsLimit M S)

/-- The original stage scheme diagram. -/
abbrev baseChangeDiagram : (Finset M)ᵒᵖ ⥤ Scheme.{u} := schemeDiagram M p ⋙ Over.forget X

/-- The literal standard-order localization pullback is the cone vertex. -/
abbrev baseChangeCone : Cone (baseChangeDiagram M p) :=
  ((Over.forget X).mapCone (schemeCone M S p)).extend
    (pullbackSymmetry p (Spec.algebraMap R S)).hom

/-- The standard-order cone is limiting via native pullback symmetry. -/
def baseChangeConeIsLimit : IsLimit (baseChangeCone M S p) :=
  IsLimit.extendIso (s := (Over.forget X).mapCone (schemeCone M S p))
    (pullbackSymmetry p (Spec.algebraMap R S)).hom
    (isLimitOfPreserves (Over.forget X) (schemeConeIsLimit M S p))

/-- The actual original localization projection to a principal stage. -/
abbrev baseChangeProjection (s : (Finset M)ᵒᵖ) :
    pullback p (Spec.algebraMap R S) ⟶ (baseChangeDiagram M p).obj s :=
  (baseChangeCone M S p).π.app s

@[reassoc (attr := simp)] theorem baseChangeProjection_base (s : (Finset M)ᵒᵖ) :
    baseChangeProjection M S p s ≫ ((schemeDiagram M p).obj s).hom =
      pullback.fst p (Spec.algebraMap R S) := by
  change (pullbackSymmetry p (Spec.algebraMap R S)).hom ≫
    ((schemeCone M S p).π.app s).left ≫ _ = _
  rw [Over.w]
  exact pullbackSymmetry_hom_comp_snd _ _

@[reassoc] theorem baseChangeProjection_field (s : Finset M) :
    baseChangeProjection M S p (op s) ≫ pullback.fst (Spec.algebraMap R (stage M s)) p =
      pullback.snd p (Spec.algebraMap R S) ≫
        Spec.map (CommRingCat.ofHom (projection M S s)) := by
  change (pullbackSymmetry p (Spec.algebraMap R S)).hom ≫
    pullback.lift
      (pullback.fst (Spec.algebraMap R S) p ≫
        Spec.map (CommRingCat.ofHom (projection M S s)))
      (pullback.snd (Spec.algebraMap R S) p) _ ≫ _ = _
  simp only [pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]

/-- Each cone projection is the actual base change of the original
principal-localization map into the supplied localization. -/
theorem baseChangeProjection_isPullback (s : Finset M) :
    IsPullback (baseChangeProjection M S p (op s))
      (pullback.snd p (Spec.algebraMap R S))
      (pullback.fst (Spec.algebraMap R (stage M s)) p)
      (Spec.map (CommRingCat.ofHom (projection M S s))) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd (Spec.algebraMap R (stage M s)) p)
    (h₂₂ := Spec.algebraMap R (stage M s))
  · have h := baseStructure_fac M S (op s)
    change Spec.map (CommRingCat.ofHom (projection M S s)) ≫
      Spec.algebraMap R (stage M s) = Spec.algebraMap R S at h
    rw [h]
    change IsPullback (baseChangeProjection M S p (op s) ≫
      ((schemeDiagram M p).obj (op s)).hom) _ _ _
    rw [baseChangeProjection_base]
    exact IsPullback.of_hasPullback _ _
  · exact baseChangeProjection_field M S p s
  · exact (IsPullback.of_hasPullback _ _).flip

instance baseChange_transition_affine {s t : (Finset M)ᵒᵖ} (a : s ⟶ t) :
    IsAffineHom ((baseChangeDiagram M p).map a) := by
  exact MorphismProperty.overPullbackMap (P := @IsAffineHom) p
    ((baseDiagram M).map a) (inferInstanceAs (IsAffineHom ((specDiagram M).map a)))

instance baseChange_stage_affine (s : (Finset M)ᵒᵖ) :
    IsAffineHom ((schemeDiagram M p).obj s).hom := by
  change IsAffineHom (pullback.snd (Spec.algebraMap R (stage M s.unop)) p)
  exact MorphismProperty.pullback_snd _ _
    (inferInstanceAs (IsAffineHom (Spec.algebraMap R (stage M s.unop))))

instance baseChange_stage_compact [CompactSpace X] (s : (Finset M)ᵒᵖ) :
    CompactSpace ((baseChangeDiagram M p).obj s) :=
  QuasiCompact.compactSpace_of_compactSpace ((schemeDiagram M p).obj s).hom

instance baseChange_stage_quasiSeparated [QuasiSeparatedSpace X] (s : (Finset M)ᵒᵖ) :
    QuasiSeparatedSpace ((baseChangeDiagram M p).obj s) :=
  quasiSeparatedSpace_of_quasiSeparated ((schemeDiagram M p).obj s).hom

/-- The native principal stage's actual base open. -/
abbrev stageBaseOpen (s : Finset M) : (Spec (.of R)).Opens :=
  (Spec.algebraMap R (stage M s)).opensRange

/-- The literal inverse-image open in the original scheme. -/
abbrev stageSourceOpen (s : Finset M) : X.Opens := p ⁻¹ᵁ stageBaseOpen M s

/-- The original pullback stage is exactly its inverse-image open. -/
def stageOpenIso (s : Finset M) :
    (baseChangeDiagram M p).obj (op s) ≅ stageSourceOpen M p s :=
  IsOpenImmersion.isoOfRangeEq (pullback.snd (Spec.algebraMap R (stage M s)) p)
    (stageSourceOpen M p s).ι (by
      rw [Scheme.Opens.range_ι]
      exact IsOpenImmersion.range_pullbackSnd _ _)

@[reassoc (attr := simp)] theorem stageOpenIso_hom_over (s : Finset M) :
    (stageOpenIso M p s).hom ≫ (stageSourceOpen M p s).ι =
      ((schemeDiagram M p).obj (op s)).hom :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
