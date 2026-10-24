/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.AbelianAdjunction
public import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# Fully faithful extension by zero for open immersions

Postcomposition of étale charts is fully faithful for an open immersion.
The resulting site adjunction identifies restriction of direct image with
the identity, retaining its actual counit. The lower-shriek adjoint triple
then proves invertibility of the actual extension-by-zero unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Postcomposition with an open immersion retains all maps between its étale charts. -/
instance siteEtalePostcompose_full_of_open : (siteEtalePostcompose j).Full where
  map_surjective {A B} f := by
    refine ⟨MorphismProperty.Over.homMk f.left ?_, ?_⟩
    · apply (cancel_mono j).mp
      have h := MorphismProperty.Over.w f
      change f.left ≫ (B.hom ≫ j) = A.hom ≫ j at h
      exact (Category.assoc _ _ _).trans h
    · apply MorphismProperty.Over.Hom.ext
      rfl

instance siteEtalePostcompose_faithful_of_open : (siteEtalePostcompose j).Faithful where
  map_injective h := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f => f.left) h

/-- The literal chart restriction/direct-image counit is invertible for an open immersion. -/
instance etaleRestrictionDirectImage_counit_isIso_of_open :
    IsIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
      (Scheme.smallEtaleTopology X)).counit) := by
  have h (F : AbelianSheaf.{u, u + 1} U) :
      IsIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X)).counit.app F) := by
    have hV (V : U.Etaleᵒᵖ) :
        IsIso ((((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
          (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
          (Scheme.smallEtaleTopology X)).counit.app F).hom.app V) := by
      change IsIso (F.obj.map ((siteEtalePostcomposeAdj j).unit.app V.unop).op)
      infer_instance
    let : IsIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X)).counit.app F).hom :=
      NatIso.isIso_of_isIso_app _
    let : IsIso ((sheafToPresheaf (Scheme.smallEtaleTopology U) AddCommGrpCat.{u + 1}).map
        (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
          (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
          (Scheme.smallEtaleTopology X)).counit.app F)) := by
      change IsIso (((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X)).counit.app F).hom
      infer_instance
    exact isIso_of_reflects_iso _ (sheafToPresheaf (Scheme.smallEtaleTopology U)
      AddCommGrpCat.{u + 1})
  exact NatIso.isIso_of_isIso_app _

/-- The original inverse-image/direct-image counit is invertible for an open immersion. -/
instance inverseImageAdjunction_counit_isIso_of_open :
    IsIso (inverseImageAdjunction j).counit := by
  have h (F : AbelianSheaf.{u, u + 1} U) :
      IsIso ((inverseImageAdjunction j).counit.app F) := by
    rw [← Adjunction.leftAdjointUniq_hom_app_counit (inverseImageAdjunction j)
      ((siteEtalePostcomposeAdj j).sheafPushforwardContinuous
        (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U)
        (Scheme.smallEtaleTopology X)) F]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The genuine extension/restriction/direct-image adjoint triple. -/
def etaleLowerShriekTriple :
    Adjunction.Triple (etaleLowerShriek j) (inverseImage j) (directImage j) :=
  ⟨etaleLowerShriekAdjunction j, inverseImageAdjunction j⟩

/-- Restricting extension by zero gives the identity through its actual adjunction unit. -/
instance etaleLowerShriek_unit_isIso_of_open : IsIso (etaleLowerShriekAdjunction j).unit :=
  (etaleLowerShriekTriple j).isIso_unit_iff_isIso_counit.mpr
    (inverseImageAdjunction_counit_isIso_of_open j)

/-- The original lower-shriek functor for an open immersion is fully faithful. -/
def etaleLowerShriekFullyFaithful : (etaleLowerShriek j).FullyFaithful :=
  (etaleLowerShriekAdjunction j).fullyFaithfulLOfIsIsoUnit

instance etaleLowerShriek_full_of_open : (etaleLowerShriek j).Full :=
  (etaleLowerShriekFullyFaithful j).full

instance etaleLowerShriek_faithful_of_open : (etaleLowerShriek j).Faithful :=
  (etaleLowerShriekFullyFaithful j).faithful

/-- The restriction isomorphism is the inverse of the original lower-shriek unit. -/
def etaleLowerShriekInverseImageIso : etaleLowerShriek j ⋙ inverseImage j ≅ 𝟭 _ :=
  (asIso (etaleLowerShriekAdjunction j).unit).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
