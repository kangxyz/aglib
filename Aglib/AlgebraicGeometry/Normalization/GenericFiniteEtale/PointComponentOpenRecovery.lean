/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.PointComponent
public import Aglib.AlgebraicGeometry.Properties.Normal.OpenRestriction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericGalois

/-! # The actual open-cover square on the selected normalization component

Restrict the original open-recovery square to the actual normal component.
Its unchanged clopen covering-source preimage is precisely the cover already
selected at the original point. No replacement connected cover is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U E : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U] (p : E ⟶ U) [IsFinite p] [Etale p]

local instance : IsLocallyNoetherian (genericMap j p).normalization := by
  let : IsFinite (genericMap j p).fromNormalization := fromNormalization_isFinite j p
  exact LocallyOfFiniteType.isLocallyNoetherian (genericMap j p).fromNormalization

local notation "C" => normalComponentOpen (Hom.normalization (genericMap j p))
  (genericMap_normalStalks j p)

/-- The original covering-source inclusion restricted to the actual component. -/
def pointComponentInclusion (x : (genericMap j p).normalization) :
    (pointComponentOpen j p x).toScheme ⟶ (C x).toScheme := inclusion j p ∣_ C x

instance pointComponentInclusion_isOpenImmersion (x : (genericMap j p).normalization) :
    IsOpenImmersion (pointComponentInclusion j p x) := by
  exact MorphismProperty.of_isPullback
    (isPullback_morphismRestrict (inclusion j p) (C x)).flip inferInstance

/-- The selected component retains its actual normal stalks. -/
theorem pointComponent_normalStalks (x : (genericMap j p).normalization) :
    NormalStalks (C x) :=
  (genericMap_normalStalks j p).of_isOpenImmersion (C x).ι

/-- The restricted covering source is the original base-open pullback of the
actual component, with the same structural and inclusion maps. -/
theorem pointComponent_isPullback (x : (genericMap j p).normalization) :
    IsPullback (pointComponentInclusion j p x) ((pointComponentCover j p x).obj.hom)
      ((C x).ι ≫ (genericMap j p).fromNormalization) j :=
  (isPullback_morphismRestrict (inclusion j p) (C x)).paste_vert (isPullback j p)

/-- The actual component remains finite over the unchanged base. -/
theorem pointComponent_isFinite (x : (genericMap j p).normalization) :
    IsFinite ((C x).ι ≫ (genericMap j p).fromNormalization) := by
  let : IsFinite (genericMap j p).fromNormalization := fromNormalization_isFinite j p
  infer_instance

/-- The same actual component dominates the original base, via its unchanged
nonempty integral finite-etale open subcover. -/
theorem pointComponent_isDominant (x : (genericMap j p).normalization) :
    IsDominant ((C x).ι ≫ (genericMap j p).fromNormalization) := by
  let Y := pointComponentCover j p x
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsIntegral Y.obj.left := inferInstanceAs (IsIntegral (pointComponentOpen j p x))
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let : IsDominant (pointComponentInclusion j p x ≫
      ((C x).ι ≫ (genericMap j p).fromNormalization)) := by
    rw [(pointComponent_isPullback j p x).w]
    exact inferInstanceAs (IsDominant (Y.obj.hom ≫ j))
  exact IsDominant.of_comp (pointComponentInclusion j p x) _

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
