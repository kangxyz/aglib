/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.FlatPreimmersionBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseOpenBaseChange

/-! # Original pointwise etaleness through the native normalization comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- Etaleness at the specified original base-changed normalization point
returns to its unchanged original image under the native comparison. -/
theorem etaleAt_of_flatPreimmersionBaseChange
    {X U T V : Scheme.{u}} [IsIntegral X] [IsIntegral U] [IsIntegral T] [IsIntegral V]
    [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (j : U ⟶ X) [IsOpenImmersion j] (b : T ⟶ X) [Flat b] [IsPreimmersion b]
    (hg : genericPoint X ∈ Set.range b)
    (jR : V ⟶ T) [IsOpenImmersion jR] (g : V ⟶ U) (H : IsPullback g jR j b)
    (Y : FiniteEtale U) [IsIntegral Y.obj.left]
    (z : (genericMap jR (pullback.snd Y.obj.hom g)).normalization)
    (y : (genericMap j Y.obj.hom).normalization)
    (hy : ((flatPreimmersionBaseChangeIso j b hg jR g H Y).hom ≫
      pullback.fst (genericMap j Y.obj.hom).fromNormalization b) z = y)
    (het : (genericMap jR (pullback.snd Y.obj.hom g)).fromNormalization.etaleAt z) :
    (genericMap j Y.obj.hom).fromNormalization.etaleAt y := by
  let f := (genericMap j Y.obj.hom).fromNormalization
  let : IsFinite f := fromNormalization_isFinite j Y.obj.hom
  let e := flatPreimmersionBaseChangeIso j b hg jR g H Y
  have he : e.hom ≫ pullback.snd f b =
      (genericMap jR (pullback.snd Y.obj.hom g)).fromNormalization :=
    flatPreimmersionBaseChangeIso_hom_over j b hg jR g H Y
  have hcomp : (e.hom ≫ pullback.snd f b).etaleAt z := he.symm ▸ het
  have hp := Hom.etaleAt.of_comp_openImmersion e.hom (pullback.snd f b) z hcomp
  exact Hom.etaleAt_of_isPullback_of_flat_of_preimmersion
    (IsPullback.of_hasPullback f b) (e.hom z) y hy hp

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
