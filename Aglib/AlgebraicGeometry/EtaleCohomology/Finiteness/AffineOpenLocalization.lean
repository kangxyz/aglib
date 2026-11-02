/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Etale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.AffineLocality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Descent.SurjectiveAffine

/-! # Original higher-image constructibility from affine-open base changes

The original all-degree etale exchange identifies each actual affine-open
restriction. The existing constructibility-locality producer supplies the
partitions. A second form uses the original spectrum chart of each affine
open, retaining the original coefficient pullback and avoiding replacement
source schemes. No proper base change or smooth positive-degree theorem is
needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- The literal affine-open pullback images supply constructibility of the
original higher image through the canonical etale mate. -/
theorem higherDirectImage_isConstructible_of_affineOpenBaseChanges
    {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ) (F : AbelianSheaf.{u, u + 1} X)
    (hlocal : ∀ U : S.affineOpens, Constructible.IsConstructible
      ((higherDirectImage (pullback.fst U.1.ι f) q).obj
        ((inverseImage (pullback.snd U.1.ι f)).obj F))) :
    Constructible.IsConstructible ((higherDirectImage f q).obj F) := by
  apply Constructible.isConstructible_of_affineOpenPullbacks
  intro U
  have : IsIso (higherBaseChangeMap f (pullback.fst U.1.ι f) U.1.ι
      (pullback.snd U.1.ι f) pullback.condition q) :=
    higherBaseChangeMap_etale_isIso f U.1.ι q
  exact (Constructible.isConstructible_iff_of_iso
    (asIso ((higherBaseChangeMap f (pullback.fst U.1.ι f) U.1.ι
      (pullback.snd U.1.ι f) pullback.condition q).app F))).mpr (hlocal U)

/-- The same locality criterion using the original spectrum chart of each
actual affine open. The affine isomorphism is descended, not assumed to
preserve a replacement partition. -/
theorem higherDirectImage_isConstructible_of_affineSpecBaseChanges
    {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ) (F : AbelianSheaf.{u, u + 1} X)
    (hlocal : ∀ U : S.affineOpens, Constructible.IsConstructible
      ((higherDirectImage (pullback.fst U.property.fromSpec f) q).obj
        ((inverseImage (pullback.snd U.property.fromSpec f)).obj F))) :
    Constructible.IsConstructible ((higherDirectImage f q).obj F) := by
  apply Constructible.isConstructible_of_affineOpenPullbacks
  intro U
  have : IsAffine U.1.toScheme := U.property
  have : IsOpenImmersion U.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.property
  have : Etale U.property.fromSpec := inferInstance
  have : IsIso (higherBaseChangeMap f (pullback.fst U.property.fromSpec f)
      U.property.fromSpec (pullback.snd U.property.fromSpec f) pullback.condition q) :=
    higherBaseChangeMap_etale_isIso f U.property.fromSpec q
  have hspec := (Constructible.isConstructible_iff_of_iso
    (asIso ((higherBaseChangeMap f (pullback.fst U.property.fromSpec f)
      U.property.fromSpec (pullback.snd U.property.fromSpec f)
      pullback.condition q).app F))).mpr (hlocal U)
  apply Constructible.isConstructible_of_surjective_pullback_of_isAffine
    U.property.isoSpec.inv
  exact (Constructible.isConstructible_iff_of_iso
    ((inverseImageComp U.1.ι U.property.isoSpec.inv).app
      ((higherDirectImage f q).obj F))).mp hspec

end AlgebraicGeometry.Scheme.EtaleCohomology
