/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageNoetherian

/-! # Finite module images over locally Noetherian schemes

Constructibility is affine-local on the target. Original finite base change
therefore removes the quasi-compactness assumption from the Noetherian result.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Finite direct image preserves genuine constructible modules over a locally
Noetherian target, with arbitrary independent-universe commutative coefficients. -/
theorem isConstructible_finiteDirectImage_of_locallyNoetherian
    (R : Type r) [CommRing R] {Y X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] {F : ModuleSheaf R Y} (hF : IsConstructible F) :
    IsConstructible ((moduleDirectImage R f).obj F) := by
  intro U
  let : IsAffine U.1.toScheme := U.2
  let : IsLocallyNoetherian U.1.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.1.ι
  let : IsNoetherian U.1.toScheme := ⟨⟩
  let p := pullback.fst f U.1.ι
  let q := pullback.snd f U.1.ι
  have h := isConstructible_finiteDirectImage_of_noetherian R q
    (isConstructible_pullback p hF)
  exact nonempty_constructiblePartition ((isConstructible_iff_of_iso
    ((finiteImageBaseChangeIso R f q U.1.ι p
      (IsPullback.of_hasPullback f U.1.ι)).app F)).mpr h)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
