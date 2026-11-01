/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ConstructibleAffineNoetherian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.AffineLocality

/-! # Original finite direct-image constructibility on Noetherian schemes

Each original affine-open restriction is compared by the canonical finite
base-change mate with the actual finite morphism over that affine open.
The original qcqs inverse-image producer and the affine Noetherian theorem
supply constructibility, transported through the original mate. The complete
affine-locality producer then supplies the original partitions. This is the
Noetherian theorem, not the
arbitrary-base finite finitely presented theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

/-- Construct and transport original constructibility across a variable
actual Cartesian square. No partition or constructibility of the direct
image is supplied as an additional input. -/
theorem isConstructible_directImagePullback_of_isAffine_of_isNoetherian
    {Y X Y' U : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsAffine U] [IsNoetherian U]
    (f : Y ⟶ X) (f' : Y' ⟶ U) (g : U ⟶ X) (k : Y' ⟶ Y)
    [IsFinite f] (H : IsPullback k f' f g)
    {F : AbelianSheaf.{u, u + 1} Y} (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((inverseImage g).obj ((directImage f).obj F)) := by
  have : IsFinite f' := MorphismProperty.of_isPullback H (inferInstance : IsFinite f)
  have hFk : Constructible.IsConstructible ((inverseImage k).obj F) :=
    Constructible.isConstructible_pullback_of_qcqs k hF
  have hImage := isConstructible_directImage_of_isAffine_of_isNoetherian f' hFk
  have : IsIso ((baseChangeMap f f' g k H.w.symm).app F) :=
    finiteBaseChange_app_isIso f f' g k H F
  exact (Constructible.isConstructible_iff_of_iso
    (asIso ((baseChangeMap f f' g k H.w.symm).app F))).mpr hImage

/-- Finite direct image preserves original finite-abelian constructibility
on an arbitrary Noetherian target scheme. -/
theorem isConstructible_directImage_of_isNoetherian
    {Y X : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsFinite f]
    {F : AbelianSheaf.{u, u + 1} Y} (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((directImage f).obj F) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Y := ⟨⟩
  apply Constructible.isConstructible_of_affineOpenPullbacks
  intro U
  have : IsAffine U.1.toScheme := U.property
  have : IsNoetherian U.1.toScheme := ⟨⟩
  exact isConstructible_directImagePullback_of_isAffine_of_isNoetherian
    f (pullback.snd f U.1.ι) U.1.ι (pullback.fst f U.1.ι)
    (IsPullback.of_hasPullback f U.1.ι) hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
