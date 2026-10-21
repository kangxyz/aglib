/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.LocalSpectrum
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology

/-!
# Higher-direct-image stalks and cohomology over the local spectrum

For a qcqs morphism and a quasicoherent coefficient, the actual higher-image
stalk is the original cohomology of the actual base change to the local ring.
The comparison composes the original stalk/pullback-sections identification,
the canonical flat base-change arrow, and the original affine cohomology map.
Properness and local Noetherianity are not needed for this localization result.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (y : Y)

/-- Canonical localization of the actual higher-direct-image stalk, with the
unchanged structural local-ring action on the original cohomology. -/
def moduleHigherDirectImageStalkLinearEquiv (n : ℕ) :
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let N := (Scheme.Modules.pullback a).obj M
    let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
    letI := moduleCohomologyModuleOfHom _ α N n
    (moduleStalk Y y).obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ≃ₗ[
        Y.presheaf.stalk y]
      Sheaf.H.{u + 1} (moduleAddSheaf _ N) n := by
  let a := Limits.pullback.fst f (Y.fromSpecStalk y)
  let b := Limits.pullback.snd f (Y.fromSpecStalk y)
  let N := (Scheme.Modules.pullback a).obj M
  letI : Flat (Y.fromSpecStalk y) := Scheme.fromSpecStalk_flat Y y
  let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
  letI := moduleCohomologyModuleOfHom _ α N n
  let e₁ : _ ≃ₗ[Y.presheaf.stalk y] _ :=
    (stalkFromSpecStalkSectionsIso Y y
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)).toLinearEquiv
  let e₂ : _ ≃ₗ[Y.presheaf.stalk y] _ :=
    (moduleSpecΓFunctor.mapIso (higherDirectImageFlatBaseChangeIso
      a b f (Y.fromSpecStalk y)
      (IsPullback.of_hasPullback f (Y.fromSpecStalk y)) M n)).toLinearEquiv
  let e₃ : _ ≃ₗ[Y.presheaf.stalk y] _ :=
    moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) n
  exact e₁.trans (e₂.trans e₃)

/-- The localization equivalence retains the actual flat base-change map on
sections and the original affine cohomology comparison. -/
theorem moduleHigherDirectImageStalkLinearEquiv_apply (n : ℕ)
    (s : (moduleStalk Y y).obj (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let N := (Scheme.Modules.pullback a).obj M
    letI : Flat (Y.fromSpecStalk y) := Scheme.fromSpecStalk_flat Y y
    moduleHigherDirectImageStalkLinearEquiv f M y n s =
      moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) n
        (moduleSpecΓFunctor.map
          ((higherDirectImageFlatBaseChangeMap a b f (Y.fromSpecStalk y)
            (IsPullback.of_hasPullback f (Y.fromSpecStalk y)) n).app M)
          ((stalkFromSpecStalkSectionsIso Y y
            (((Scheme.Modules.pushforward f).rightDerived n).obj M)).hom s)) := by
  dsimp only
  simp only [moduleHigherDirectImageStalkLinearEquiv, LinearEquiv.trans_apply,
    CategoryTheory.Iso.toLinearEquiv_apply, Functor.mapIso_hom,
    higherDirectImageFlatBaseChangeIso_hom]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
