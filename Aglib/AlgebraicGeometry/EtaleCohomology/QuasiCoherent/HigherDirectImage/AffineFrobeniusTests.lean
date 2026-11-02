/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineFrobeniusCohomology
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineAlgebras

/-! # Frobenius on the original affine étale tests

The original affine-cohomology square is stated at the literal structural arrow
of each native affine test. The existing affine algebra retains that same ring
and arrow; no replacement chart or coefficient module is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme.Cohomology

universe u eX eY

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge Scheme.Modules.isQuasicoherent_unit
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)

local instance :
    (((Scheme.Modules.pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent :=
  moduleHigherDirectImage_isQuasicoherent f (SheafOfModules.unit X.ringCatSheaf) q

/-- Normalize the entire original equation at a variable structural arrow,
before its source is a chosen affine test. -/
private theorem originalAffineFrobenius_specMap_eq
    (T : CommRingCat.{u}) [Algebra A T]
    (j : Spec T ⟶ Spec (CommRingCat.of A)) [Etale j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A T) : CommRingCat.of A ⟶ T) = j)
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]
    (x : (moduleSpecΓFunctor (R := T)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf)))) :
    let O := SheafOfModules.unit X.ringCatSheaf
    let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj O
    let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
      (higherDirectImageFrobenius.{u, eX} f q p hp hA)
    AffineCohomologyFrobenius.{u, eY} f j q p hp hA x
      ((Ψ.hom.app (op (Scheme.Etale.mk j)) (ULift.up x)).down) := by
  subst j
  exact higherDirectImageAffineSectionsEquiv_affineFrobenius.{u, eX, eY}
    f q (CommAlgCat.of A T) p hp hA x

variable (U : (Spec (CommRingCat.of A)).AffineEtale)
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eY} (AbelianSheaf.{u, u + 1}
    (Limits.pullback ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of A))).obj U).hom f))]

local instance : Etale ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of A))).obj U).hom :=
  ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of A))).obj U).prop

/-- The actual coefficient Frobenius intertwines with original inverse-image
Frobenius at the literal original structural arrow of every affine étale test. -/
theorem higherDirectImageAffineSectionsEquiv_affineTest_frobenius
    (x : (moduleSpecΓFunctor (R := U.left.unop)).obj
      ((Scheme.Modules.pullback
        ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of A))).obj U).hom).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf)))) :
    let V := (Scheme.AffineEtale.Spec (Spec (CommRingCat.of A))).obj U
    let O := SheafOfModules.unit X.ringCatSheaf
    let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj O
    let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
      (higherDirectImageFrobenius.{u, eX} f q p hp hA)
    AffineCohomologyFrobenius.{u, eY} f V.hom q p hp hA x
      ((Ψ.hom.app (op V) (ULift.up x)).down) := by
  let : Algebra A U.left.unop :=
    inferInstanceAs (Algebra A (EtaleAffineBasis.affineAlgebra (CommRingCat.of A) U))
  have h := originalAffineFrobenius_specMap_eq.{u, eX, eY} f q U.left.unop
    ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of A))).obj U).hom
    (EtaleAffineBasis.affineAlgebra_specMap (CommRingCat.of A) U) p hp hA x
  dsimp only
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
