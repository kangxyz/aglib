/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalPurity

/-!
# The same canonical homology map on any original injective model

The native single-homology normalization and the already proved resolution
independence identify the ordinary top-homology maps for all original
injective resolutions. The local model map is therefore the actual native
canonical map composed with its original model comparison.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w a b
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasExt.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{a} (Spec A).Modules]
  [HasDerivedCategory.{b} (Spec (regularListQuotientRing s)).Modules]

/-- The native homology frame is independent of the original injective model, by the
already normalized native single isomorphism. -/
theorem derivedRegularListTopHomologyIso_resolution_independent
    (I J : InjectiveResolution L) :
    derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs I e =
      derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs J e := by
  apply Iso.ext
  rw [← derivedClosedImmersionRightAdjointRegularListIso_homology s hs I e,
    ← derivedClosedImmersionRightAdjointRegularListIso_homology s hs J e,
    derivedClosedImmersionRightAdjointRegularListIso_independent s hs I J e]

variable {R : CommRingCat.{u}} (α : R ⟶ A) (J : InjectiveResolution L)
  {Q : (Spec (regularListQuotientRing s)).Modules}
  (Δ : tensorSheaf (Spec (regularListQuotientRing s))
    (closedImmersionRegularListNormalLineBundle α s hs).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L)

/-- The original resolution top frame, inverse normal line and actual Delta contraction. -/
def regularListCanonicalModelTopHomologyIso :
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology
      (s.length : ℤ) ≅ Q :=
  closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e ≪≫
    closedImmersionRegularListInverseNormalLineIso α s hs e ≪≫
    normalDeterminantContractionIso
      (closedImmersionRegularListNormalLineBundle α s hs)
      (closedImmersionRegularListNormalFrameIso α s hs)
      (closedImmersionRegularListNormalDualFrameIso α s hs) Δ

/-- The common-model presentation is the same actual native canonical map, with the original
native unit comparison; no equality of unrelated isomorphisms is assumed. -/
theorem regularListCanonicalModelTopHomologyIso_native :
    derivedClosedImmersionRightAdjointRegularListModelHomologyIso s J (s.length : ℤ) ≪≫
      regularListCanonicalModelTopHomologyIso s hs e α J Δ =
    derivedClosedImmersionRegularListCanonicalTopHomologyIso α s hs e Δ := by
  apply Iso.ext
  rw [derivedClosedImmersionRegularListCanonicalTopHomologyIso_hom,
    derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso_hom]
  let en := closedImmersionRegularListInverseNormalLineIso α s hs e
  let ec := normalDeterminantContractionIso
    (closedImmersionRegularListNormalLineBundle α s hs)
    (closedImmersionRegularListNormalFrameIso α s hs)
    (closedImmersionRegularListNormalDualFrameIso α s hs) Δ
  have hm := (derivedClosedImmersionRightAdjointRegularListTopHomologyIso_hom s hs J e).symm
  have hn := congrArg Iso.hom (derivedRegularListTopHomologyIso_resolution_independent
    s hs e J (injectiveResolution L))
  have h := congrArg (fun f => f ≫ en.hom ≫ ec.hom) (hm.trans hn)
  simpa only [regularListCanonicalModelTopHomologyIso, Iso.trans_hom, Category.assoc] using h

end AlgebraicGeometry.Scheme.Modules
