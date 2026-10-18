/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Composition
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.OpenTop

/-!
# The original two-stage principal map on a single restriction

The original restriction-composition isomorphism presents the released
two-stage principal arrow on its actual composite source open. It preserves
the original class one, so the original target common-degree class remains
its actual value.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A) (r : A)
  {L : (Spec A).Modules} (J : InjectiveResolution L)

/-- The same original two-stage principal arrow, with its original source-composition iso. -/
def regularListPrincipalSingleRestrictionHomologyMap (n : ℤ) :
    let φ : A ⟶ CommRingCat.of (Localization.Away r) :=
      CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let t := regularListPrincipalList s r
    ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology n).restrict
        (regularListPrincipalSource s r) ⟶
      (closedImmersionRightAdjointRegularListResolutionComplex
        (R := CommRingCat.of (Localization.Away r)) t
        (affineOpenRestrictedInjectiveResolution φ J)).homology n := by
  intro φ t
  let ψ : regularListQuotientRing s ⟶
      CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) :=
    CommRingCat.ofHom (algebraMap (A ⧸ Ideal.ofList s)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
  let ε := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv
  exact (restrictFunctorComp (Spec.map ε) (Spec.map ψ)).hom.app
      ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology n) ≫
    regularListPrincipalSheafHomologyMap s r J n

variable (hs : RingTheory.Sequence.IsWeaklyRegular A s) [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} (Localization.Away r))]

local instance : ((restrictFunctor (Spec.map
    (CommRingCat.ofHom (algebraMap A (Localization.Away r))))).obj L).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))))).symm.app L)
    (isQuasicoherent_pullback (CommRingCat.ofHom (algebraMap A (Localization.Away r))) L)

/-- The original composite principal arrow preserves the same original class-one section. -/
theorem regularListPrincipalSingleRestrictionHomologyMap_modelTopClass
    (V : (Spec (regularListQuotientRing (A := CommRingCat.of (Localization.Away r))
      (regularListPrincipalList s r))).Opens) :
    let S := Localization.Away r
    let φ : A ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap A S)
    let J' := affineOpenRestrictedInjectiveResolution φ J
    let θ := affineRestrictGlobalSectionsIso φ L
    let e' := regularListPrincipalCoefficientFrame r e θ
    letI : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
    (regularListPrincipalSingleRestrictionHomologyMap s r J (s.length : ℤ)).val.app (op V)
      (regularListModelTopClass s hs J e (1 : A) ((regularListPrincipalSource s r) ''ᵁ V)) =
      regularListModelTopClassInDegree (A := CommRingCat.of S)
        (regularListPrincipalList s r) (hs.of_flat (S := S))
        J' e' s.length (List.length_map (as := s) (algebraMap A S)) (1 : S) V := by
  intro S φ J' θ e'
  let : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
  let ψ : regularListQuotientRing s ⟶
      CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) :=
    CommRingCat.ofHom (algebraMap (A ⧸ Ideal.ofList s)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
  let ε := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv
  change (regularListPrincipalSheafHomologyMap s r J (s.length : ℤ)).val.app (op V)
      (((restrictFunctorComp (Spec.map ε) (Spec.map ψ)).hom.app
        ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
          (s.length : ℤ))).val.app (op V)
        (regularListModelTopClass s hs J e (1 : A)
          ((Spec.map ε ≫ Spec.map ψ) ''ᵁ V))) = _
  rw [regularListModelTopClass_restrictFunctorComp_one]
  simpa only [map_one] using
    regularListPrincipalSheafHomologyMap_modelTopClass s hs r e J (1 : A) V

end AlgebraicGeometry.Scheme.Modules
