/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.HomologyClass
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.SourceIsomorphism

/-!
# The original principal class on the literal localized quotient

The actual geometric principal homology map is followed by the actual
source-isomorphism comparison. Its original source precomposition cancels
the inverse quotient/localization factor in the same original top class.
The induced coefficient frame and exact list-length cast are retained.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A) (r : A)

local instance {S : CommRingCat.{u}} (t : List S) :
    IsClosedImmersion (Spec.map (regularListQuotientMap t)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

local instance : IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (regularListPrincipalClosedMap s r))) :=
  IsClosedImmersion.spec_of_surjective _
    (IsLocalization.map_surjective_of_surjective (Submonoid.powers r) (Localization.Away r)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) Ideal.Quotient.mk_surjective)

/-- The same quotient/localization ring equivalence gives the actual source-only square. -/
theorem regularListPrincipalSourceOnlySquare :
    let S := CommRingCat.of (Localization.Away r)
    let q := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let t := regularListPrincipalList s r
    let e := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso
    IsPullback (Spec.map e.inv) (Spec.map (regularListQuotientMap (A := S) t))
      (Spec.map q) (𝟙 (Spec S)) := by
  intro S q t e
  have he : regularListQuotientMap (A := S) t ≫ e.hom = q := by
    ext a
    exact regularListPrincipalQuotientEquiv_mk s r a
  have hi : q ≫ e.inv = regularListQuotientMap (A := S) t := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply IsPullback.of_horiz_isIso
  exact ⟨by rw [Category.comp_id, ← Spec.map_comp, hi]⟩

/-- Its original source-linear equivalence is exactly the already normalized principal one. -/
theorem regularListPrincipalSourceModuleIso_eq :
    closedImmersionSourceModuleIso (CommRingCat.ofHom (regularListPrincipalClosedMap s r))
        (regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
          (regularListPrincipalList s r)) (regularListPrincipalQuotientEquiv s r)
        (regularListPrincipalSourceOnlySquare s r) =
      regularListPrincipalModuleIso s r := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

variable (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
  [HasExt.{w} (ModuleCat.{u} A)]
  [HasExt.{z} (ModuleCat.{u} (Localization.Away r))]

/-- The actual principal geometric homology map and actual source normalization send the
original top class to the original localized-list class with its induced coefficient frame. -/
theorem regularListPrincipalNormalizedHomologyMap_topClass (x : A) :
    let S := Localization.Away r
    let σ : A ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap A S)
    let q' := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let t := regularListPrincipalList s r
    let τ := regularListQuotientMap (A := CommRingCat.of S) t
    let : IsClosedImmersion (Spec.map τ) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let J' := affineOpenRestrictedInjectiveResolution σ J
    let θ := affineRestrictGlobalSectionsIso σ L
    let e' := regularListPrincipalCoefficientFrame r e θ
    let : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
    let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
      s.length).symm ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
        (Ext.mk₀ e.inv) (add_zero s.length))
    affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length
      (closedImmersionSourceHomologyMap q' τ (regularListPrincipalQuotientEquiv s r)
        (regularListPrincipalSourceOnlySquare s r) J' (s.length : ℤ)
        (closedImmersionQuotientLocalizationHomologyMap (Ideal.ofList s) r J
          (s.length : ℤ) ξ)) =
      (cast (congrArg (fun k => Ext.{z}
        (ModuleCat.of S (S ⧸ Ideal.ofList t)) (ModuleCat.of S S) k)
        (List.length_map (as := s) (algebraMap A S)))
        (ChainComplex.Koszul.topExtClass t (hs.of_flat (S := S))
          (ModuleCat.of S S) (algebraMap A S x))).comp (Ext.mk₀ e'.inv)
            (add_zero s.length) := by
  intro S σ q' t τ hτ J' θ e' hflat ξ
  let : IsClosedImmersion (Spec.map τ) := hτ
  have hp := regularListPrincipalHomologyMap_topClass s hs r e J x
  have hs' := closedImmersionSourceHomologyMap_ext q' τ
    (regularListPrincipalQuotientEquiv s r) (regularListPrincipalSourceOnlySquare s r)
    J' s.length
    (closedImmersionQuotientLocalizationHomologyMap (Ideal.ofList s) r J (s.length : ℤ) ξ)
  rw [regularListPrincipalSourceModuleIso_eq] at hs'
  exact hs'.trans
    ((congrArg (fun γ => (Ext.mk₀ (regularListPrincipalModuleIso s r).hom).comp γ
      (zero_add s.length)) hp).trans (by
        rw [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp]))

end AlgebraicGeometry.Scheme.Modules
