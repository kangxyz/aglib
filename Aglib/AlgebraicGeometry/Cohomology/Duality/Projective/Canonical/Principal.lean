/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalPurity
public import Aglib.AlgebraicGeometry.Spec.Localization

/-!
# The actual principal refinement of a regular-list quotient

The literal quotient by the localized list is identified with the original
localization of the original quotient. The equivalence preserves every
quotient representative. Its spectral map followed by the original
localization open immersion is the chart refinement used in native
closed-right-adjoint restriction. No quotient ring or derived comparison
is treated as definitionally interchangeable with its isomorphic model.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A) (r : A)

/-- The original regular list mapped to the actual ambient principal localization. -/
abbrev regularListPrincipalList : List (Localization.Away r) :=
  s.map (algebraMap A (Localization.Away r))

private def principalQuotientMap : Localization.Away r →+*
    Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r) :=
  IsLocalization.Away.map (Localization.Away r)
    (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    (Ideal.Quotient.mk (Ideal.ofList s)) r

private theorem principalQuotientMap_surjective :
    Function.Surjective (principalQuotientMap s r) :=
  IsLocalization.map_surjective_of_surjective (Submonoid.powers r) (Localization.Away r)
    (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) Ideal.Quotient.mk_surjective

private theorem principalQuotientMap_kernel :
    Ideal.ofList (regularListPrincipalList s r) = RingHom.ker (principalQuotientMap s r) := by
  have h := CommRingCat.ker_localizationAway_map (regularListQuotientMap s) r
  change RingHom.ker (principalQuotientMap s r) =
    (RingHom.ker (Ideal.Quotient.mk (Ideal.ofList s))).map
      (algebraMap A (Localization.Away r)) at h
  rw [Ideal.mk_ker, Ideal.map_ofList] at h
  exact h.symm

/-- The same quotient/localization equivalence as in the original class-localization model. -/
@[no_expose] def regularListPrincipalQuotientEquiv :
    (Localization.Away r ⧸ Ideal.ofList (regularListPrincipalList s r)) ≃+*
      Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r) :=
  (Ideal.quotEquivOfEq (principalQuotientMap_kernel s r)).trans
    ((principalQuotientMap s r).quotientKerEquivOfSurjective
      (principalQuotientMap_surjective s r))

/-- Quotient representatives are sent through the original localized quotient homomorphism. -/
theorem regularListPrincipalQuotientEquiv_mk (a : Localization.Away r) :
    regularListPrincipalQuotientEquiv s r
      (Ideal.Quotient.mk (Ideal.ofList (regularListPrincipalList s r)) a) =
    IsLocalization.Away.map (Localization.Away r)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
      (Ideal.Quotient.mk (Ideal.ofList s)) r a := by
  exact RingHom.quotientKerEquivOfSurjective_apply_mk
    (principalQuotientMap_surjective s r) a

/-- The actual open chart on the original quotient, with its literal localized-list quotient. -/
def regularListPrincipalSource :
    Spec (CommRingCat.of
      (Localization.Away r ⧸ Ideal.ofList (regularListPrincipalList s r))) ⟶
      Spec (regularListQuotientRing s) :=
  Spec.map (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv ≫
    Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ Ideal.ofList s)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))))

instance regularListPrincipalSource_isOpenImmersion :
    IsOpenImmersion (regularListPrincipalSource s r) := by
  unfold regularListPrincipalSource
  infer_instance

/-- The normalized quotient chart is the same actual Cartesian principal restriction. -/
theorem regularListPrincipalSquare :
    IsPullback (regularListPrincipalSource s r)
      (Spec.map (regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
        (regularListPrincipalList s r)))
      (Spec.map (regularListQuotientMap s))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))) := by
  let A' : CommRingCat := .of (Localization.Away r)
  let B' : CommRingCat := .of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
  let φ : A' ⟶ B' := CommRingCat.ofHom (principalQuotientMap s r)
  let e := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso
  have he : regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
        (regularListPrincipalList s r) ≫ e.hom = φ := by
    ext a
    exact regularListPrincipalQuotientEquiv_mk s r a
  have h : IsPullback (Spec.map e.inv)
      (Spec.map (regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
        (regularListPrincipalList s r)))
      (Spec.map φ) (𝟙 (Spec A')) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id, ← Spec.map_comp, ← he]
      simp only [Category.assoc, e.hom_inv_id, Category.comp_id]⟩
  have hloc : (CommRingCat.ofHom (algebraMap A (Localization.Away r)) : A ⟶ A') ≫ φ =
      regularListQuotientMap s ≫ CommRingCat.ofHom
        (algebraMap (A ⧸ Ideal.ofList s) B') := by
    ext a
    change principalQuotientMap s r (algebraMap A (Localization.Away r) a) =
      algebraMap (A ⧸ Ideal.ofList s) B' (Ideal.Quotient.mk (Ideal.ofList s) a)
    simp only [principalQuotientMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have hsquare : regularListPrincipalSource s r ≫ Spec.map (regularListQuotientMap s) =
      Spec.map (regularListQuotientMap (A := A') (regularListPrincipalList s r)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))) := by
    change (Spec.map e.inv ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) B'))) ≫ Spec.map (regularListQuotientMap s) = _
    rw [Category.assoc, ← Spec.map_comp, ← hloc, Spec.map_comp, ← Category.assoc]
    have hh : Spec.map e.inv ≫ Spec.map φ =
        Spec.map (regularListQuotientMap (A := A') (regularListPrincipalList s r)) := by
      exact h.w.trans (Category.comp_id _)
    rw [hh]
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact hsquare
  · change (Spec.map (regularListQuotientMap s)) ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))).opensRange =
      (Spec.map e.inv ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (A ⧸ Ideal.ofList s)
          (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))))).opensRange
    have hA := Scheme.Hom.opensRange_localizationAway (R := A) r
    have hB := Scheme.Hom.opensRange_localizationAway (R := regularListQuotientRing s)
      (Ideal.Quotient.mk (Ideal.ofList s) r)
    have heRange := Scheme.Hom.opensRange_comp_of_isIso (Spec.map e.inv)
      (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ Ideal.ofList s)
        (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))))
    exact (congrArg (fun U => (Spec.map (regularListQuotientMap s)) ⁻¹ᵁ U) hA).trans
      ((SpecMap_preimage_basicOpen (regularListQuotientMap s) r).trans
        ((congrArg PrimeSpectrum.basicOpen
          (show (regularListQuotientMap s) r = Ideal.Quotient.mk (Ideal.ofList s) r from rfl)).trans
            (hB.symm.trans heRange.symm)))

end AlgebraicGeometry.Scheme.Modules
