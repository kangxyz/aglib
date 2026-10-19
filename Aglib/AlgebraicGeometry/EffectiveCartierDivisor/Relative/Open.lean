/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Pointwise
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Openness of the locus of Cartier fibres

Let `T` be locally Noetherian, `p : X ⟶ T` flat and locally of finite type, and `i : D ⟶ X` a
closed immersion with `D` flat over `T`. Following the proof of Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 3.7, p. 24:

* the actual ideal of `D` is locally rank one at every point of a fibre `X_t` whose fibre
  divisor `D_t ⊆ X_t` is effective Cartier
  (`isLocallyRankOneAt_idealModule_of_fiberIsEffectiveCartier`, Lemma 3.4 at one fibre);
* conversely the fibre divisor over `t` is effective Cartier once the ideal is locally rank one
  at every point over `t` (`fiberIsEffectiveCartier_of_forall_isLocallyRankOneAt`, no
  Noetherian or flatness hypothesis on `p`);
* if `p` is moreover universally closed (for example proper), the set of `t` with effective
  Cartier fibre divisor is open (`isOpen_setOf_fiberIsEffectiveCartier`): it is the complement
  of the image of the closed complement of the locus where the ideal is locally rank one;
* over every open subscheme of the base contained in that set, `D` is a relative effective
  Cartier divisor (`isRelativeEffectiveCartier_restrict`). This half needs no properness.

The Noetherian hypothesis on `T` is used twice. It turns `LocallyOfFiniteType` into the
finite-presentation conditions on `p` and `i ≫ p` that Nakayama's lemma and the local criterion
need, and, since `X` is then locally Noetherian, it lets
`spectralIdeal_isLocallyRankOneAt_of_fiberPullbackRankOne` spread regularity of a local equation
from a stalk to a neighbourhood.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Hom

variable {D X T : Scheme.{u}}

/-- The fibre divisor over `t` is effective Cartier once the actual ideal is locally rank one at
every point of `X` over `t`. -/
theorem fiberIsEffectiveCartier_of_forall_isLocallyRankOneAt (p : X ⟶ T) (i : D ⟶ X)
    [IsClosedImmersion i] [Flat (i ≫ p)] (t : T)
    (h : ∀ x : X, p x = t → IsLocallyRankOneAt (idealModule i) x) :
    FiberIsEffectiveCartier i p t := by
  rw [fiberIsEffectiveCartier_iff]
  let q := T.fromSpecResidueField t
  have : IsIso (idealPullbackMap i (fibreInclusion p i q) (pullback.fst p q)
      (pullback.fst (i ≫ p) q) (fibreInclusion_fst p i q).symm) :=
    flatQuotient_idealPullbackMap_isIso p q (pullback.snd p q) (pullback.fst p q) i
      (fibreInclusion p i q) _ _ (IsPullback.of_hasPullback p q) (fibreInclusion_isPullback p i q)
  refine isLocallyRankOne_of_iso _ (asIso (idealPullbackMap i (fibreInclusion p i q)
    (pullback.fst p q) (pullback.fst (i ≫ p) q) (fibreInclusion_fst p i q).symm))
    (isLocallyRankOne_pullback_of_forall _ _ fun y ↦ h _ ?_)
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply]

/-- Affine form of the pointwise criterion at the fibres over `Z`, over a Noetherian ring. -/
theorem isLocallyRankOneAt_of_fiberPullbackRankOne_of_isAffine [IsAffine T] [IsAffine X]
    [IsLocallyNoetherian X] (p : X ⟶ T) (i : D ⟶ X) [Flat p] [LocallyOfFinitePresentation p]
    [IsClosedImmersion i] [Flat (i ≫ p)] [LocallyOfFinitePresentation (i ≫ p)] {Z : Set T}
    (hM : FiberPullbackRankOne p (idealModule i) Z) (x : X) (hx : p x ∈ Z) :
    IsLocallyRankOneAt (idealModule i) x := by
  have : IsAffine D := isAffine_of_isAffineHom i
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Flat (Spec.map p.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine p)).mp inferInstance
  have : LocallyOfFinitePresentation (Spec.map p.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @LocallyOfFinitePresentation
      (arrowIsoSpecΓOfIsAffine p)).mp inferInstance
  have : IsClosedImmersion (Spec.map i.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (arrowIsoSpecΓOfIsAffine i)).mp
      inferInstance
  have : Flat (Spec.map i.appTop ≫ Spec.map p.appTop) := by
    rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop]
    exact (MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine (i ≫ p))).mp
      inferInstance
  have : LocallyOfFinitePresentation (Spec.map i.appTop ≫ Spec.map p.appTop) := by
    rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop]
    exact (MorphismProperty.arrow_mk_iso_iff @LocallyOfFinitePresentation
      (arrowIsoSpecΓOfIsAffine (i ≫ p))).mp inferInstance
  have hw : D.isoSpec.inv ≫ i = Spec.map i.appTop ≫ X.isoSpec.inv :=
    (Scheme.isoSpec_inv_naturality i).symm
  have : IsIso (idealPullbackMap i (Spec.map i.appTop) X.isoSpec.inv D.isoSpec.inv hw) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  have hM' := (hM.pullback X.isoSpec.inv (Spec.map p.appTop) T.isoSpec.inv
    (Scheme.isoSpec_inv_naturality p).symm).of_iso
    (asIso (idealPullbackMap i (Spec.map i.appTop) X.isoSpec.inv D.isoSpec.inv hw))
  have hpt : (X.isoSpec.hom ≫ Spec.map p.appTop ≫ T.isoSpec.inv) x = p x := by
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have hP : Spec.map p.appTop (X.isoSpec.hom x) ∈ T.isoSpec.inv ⁻¹' Z := by
    change (X.isoSpec.hom ≫ Spec.map p.appTop ≫ T.isoSpec.inv) x ∈ Z
    rw [hpt]
    exact hx
  have hSpec := spectralIdeal_isLocallyRankOneAt_of_fiberPullbackRankOne p.appTop i.appTop hM'
    _ hP
  have hw' : D.isoSpec.hom ≫ Spec.map i.appTop = i ≫ X.isoSpec.hom :=
    Scheme.isoSpec_hom_naturality i
  have : IsIso (idealPullbackMap (Spec.map i.appTop) i X.isoSpec.hom D.isoSpec.hom hw') :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact (hSpec.pullback X.isoSpec.hom).of_iso
    (asIso (idealPullbackMap (Spec.map i.appTop) i X.isoSpec.hom D.isoSpec.hom hw'))

/-- **Pointwise criterion at the fibers over `Z`** (the whole-fiber form of Kleiman, Lemma 3.4,
(ii) ⇒ (i), with `D` flat over the whole base): over a locally Noetherian base, the actual ideal of
a closed subscheme flat over the base is locally rank one at every point lying over `Z`. -/
theorem isLocallyRankOneAt_of_fiberPullbackRankOne [IsLocallyNoetherian T] (p : X ⟶ T)
    (i : D ⟶ X) [Flat p] [LocallyOfFiniteType p] [IsClosedImmersion i] [Flat (i ≫ p)]
    {Z : Set T} (hM : FiberPullbackRankOne p (idealModule i) Z) (x : X) (hx : p x ∈ Z) :
    IsLocallyRankOneAt (idealModule i) x := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p x ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ p ⁻¹ᵁ U from hxU)
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : Flat (p.resLE U V hVU) := IsZariskiLocalAtSource.resLE hVU inferInstance
  have : LocallyOfFinitePresentation (p.resLE U V hVU) :=
    IsZariskiLocalAtSource.resLE hVU inferInstance
  have hle : i ⁻¹ᵁ V ≤ (i ≫ p) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage]
    exact i.preimage_mono hVU
  have hcomp : (i ∣_ V) ≫ p.resLE U V hVU = (i ≫ p).resLE U (i ⁻¹ᵁ V) hle := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
  have : Flat ((i ∣_ V) ≫ p.resLE U V hVU) := by
    rw [hcomp]
    exact IsZariskiLocalAtSource.resLE hle inferInstance
  have : LocallyOfFinitePresentation ((i ∣_ V) ≫ p.resLE U V hVU) := by
    rw [hcomp]
    exact IsZariskiLocalAtSource.resLE hle inferInstance
  have hw : V.ι ≫ p = p.resLE U V hVU ≫ U.ι := (Scheme.Hom.resLE_comp_ι p hVU).symm
  let eV := asIso (idealPullbackMap i (i ∣_ V) V.ι (i ⁻¹ᵁ V).ι (morphismRestrict_ι i V).symm)
  have hM' := (hM.pullback V.ι _ U.ι hw).of_iso eV
  have hxZ : p.resLE U V hVU ⟨x, hxV⟩ ∈ U.ι ⁻¹' Z := by
    change (p.resLE U V hVU ≫ U.ι) ⟨x, hxV⟩ ∈ Z
    rw [Scheme.Hom.resLE_comp_ι]
    exact hx
  have hV' := isLocallyRankOneAt_of_fiberPullbackRankOne_of_isAffine _ _ hM' ⟨x, hxV⟩ hxZ
  exact (hV'.of_iso eV.symm).of_pullback V.ι

/-- The actual ideal is locally rank one at every point of a fiber whose fiber divisor is
effective Cartier (the whole-fiber form of Kleiman, Lemma 3.4, (ii) ⇒ (i), at one fiber, with `D`
flat over the base). -/
theorem isLocallyRankOneAt_idealModule_of_fiberIsEffectiveCartier [IsLocallyNoetherian T]
    (p : X ⟶ T) (i : D ⟶ X) [Flat p] [LocallyOfFiniteType p] [IsClosedImmersion i]
    [Flat (i ≫ p)] (x : X) (hx : FiberIsEffectiveCartier i p (p x)) :
    IsLocallyRankOneAt (idealModule i) x :=
  isLocallyRankOneAt_of_fiberPullbackRankOne p i
    (fiberPullbackRankOne_idealModule p i {p x} fun _ ht ↦ ht ▸ hx) x rfl

/-- **Openness** (proof of Kleiman, Thm 3.7): for `p` flat, locally of finite type and
universally closed over a locally Noetherian base, and `D` closed and flat over the base, the
set of points whose fibre divisor `D_t ⊆ X_t` is effective Cartier is open. -/
theorem isOpen_setOf_fiberIsEffectiveCartier [IsLocallyNoetherian T] (p : X ⟶ T) (i : D ⟶ X)
    [Flat p] [LocallyOfFiniteType p] [UniversallyClosed p] [IsClosedImmersion i]
    [Flat (i ≫ p)] :
    IsOpen {t : T | FiberIsEffectiveCartier i p t} := by
  let L : Set X := {x | IsLocallyRankOneAt (idealModule i) x}
  have hset : {t : T | FiberIsEffectiveCartier i p t} = (p '' Lᶜ)ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · rintro ht x hxL rfl
      exact hxL (isLocallyRankOneAt_idealModule_of_fiberIsEffectiveCartier p i x ht)
    · intro h
      apply fiberIsEffectiveCartier_of_forall_isLocallyRankOneAt p i t
      intro x hx
      by_contra hxL
      exact h x hxL hx
  rw [hset, isOpen_compl_iff]
  exact p.isClosedMap _ (isOpen_setOf_isLocallyRankOneAt (idealModule i)).isClosed_compl

/-- Over every open subscheme of the base on which all fibre divisors are effective Cartier,
`D` is a relative effective Cartier divisor (Kleiman, proof of Thm 3.7). -/
theorem isRelativeEffectiveCartier_restrict [IsLocallyNoetherian T] (p : X ⟶ T) (i : D ⟶ X)
    [Flat p] [LocallyOfFiniteType p] [IsClosedImmersion i] [Flat (i ≫ p)] (U : T.Opens)
    (hU : ∀ t ∈ U, FiberIsEffectiveCartier i p t) :
    IsRelativeEffectiveCartier (i ∣_ (p ⁻¹ᵁ U)) (p ∣_ U) := by
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · let e := asIso (idealPullbackMap i (i ∣_ (p ⁻¹ᵁ U)) (p ⁻¹ᵁ U).ι (i ⁻¹ᵁ (p ⁻¹ᵁ U)).ι
      (morphismRestrict_ι i (p ⁻¹ᵁ U)).symm)
    refine isLocallyRankOne_of_iso _ e (isLocallyRankOne_pullback_of_forall _ _ fun y ↦ ?_)
    exact isLocallyRankOneAt_idealModule_of_fiberIsEffectiveCartier p i _ (hU _ y.2)
  · rw [← morphismRestrict_comp]
    infer_instance

/-- The open subscheme of Cartier fibres, under the hypotheses of
`isOpen_setOf_fiberIsEffectiveCartier`. -/
def fiberCartierLocus [IsLocallyNoetherian T] (i : D ⟶ X) (p : X ⟶ T) [Flat p]
    [LocallyOfFiniteType p] [UniversallyClosed p] [IsClosedImmersion i] [Flat (i ≫ p)] :
    T.Opens :=
  ⟨{t : T | FiberIsEffectiveCartier i p t}, isOpen_setOf_fiberIsEffectiveCartier p i⟩

theorem mem_fiberCartierLocus [IsLocallyNoetherian T] (p : X ⟶ T) (i : D ⟶ X) [Flat p]
    [LocallyOfFiniteType p] [UniversallyClosed p] [IsClosedImmersion i] [Flat (i ≫ p)]
    (t : T) : t ∈ fiberCartierLocus i p ↔ FiberIsEffectiveCartier i p t :=
  Iff.rfl

/-- Over the open subscheme of Cartier fibres, `D` is a relative effective Cartier divisor. -/
theorem isRelativeEffectiveCartier_restrict_fiberCartierLocus [IsLocallyNoetherian T]
    (p : X ⟶ T) (i : D ⟶ X) [Flat p] [LocallyOfFiniteType p] [UniversallyClosed p]
    [IsClosedImmersion i] [Flat (i ≫ p)] :
    IsRelativeEffectiveCartier (i ∣_ (p ⁻¹ᵁ fiberCartierLocus i p))
      (p ∣_ fiberCartierLocus i p) :=
  isRelativeEffectiveCartier_restrict p i _ fun _ ht ↦ ht

end AlgebraicGeometry.Scheme.Hom
