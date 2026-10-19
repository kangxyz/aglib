/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Spectral
public import Aglib.AlgebraicGeometry.Modules.Invertible.Locality
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The fibrewise criterion for relative effective Cartier divisors

Let `p : X ⟶ T` be flat and locally of finite presentation, and let `i : D ⟶ X` be a closed
immersion with `i ≫ p` flat and locally of finite presentation. Then `D` is a relative effective
Cartier divisor exactly when every fibre `D_t ⊆ X_t` is an effective Cartier divisor
(`isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier`). This is Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Lemma 3.4, pp. 22-23, in the arbitrary-base form of the
"In particular" sentence of Stacks Project, Tag 062Y (Lemma 31.19.9). The base can be
non-Noetherian and nonreduced. Over a locally Noetherian base with `p` locally of finite type
all finite-presentation conditions are automatic
(`isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier_of_isLocallyNoetherian`). These
hypotheses are weaker than Kleiman's standing ones (p. 15), which also require `p` separated
and of finite type.

Only the direction from the fibres uses the hypotheses on `p` and the finite presentation of
`i ≫ p`; the converse holds for every closed subscheme flat over the base
(`IsRelativeEffectiveCartier.fiberIsEffectiveCartier`). The proof covers `X` by affine opens
over affine opens of `T`, transports the fibre pullback condition to the spectral family, and
applies `spectralIdeal_isLocallyRankOne_of_fiberPullbackRankOne`.
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

/-- The fibre pullback condition makes the actual ideal locally rank one over affine schemes. -/
theorem idealModule_isLocallyRankOne_of_fiberPullbackRankOne_of_isAffine [IsAffine T]
    [IsAffine X] (p : X ⟶ T) (i : D ⟶ X) [Flat p] [LocallyOfFinitePresentation p]
    [IsClosedImmersion i] [Flat (i ≫ p)] [LocallyOfFinitePresentation (i ≫ p)]
    (hM : FiberPullbackRankOne p (idealModule i) Set.univ) :
    IsLocallyRankOne X (idealModule i) := by
  have : IsAffine D := isAffine_of_isAffineHom i
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
  have hM' : FiberPullbackRankOne (Spec.map p.appTop) (idealModule (Spec.map i.appTop))
      Set.univ :=
    (hM.pullback X.isoSpec.inv (Spec.map p.appTop) T.isoSpec.inv
      (Scheme.isoSpec_inv_naturality p).symm).of_iso
      (asIso (idealPullbackMap i (Spec.map i.appTop) X.isoSpec.inv D.isoSpec.inv hw))
  have hSpec := spectralIdeal_isLocallyRankOne_of_fiberPullbackRankOne p.appTop i.appTop hM'
  have hw' : D.isoSpec.hom ≫ Spec.map i.appTop = i ≫ X.isoSpec.hom :=
    Scheme.isoSpec_hom_naturality i
  have : IsIso (idealPullbackMap (Spec.map i.appTop) i X.isoSpec.hom D.isoSpec.hom hw') :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact isLocallyRankOne_of_iso X
    (asIso (idealPullbackMap (Spec.map i.appTop) i X.isoSpec.hom D.isoSpec.hom hw'))
    (pullback_locallyRankOne X.isoSpec.hom _ hSpec)

/-- The fibre pullback condition makes the actual ideal locally rank one, for `p` flat and
locally of finite presentation and `i ≫ p` flat and locally of finite presentation. -/
theorem idealModule_isLocallyRankOne_of_fiberPullbackRankOne (p : X ⟶ T) (i : D ⟶ X)
    [Flat p] [LocallyOfFinitePresentation p] [IsClosedImmersion i] [Flat (i ≫ p)]
    [LocallyOfFinitePresentation (i ≫ p)]
    (hM : FiberPullbackRankOne p (idealModule i) Set.univ) :
    IsLocallyRankOne X (idealModule i) := by
  have hloc : ∀ x : X, ∃ (U : T.Opens) (_ : IsAffineOpen U)
      (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧ V ≤ p ⁻¹ᵁ U := by
    intro x
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show p x ∈ (⊤ : T.Opens) from trivial)
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ p ⁻¹ᵁ U from hxU)
    exact ⟨U, hU, V, hV, hxV, hVU⟩
  choose U hU V hV hxV hVU using hloc
  have hcover : IsOpenCover V := .mk (by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxV x⟩)
  apply isLocallyRankOne_of_cover_restrict (idealModule i) V hcover
  intro x
  have : IsAffine (U x).toScheme := hU x
  have : IsAffine (V x).toScheme := hV x
  have : Flat (p.resLE (U x) (V x) (hVU x)) :=
    IsZariskiLocalAtSource.resLE (hVU x) inferInstance
  have : LocallyOfFinitePresentation (p.resLE (U x) (V x) (hVU x)) :=
    IsZariskiLocalAtSource.resLE (hVU x) inferInstance
  have hle : i ⁻¹ᵁ V x ≤ (i ≫ p) ⁻¹ᵁ U x := by
    rw [Scheme.Hom.comp_preimage]
    exact i.preimage_mono (hVU x)
  have hcomp : (i ∣_ V x) ≫ p.resLE (U x) (V x) (hVU x) =
      (i ≫ p).resLE (U x) (i ⁻¹ᵁ V x) hle := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
  have : Flat ((i ∣_ V x) ≫ p.resLE (U x) (V x) (hVU x)) := by
    rw [hcomp]
    exact IsZariskiLocalAtSource.resLE hle inferInstance
  have : LocallyOfFinitePresentation ((i ∣_ V x) ≫ p.resLE (U x) (V x) (hVU x)) := by
    rw [hcomp]
    exact IsZariskiLocalAtSource.resLE hle inferInstance
  have hw : (V x).ι ≫ p = p.resLE (U x) (V x) (hVU x) ≫ (U x).ι :=
    (Scheme.Hom.resLE_comp_ι p (hVU x)).symm
  have hM' : FiberPullbackRankOne (p.resLE (U x) (V x) (hVU x)) (idealModule (i ∣_ V x))
      Set.univ :=
    (hM.pullback (V x).ι _ (U x).ι hw).of_iso (asIso (idealPullbackMap i (i ∣_ V x) (V x).ι
      (i ⁻¹ᵁ V x).ι (morphismRestrict_ι i (V x)).symm))
  exact isLocallyRankOne_of_iso (V x).toScheme (idealRestrictionIso i (V x)).symm
    (idealModule_isLocallyRankOne_of_fiberPullbackRankOne_of_isAffine _ _ hM')

/-- **Fibrewise criterion** (Kleiman, Lemma 3.4; Stacks Project, Tag 062Y): for `p` flat and
locally of finite presentation and a closed subscheme `D` with `D ⟶ T` flat and locally of
finite presentation, `D` is a relative effective Cartier divisor as soon as every fibre
`D_t ⊆ X_t` is an effective Cartier divisor. -/
theorem isRelativeEffectiveCartier_of_fiberIsEffectiveCartier (p : X ⟶ T) (i : D ⟶ X)
    [Flat p] [LocallyOfFinitePresentation p] [IsClosedImmersion i] [Flat (i ≫ p)]
    [LocallyOfFinitePresentation (i ≫ p)] (h : ∀ t : T, FiberIsEffectiveCartier i p t) :
    IsRelativeEffectiveCartier i p :=
  ⟨⟨inferInstance, idealModule_isLocallyRankOne_of_fiberPullbackRankOne p i
    (fiberPullbackRankOne_idealModule p i Set.univ fun t _ ↦ h t)⟩, inferInstance⟩

/-- The fibrewise criterion as an equivalence (Kleiman, Lemma 3.4, (i) ⇔ (ii) on all fibres). -/
theorem isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier (p : X ⟶ T) (i : D ⟶ X)
    [Flat p] [LocallyOfFinitePresentation p] [IsClosedImmersion i] [Flat (i ≫ p)]
    [LocallyOfFinitePresentation (i ≫ p)] :
    IsRelativeEffectiveCartier i p ↔ ∀ t : T, FiberIsEffectiveCartier i p t :=
  ⟨fun hD t ↦ hD.fiberIsEffectiveCartier t,
    isRelativeEffectiveCartier_of_fiberIsEffectiveCartier p i⟩

/-- The fiberwise criterion over a locally Noetherian base with `p` flat and locally of finite
type, a weakening of Kleiman's standing hypotheses (which also require `p` separated and of
finite type). The finite-presentation conditions are then automatic. -/
theorem isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier_of_isLocallyNoetherian
    [IsLocallyNoetherian T] (p : X ⟶ T) (i : D ⟶ X) [Flat p] [LocallyOfFiniteType p]
    [IsClosedImmersion i] [Flat (i ≫ p)] :
    IsRelativeEffectiveCartier i p ↔ ∀ t : T, FiberIsEffectiveCartier i p t :=
  isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier p i

end AlgebraicGeometry.Scheme.Hom
