/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Fiberwise
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Open
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.LineBundleStack
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Cartier fibres under base change of the base

For `p : X ⟶ T`, a closed subscheme `i : D ⟶ X` flat over `T`, and cartesian squares
`X' = X ×_T T'` along `g : T' ⟶ T` and `D' = D ×_X X'` (any choice of the cartesian squares, not
only the canonical pullbacks), the fiber of `D' ⊆ X'` over `t'` is effective Cartier exactly when
the fiber of `D` over `g t'` is (`fiberIsEffectiveCartier_iff_of_isPullback`; canonical form
`fiberIsEffectiveCartier_baseChange_iff`). The ideal of the first fiber is the pullback of the
ideal of the second along the map of fibers `fiberMapOfIsPullback`, which is the base change of
the field extension `Spec κ(t') ⟶ Spec κ(g t')` (Mathlib's
`isPullback_fiberToSpecResidueField_of_isPullback`). One direction is pullback of a line bundle;
the other is faithfully flat descent along that affine faithfully flat morphism
(`isLocallyRankOne_idealModule_of_pullback`), built from Aglib's affine descent
`Scheme.Modules.isLocallyRankOne_of_pullback_specMap_of_faithfullyFlat`. This is Kleiman's step
"as a field extension is faithfully flat" (*The Picard scheme*, arXiv:math/0504020v1, proof of
Thm 3.7, p. 24).

With the fiberwise criterion this gives, for `p` and `D ⟶ T` flat and locally of finite
presentation and an arbitrary `g`, `D'` is a relative effective Cartier divisor of `X' ⟶ T'`
exactly when all fibers of `D` over the image of `g` are effective Cartier
(`isRelativeEffectiveCartier_iff_of_isPullback`). Over a locally Noetherian base, with `p` flat,
locally of finite type and universally closed, `i` a closed immersion and `D` flat, this says
that `g` lands in, equivalently factors through, the open subscheme `fiberCartierLocus i p`
(`isRelativeEffectiveCartier_iff_range_subset_of_isPullback`,
`isRelativeEffectiveCartier_iff_exists_lift_of_isPullback`, and the `fibreInclusion` forms):
the representability step of the proof of Kleiman's Thm 3.7. Allowing arbitrary cartesian
squares covers the identifications `(X₀ ×_S H) ×_H T' ≅ X₀ ×_S T'` of a Hilbert-scheme universal
property; `IsRelativeEffectiveCartier.of_iso` transports along isomorphisms.
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

variable {D X Y T T' : Scheme.{u}}

/-- Local rank one of the actual ideal of a closed immersion descends along an affine, flat and
surjective morphism. -/
theorem isLocallyRankOne_idealModule_of_pullback (b : Y ⟶ X) [IsAffineHom b] [Flat b]
    [Surjective b] (i : D ⟶ X) [IsClosedImmersion i]
    (h : IsLocallyRankOne Y ((Scheme.Modules.pullback b).obj (idealModule i))) :
    IsLocallyRankOne X (idealModule i) := by
  have hloc : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    intro x
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using hloc
  have hcover : IsOpenCover V := .mk (by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxV x⟩)
  apply isLocallyRankOne_of_cover_restrict (idealModule i) V hcover
  intro x
  refine isLocallyRankOne_of_iso _ (idealRestrictionIso i (V x)).symm ?_
  have : IsAffine (V x).toScheme := hV x
  have : IsAffine (b ⁻¹ᵁ V x).toScheme := (hV x).preimage b
  have : IsAffine (i ⁻¹ᵁ V x).toScheme := (hV x).preimage i
  let iV := i ∣_ V x
  let bV := b ∣_ V x
  have : Surjective bV := IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance (V x)
  have hψ : bV.appTop.hom.FaithfullyFlat := by
    have hflat : Flat (Spec.map bV.appTop) :=
      (MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine bV)).mp inferInstance
    have hsurj : Surjective (Spec.map bV.appTop) :=
      (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine bV)).mp
        inferInstance
    exact RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
      ⟨Flat.SpecMap_iff.mp hflat, hsurj.surj⟩
  -- the spectral ideal on `Spec Γ(V, ⊤)`
  have hwi : (i ⁻¹ᵁ V x).toScheme.isoSpec.inv ≫ iV =
      Spec.map iV.appTop ≫ (V x).toScheme.isoSpec.inv :=
    (Scheme.isoSpec_inv_naturality iV).symm
  have : IsIso (idealPullbackMap iV (Spec.map iV.appTop) (V x).toScheme.isoSpec.inv
      (i ⁻¹ᵁ V x).toScheme.isoSpec.inv hwi) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  let eS := asIso (idealPullbackMap iV (Spec.map iV.appTop) (V x).toScheme.isoSpec.inv
    (i ⁻¹ᵁ V x).toScheme.isoSpec.inv hwi)
  -- the pulled-back ideal on `b ⁻¹ᵁ V`
  let eR := asIso (idealPullbackMap i iV (V x).ι (i ⁻¹ᵁ V x).ι (morphismRestrict_ι i (V x)).symm)
  have hb : IsLocallyRankOne (b ⁻¹ᵁ V x).toScheme
      ((Scheme.Modules.pullback bV).obj (idealModule iV)) := by
    let e : (Scheme.Modules.pullback bV).obj (idealModule iV) ≅
        (Scheme.Modules.pullback (b ⁻¹ᵁ V x).ι).obj
          ((Scheme.Modules.pullback b).obj (idealModule i)) :=
      (Scheme.Modules.pullback bV).mapIso eR.symm ≪≫
        (Scheme.Modules.pullbackComp bV (V x).ι).app _ ≪≫
          (Scheme.Modules.pullbackCongr (morphismRestrict_ι b (V x))).app _ ≪≫
            ((Scheme.Modules.pullbackComp (b ⁻¹ᵁ V x).ι b).app _).symm
    exact isLocallyRankOne_of_iso _ e.symm (pullback_locallyRankOne _ _ h)
  have hSpec : IsLocallyRankOne (Spec Γ(V x, ⊤)) (idealModule (Spec.map iV.appTop)) := by
    apply Scheme.Modules.isLocallyRankOne_of_pullback_specMap_of_faithfullyFlat bV.appTop hψ _
      inferInstance
    let e : (Scheme.Modules.pullback (Spec.map bV.appTop)).obj
          (idealModule (Spec.map iV.appTop)) ≅
        (Scheme.Modules.pullback (b ⁻¹ᵁ V x).toScheme.isoSpec.inv).obj
          ((Scheme.Modules.pullback bV).obj (idealModule iV)) :=
      (Scheme.Modules.pullback (Spec.map bV.appTop)).mapIso eS.symm ≪≫
        (Scheme.Modules.pullbackComp (Spec.map bV.appTop) (V x).toScheme.isoSpec.inv).app _ ≪≫
          (Scheme.Modules.pullbackCongr (Scheme.isoSpec_inv_naturality bV)).app _ ≪≫
            ((Scheme.Modules.pullbackComp (b ⁻¹ᵁ V x).toScheme.isoSpec.inv bV).app _).symm
    exact isLocallyRankOne_of_iso _ e.symm (pullback_locallyRankOne _ _ hb)
  have hw' : (i ⁻¹ᵁ V x).toScheme.isoSpec.hom ≫ Spec.map iV.appTop =
      iV ≫ (V x).toScheme.isoSpec.hom :=
    Scheme.isoSpec_hom_naturality iV
  have : IsIso (idealPullbackMap (Spec.map iV.appTop) iV (V x).toScheme.isoSpec.hom
      (i ⁻¹ᵁ V x).toScheme.isoSpec.hom hw') :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact isLocallyRankOne_of_iso _ (asIso (idealPullbackMap (Spec.map iV.appTop) iV
    (V x).toScheme.isoSpec.hom (i ⁻¹ᵁ V x).toScheme.isoSpec.hom hw'))
    (pullback_locallyRankOne (V x).toScheme.isoSpec.hom _ hSpec)

section IsPullback

variable {X' D' : Scheme.{u}} {p : X ⟶ T} {g : T' ⟶ T} {b : X' ⟶ X} {p' : X' ⟶ T'}
  {i : D ⟶ X} {a : D' ⟶ D} {i' : D' ⟶ X'}

/-- The morphism of fibres `X'_{t'} ⟶ X_{g t'}` induced by a cartesian square of the base change.
-/
abbrev fiberMapOfIsPullback (H : IsPullback b p' p g) (t' : T') :
    p'.fiber t' ⟶ p.fiber (g t') :=
  pullback.map _ _ _ _ b (Spec.map (g.residueFieldMap t')) g H.w.symm (by simp)

theorem fiberMapOfIsPullback_isPullback (H : IsPullback b p' p g) (t' : T') :
    IsPullback (fiberMapOfIsPullback H t') (p'.fiberToSpecResidueField t')
      (p.fiberToSpecResidueField (g t')) (Spec.map (g.residueFieldMap t')) :=
  isPullback_fiberToSpecResidueField_of_isPullback H t'

/-- The map of fibres is affine, flat and surjective: it is the base change of the field extension
`Spec κ(t') ⟶ Spec κ(g t')`. -/
theorem fiberMapOfIsPullback_isAffineHom_flat_surjective (H : IsPullback b p' p g) (t' : T') :
    IsAffineHom (fiberMapOfIsPullback H t') ∧ Flat (fiberMapOfIsPullback H t') ∧
      Surjective (fiberMapOfIsPullback H t') := by
  let e := Spec.map (g.residueFieldMap t')
  have hflat : Flat e := Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField _) _)
  have hsurj : Surjective e := ⟨fun x ↦ ⟨IsLocalRing.closedPoint _,
    Subsingleton.elim (α := PrimeSpectrum _) _ _⟩⟩
  have H₀ := (fiberMapOfIsPullback_isPullback H t').flip
  exact ⟨MorphismProperty.of_isPullback H₀ inferInstance, MorphismProperty.of_isPullback H₀ hflat,
    MorphismProperty.of_isPullback H₀ hsurj⟩

/-- For cartesian squares of the base change, the ideal of the fiber of `D'` over `t'` is the
pullback of the ideal of the fiber of `D` over `g t'` along the map of fibers. -/
theorem nonempty_fiber_idealIso_of_isPullback (H : IsPullback b p' p g)
    (H' : IsPullback a i' i b) [IsClosedImmersion i] [Flat (i ≫ p)] (t' : T') :
    Nonempty (idealModule (fibreInclusion p' i' (T'.fromSpecResidueField t')) ≅
      (Scheme.Modules.pullback (fiberMapOfIsPullback H t')).obj
        (idealModule (fibreInclusion p i (T.fromSpecResidueField (g t'))))) := by
  let q' := T'.fromSpecResidueField t'
  let q := T.fromSpecResidueField (g t')
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback H' inferInstance
  have : Flat (i' ≫ p') := MorphismProperty.of_isPullback (H'.paste_vert H) inferInstance
  have h1 : IsIso (idealPullbackMap i' (fibreInclusion p' i' q') (pullback.fst p' q')
      (pullback.fst (i' ≫ p') q') (fibreInclusion_fst p' i' q').symm) :=
    flatQuotient_idealPullbackMap_isIso p' q' (pullback.snd p' q') (pullback.fst p' q') i'
      (fibreInclusion p' i' q') _ _ (IsPullback.of_hasPullback p' q')
      (fibreInclusion_isPullback p' i' q')
  have h2 : IsIso (idealPullbackMap i i' b a H'.w) :=
    flatQuotient_idealPullbackMap_isIso p g p' b i i' a H'.w H H'
  have h3 : IsIso (idealPullbackMap i (fibreInclusion p i q) (pullback.fst p q)
      (pullback.fst (i ≫ p) q) (fibreInclusion_fst p i q).symm) :=
    flatQuotient_idealPullbackMap_isIso p q (pullback.snd p q) (pullback.fst p q) i
      (fibreInclusion p i q) _ _ (IsPullback.of_hasPullback p q) (fibreInclusion_isPullback p i q)
  have hfst : pullback.fst p' q' ≫ b = fiberMapOfIsPullback H t' ≫ pullback.fst p q :=
    (pullback.lift_fst _ _ _).symm
  exact ⟨(asIso (idealPullbackMap i' (fibreInclusion p' i' q') (pullback.fst p' q')
      (pullback.fst (i' ≫ p') q') (fibreInclusion_fst p' i' q').symm)).symm ≪≫
    (Scheme.Modules.pullback (pullback.fst p' q')).mapIso
      (asIso (idealPullbackMap i i' b a H'.w)).symm ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback (fiberMapOfIsPullback H t')).mapIso
      (asIso (idealPullbackMap i (fibreInclusion p i q) (pullback.fst p q)
        (pullback.fst (i ≫ p) q) (fibreInclusion_fst p i q).symm))⟩

/-- For cartesian squares of the base change, the fiber of `D'` over `t'` is effective Cartier iff
the fiber of `D` over `g t'` is (Kleiman, proof of Thm 3.7: a field extension is faithfully
flat). -/
theorem fiberIsEffectiveCartier_iff_of_isPullback (H : IsPullback b p' p g)
    (H' : IsPullback a i' i b) [IsClosedImmersion i] [Flat (i ≫ p)] (t' : T') :
    FiberIsEffectiveCartier i' p' t' ↔ FiberIsEffectiveCartier i p (g t') := by
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback H' inferInstance
  rw [fiberIsEffectiveCartier_iff, fiberIsEffectiveCartier_iff]
  obtain ⟨e⟩ := nonempty_fiber_idealIso_of_isPullback H H' t'
  obtain ⟨_, _, _⟩ := fiberMapOfIsPullback_isAffineHom_flat_surjective H t'
  constructor
  · intro h
    exact isLocallyRankOne_idealModule_of_pullback (fiberMapOfIsPullback H t') _
      (isLocallyRankOne_of_iso _ e h)
  · intro h
    exact isLocallyRankOne_of_iso _ e.symm (pullback_locallyRankOne _ _ h)

/-- **Base change and Cartier fibers** for any cartesian squares: for `p` and `D ⟶ T` flat and
locally of finite presentation, `D'` is a relative effective Cartier divisor of `X' ⟶ T'` exactly
when the fibers of `D` over the image of `g` are effective Cartier. -/
theorem isRelativeEffectiveCartier_iff_of_isPullback (H : IsPullback b p' p g)
    (H' : IsPullback a i' i b) [Flat p] [LocallyOfFinitePresentation p] [IsClosedImmersion i]
    [Flat (i ≫ p)] [LocallyOfFinitePresentation (i ≫ p)] :
    IsRelativeEffectiveCartier i' p' ↔ ∀ t' : T', FiberIsEffectiveCartier i p (g t') := by
  have : Flat p' := MorphismProperty.of_isPullback H inferInstance
  have : LocallyOfFinitePresentation p' := MorphismProperty.of_isPullback H inferInstance
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback H' inferInstance
  have : Flat (i' ≫ p') := MorphismProperty.of_isPullback (H'.paste_vert H) inferInstance
  have : LocallyOfFinitePresentation (i' ≫ p') :=
    MorphismProperty.of_isPullback (H'.paste_vert H) inferInstance
  rw [isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier]
  exact forall_congr' fun t' ↦ fiberIsEffectiveCartier_iff_of_isPullback H H' t'

/-- **Representability step** (proof of Kleiman, Thm 3.7), for any cartesian squares: over a
locally Noetherian base, with `p` flat, locally of finite type and universally closed, `i` a
closed immersion and `D` flat over `T`, the divisor `D'` is a relative effective Cartier divisor of
`X' ⟶ T'` exactly when `g` lands in the open locus of Cartier fibers. -/
theorem isRelativeEffectiveCartier_iff_range_subset_of_isPullback [IsLocallyNoetherian T]
    (H : IsPullback b p' p g) (H' : IsPullback a i' i b) [Flat p] [LocallyOfFiniteType p]
    [UniversallyClosed p] [IsClosedImmersion i] [Flat (i ≫ p)] :
    IsRelativeEffectiveCartier i' p' ↔ Set.range g ⊆ fiberCartierLocus i p := by
  rw [isRelativeEffectiveCartier_iff_of_isPullback H H', Set.range_subset_iff]
  rfl

/-- The factorization form of the representability step: `D'` is a relative effective Cartier
divisor exactly when `g` factors through the open subscheme `fiberCartierLocus i p`. -/
theorem isRelativeEffectiveCartier_iff_exists_lift_of_isPullback [IsLocallyNoetherian T]
    (H : IsPullback b p' p g) (H' : IsPullback a i' i b) [Flat p] [LocallyOfFiniteType p]
    [UniversallyClosed p] [IsClosedImmersion i] [Flat (i ≫ p)] :
    IsRelativeEffectiveCartier i' p' ↔
      ∃ g' : T' ⟶ (fiberCartierLocus i p).toScheme, g' ≫ (fiberCartierLocus i p).ι = g := by
  rw [isRelativeEffectiveCartier_iff_range_subset_of_isPullback H H']
  constructor
  · intro h
    exact ⟨IsOpenImmersion.lift (fiberCartierLocus i p).ι g (by rwa [Scheme.Opens.range_ι]),
      IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨g', rfl⟩ _ ⟨y, rfl⟩
    exact (g' y).2

end IsPullback

/-- The fiber of the canonical base change `D ×_T T' ⊆ X ×_T T'` over `t'` is effective Cartier
iff the fiber of `D` over `g t'` is. -/
theorem fiberIsEffectiveCartier_baseChange_iff (p : X ⟶ T) (i : D ⟶ X) [IsClosedImmersion i]
    [Flat (i ≫ p)] (g : T' ⟶ T) (t' : T') :
    FiberIsEffectiveCartier (fibreInclusion p i g) (pullback.snd p g) t' ↔
      FiberIsEffectiveCartier i p (g t') :=
  fiberIsEffectiveCartier_iff_of_isPullback (IsPullback.of_hasPullback p g)
    (fibreInclusion_isPullback p i g) t'

/-- **Base change and Cartier fibers**: for `p` and `D ⟶ T` flat and locally of finite
presentation, the base change of `D` along `g : T' ⟶ T` is a relative effective Cartier divisor
exactly when the fibers of `D` over the image of `g` are effective Cartier. -/
theorem isRelativeEffectiveCartier_fibreInclusion_iff (p : X ⟶ T) (i : D ⟶ X) [Flat p]
    [LocallyOfFinitePresentation p] [IsClosedImmersion i] [Flat (i ≫ p)]
    [LocallyOfFinitePresentation (i ≫ p)] (g : T' ⟶ T) :
    IsRelativeEffectiveCartier (fibreInclusion p i g) (pullback.snd p g) ↔
      ∀ t' : T', FiberIsEffectiveCartier i p (g t') :=
  isRelativeEffectiveCartier_iff_of_isPullback (IsPullback.of_hasPullback p g)
    (fibreInclusion_isPullback p i g)

/-- **Representability step** (proof of Kleiman, Thm 3.7): over a locally Noetherian base, with
`p` flat, locally of finite type and universally closed, `i` a closed immersion and `D` flat over
`T`, the base change of `D` along `g` is a relative effective Cartier divisor exactly when `g`
lands in the open locus of Cartier fibers. -/
theorem isRelativeEffectiveCartier_fibreInclusion_iff_range_subset [IsLocallyNoetherian T]
    (p : X ⟶ T) (i : D ⟶ X) [Flat p] [LocallyOfFiniteType p] [UniversallyClosed p]
    [IsClosedImmersion i] [Flat (i ≫ p)] (g : T' ⟶ T) :
    IsRelativeEffectiveCartier (fibreInclusion p i g) (pullback.snd p g) ↔
      Set.range g ⊆ fiberCartierLocus i p :=
  isRelativeEffectiveCartier_iff_range_subset_of_isPullback (IsPullback.of_hasPullback p g)
    (fibreInclusion_isPullback p i g)

/-- The factorization form for the canonical base change. -/
theorem isRelativeEffectiveCartier_fibreInclusion_iff_exists_lift [IsLocallyNoetherian T]
    (p : X ⟶ T) (i : D ⟶ X) [Flat p] [LocallyOfFiniteType p] [UniversallyClosed p]
    [IsClosedImmersion i] [Flat (i ≫ p)] (g : T' ⟶ T) :
    IsRelativeEffectiveCartier (fibreInclusion p i g) (pullback.snd p g) ↔
      ∃ g' : T' ⟶ (fiberCartierLocus i p).toScheme, g' ≫ (fiberCartierLocus i p).ι = g :=
  isRelativeEffectiveCartier_iff_exists_lift_of_isPullback (IsPullback.of_hasPullback p g)
    (fibreInclusion_isPullback p i g)

end AlgebraicGeometry.Scheme.Hom
