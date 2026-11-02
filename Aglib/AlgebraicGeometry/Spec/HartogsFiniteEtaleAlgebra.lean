/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Hartogs.FiniteSections
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteFlat
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # The original finite algebra of a cover on a Hartogs open

The algebra is literally the original global section ring of the cover.
Finiteness follows from the actual finite locally free direct-image module.
The native quasi-affine affinization square recovers the original cover on
the original open, including its original projections. The finite extension
is not asserted to be etale outside that open.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- The affinization of an original affine-base scheme retains its exact
structural map through the original scalar restriction. -/
@[reassoc]
theorem toSpecΓ_comp_spec_affineScalarMap
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (affineScalarMap f)) = f := by
  change X.toSpecΓ ≫ Spec.map ((ΓSpecIso (.of A)).inv ≫ f.appTop) = f
  rw [Spec.map_comp, ← Category.assoc, ← toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The original finite flat cover gives a finite map on actual global
functions over a quasi-affine scheme with Noetherian global ring. -/
theorem appTop_finite_of_finiteFlat_of_quasiAffine
    {W U : Scheme.{u}} [U.IsQuasiAffine] [IsNoetherianRing Γ(U, ⊤)]
    (p : W ⟶ U) [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] :
    p.appTop.hom.Finite := by
  let M := Modules.pushforwardStructureSheaf p
  let : Modules.IsFiniteLocallyFree U M :=
    Modules.finiteFlat_pushforwardStructureSheaf_isFiniteLocallyFree p
  have h := Modules.Coherent.finite_globalSections_of_quasiAffine_of_noetherian U M
  exact h

/-- The scalar map of the actual cover algebra is the original composite
structural map, not an arbitrary algebra structure on its section ring. -/
theorem affineScalarMap_comp_hom
    {A : Type u} [CommRing A] {W U : Scheme.{u}}
    (j : U ⟶ Spec (.of A)) (p : W ⟶ U) :
    p.appTop.hom.comp (affineScalarMap j) = affineScalarMap (p ≫ j) := by
  change (((ΓSpecIso (.of A)).inv ≫ j.appTop) ≫ p.appTop).hom = _
  rw [Category.assoc, ← Hom.comp_appTop]
  rfl

/-- The actual global sections of a finite flat cover on a Hartogs open
form a finite algebra over the original base ring. No normality of either
ring or scheme is imposed. -/
theorem affineScalarMap_finite_of_hartogs_finiteFlat
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens)
    (hU : Function.Bijective (affineScalarMap U.ι))
    {W : Scheme.{u}} (p : W ⟶ U) [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] :
    (affineScalarMap (p ≫ U.ι)).Finite := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (U : Set (Spec (.of A))))
  let : U.toScheme.IsQuasiAffine := IsQuasiAffine.of_isImmersion U.ι
  let : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    isNoetherianRing_of_surjective A Γ(U.toScheme, ⊤) (affineScalarMap U.ι) hU.surjective
  rw [← affineScalarMap_comp_hom]
  exact (appTop_finite_of_finiteFlat_of_quasiAffine p).comp
    (RingHom.Finite.of_surjective (affineScalarMap U.ι) hU.surjective)

/-- The original cover is exactly the pullback of its original global
section algebra along the unchanged open. Native principal-localization
affinization proves the square; no affineness of the open is assumed. -/
theorem isPullback_hartogs_finiteAlgebra
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens)
    (hU : Function.Bijective (affineScalarMap U.ι))
    {W : Scheme.{u}} (p : W ⟶ U) [IsAffineHom p] :
    IsPullback p W.toSpecΓ U.ι
      (Spec.map (CommRingCat.ofHom (affineScalarMap (p ≫ U.ι)))) := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (U : Set (Spec (.of A))))
  let : U.toScheme.IsQuasiAffine := IsQuasiAffine.of_isImmersion U.ι
  let σ := CommRingCat.ofHom (affineScalarMap U.ι)
  let : IsIso σ := (ConcreteCategory.isIso_iff_bijective σ).mpr hU
  let e := asIso (Spec.map σ)
  apply (isPullback_toSpecΓ_toSpecΓ p).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · simp
  · simp
  · change U.toScheme.toSpecΓ ≫ Spec.map
      (CommRingCat.ofHom (affineScalarMap U.ι)) = 𝟙 _ ≫ U.ι
    simpa only [Category.id_comp] using
      toSpecΓ_comp_spec_affineScalarMap U.ι
  · change Spec.map p.appTop ≫ Spec.map σ =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (affineScalarMap (p ≫ U.ι)))
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1

end AlgebraicGeometry.Scheme
