/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.Scalar

/-!
# Morphisms from spectra of local rings through scheme stalks

The canonical morphism `Spec 𝒪_{X,x} ⟶ X` composes with a structural morphism
`X ⟶ Spec R` as `Spec` of its actual `stalkScalar`. For any local ring `A`, a
morphism `Spec A ⟶ X` sending the closed point to `x` factors through a local
map `𝒪_{X,x} → A`, and that local map is uniquely determined by the original
scheme morphism. No field, Noetherianity, smoothness or finite-type condition
is required.

These are the scalar compatibility and the fixed-point existence/injectivity
forms of Mathlib's `Scheme.SpecToEquivOfLocalRing`, using the same
`Scheme.fromSpecStalk` and `Scheme.stalkClosedPointTo` maps.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical morphism `Spec 𝒪_{X,x} ⟶ X`, followed by the structure map `X ⟶ Spec R`, is
`Spec` of the structural scalar map `R → 𝒪_{X,x}`. -/
theorem fromSpecStalk_comp_eq_spec_map_stalkScalar {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (x : X) :
    X.fromSpecStalk x ≫ π = Spec.map (CommRingCat.ofHom (π.stalkScalar x)) := by
  rw [← SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  congr 1
  ext r
  rw [Hom.stalkScalar_eq_local]
  rfl

/-- Local maps from a stalk to a local ring are determined by the morphism of spectra. -/
theorem spec_map_comp_fromSpecStalk_injective {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] {φ φ' : X.presheaf.stalk x ⟶ R} [IsLocalHom φ.hom] [IsLocalHom φ'.hom]
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map φ' ≫ X.fromSpecStalk x) : φ = φ' := by
  have := (SpecToEquivOfLocalRing X R).symm.injective
    (a₁ := ⟨x, φ, inferInstance⟩) (a₂ := ⟨x, φ', inferInstance⟩) h
  exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp this).2)

/-- A morphism from the spectrum of a local ring sending the closed point to `x` factors through a
local map from the stalk at `x`. -/
theorem exists_spec_map_comp_fromSpecStalk {X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (g : Spec R ⟶ X) {x : X} (hx : g (closedPoint R) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ R, IsLocalHom φ.hom ∧ Spec.map φ ≫ X.fromSpecStalk x = g := by
  subst hx
  exact ⟨stalkClosedPointTo g, inferInstance, Spec_stalkClosedPointTo_fromSpecStalk g⟩

end AlgebraicGeometry.Scheme
