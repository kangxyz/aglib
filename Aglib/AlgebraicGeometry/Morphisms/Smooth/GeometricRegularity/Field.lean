/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Geometrically.Regular
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity
public import Aglib.RingTheory.Smooth.GeometricRegularity

/-!
# Smooth morphisms and geometric regularity

Smoothness gives geometric regularity over an arbitrary base through smooth-field regularity
after base change. Conversely, a locally finite-type scheme over a field is smooth when its
geometric fibers have regular stalks. Geometric regularity itself does not include flatness.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Every smooth morphism has geometrically regular fibers. -/
instance (priority := 100) [Smooth f] : GeometricallyRegular f where
  geometrically_regularStalks := by
    intro K _ y Z fst snd h
    have : Smooth snd := MorphismProperty.of_isPullback h inferInstance
    exact Scheme.smoothFieldRegularity K Z snd inferInstance

open scoped TensorProduct

/-- Geometric regularity of a finite-type affine scheme gives regularity of every
field-extension tensor product, with the extension field in the left tensor factor. -/
theorem GeometricallyRegular.isRegularRing_tensorProduct
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [GeometricallyRegular (Spec.map (CommRingCat.ofHom (algebraMap k A)))]
    (K : Type u) [Field K] [Algebra k K] : IsRegularRing (K ⊗[k] A) := by
  let : IsNoetherianRing (K ⊗[k] A) := Algebra.FiniteType.isNoetherianRing K _
  apply (Scheme.regularStalks_spec_iff (K ⊗[k] A)).mp
  apply ObjectProperty.prop_of_iso Scheme.RegularStalks (pullbackSpecIso k K A)
  exact pullback_of_geometrically'
    (GeometricallyRegular.geometrically_regularStalks
      (f := Spec.map (CommRingCat.ofHom (algebraMap k A)))) K
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))

set_option backward.isDefEq.respectTransparency false in
/-- A locally finite-type scheme over an arbitrary field is smooth if it is geometrically
regular. -/
theorem Smooth.of_geometricallyRegular_of_field {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [GeometricallyRegular f] : Smooth f := by
  wlog hX : ∃ A, X = Spec A generalizing f X
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) X.affineCover]
    intro i
    have hgeom : GeometricallyRegular (X.affineCover.f i ≫ f) :=
      GeometricallyRegular.comp_isOpenImmersion _ _
    exact this _ ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hf : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  algebraize [φ.hom]
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.smooth_algebraMap.mpr
  exact Algebra.Smooth.of_geometricallyRegular k A fun K _ _ ↦
    GeometricallyRegular.isRegularRing_tensorProduct k A K

end AlgebraicGeometry
