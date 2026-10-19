/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GeometricRegularity
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Geometric regularity and the flatness hypothesis

The relative criterion applies to arbitrary schemes over a locally Noetherian base.
The closed point Spec(F₂) in Spec(Z) has geometrically regular fibers but is not smooth:
flatness in the criterion is essential.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

example {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [Flat f]
    (h : ∀ s, GeometricallyRegular (f.fiberToSpecResidueField s)) : Smooth f := by
  let : GeometricallyRegular f :=
    (GeometricallyRegular.iff_forall_fiberToSpecResidueField f).mpr h
  exact (smooth_iff_flat_and_geometricallyRegular f).mpr ⟨inferInstance, inferInstance⟩

private theorem closedImmersion_geometricallyRegular {X S : Scheme.{u}} (f : X ⟶ S)
    [IsClosedImmersion f] : GeometricallyRegular f where
  geometrically_regularStalks := by
    intro K _ y Z fst snd h
    let : IsClosedImmersion snd := MorphismProperty.of_isPullback h inferInstance
    let : Etale snd := Etale.of_formallyUnramified_of_flat snd
    exact Scheme.smoothFieldRegularity K Z snd inferInstance

private def modTwoClosedPoint : Spec (.of (ZMod 2)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 2)))

private theorem modTwoClosedPoint_isClosedImmersion : IsClosedImmersion modTwoClosedPoint :=
  IsClosedImmersion.spec_of_surjective _ (ZMod.intCast_surjective (n := 2))

private theorem modTwoClosedPoint_not_flat : ¬ Flat modTwoClosedPoint := by
  intro hf
  have hflat : (Int.castRingHom (ZMod 2)).Flat :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mp hf
  have he : Int.castRingHom (ZMod 2) = algebraMap ℤ (ZMod 2) := by ext; simp
  let : Module.Flat ℤ (ZMod 2) := RingHom.flat_algebraMap_iff.mp (he ▸ hflat)
  have hinj := Module.Flat.isSMulRegular_of_nonZeroDivisors (R := ℤ) (M := ZMod 2)
    (mem_nonZeroDivisors_of_ne_zero (show (2 : ℤ) ≠ 0 by decide))
  have h : (1 : ZMod 2) = 0 := hinj (by decide)
  exact one_ne_zero h

example : GeometricallyRegular modTwoClosedPoint ∧ ¬ Smooth modTwoClosedPoint := by
  let := modTwoClosedPoint_isClosedImmersion
  refine ⟨closedImmersion_geometricallyRegular modTwoClosedPoint, ?_⟩
  intro hs
  let := hs
  exact modTwoClosedPoint_not_flat inferInstance
