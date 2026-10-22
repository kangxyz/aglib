/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.SpecKernel
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Kernel criteria for schematic dominance

Schematic dominance cancels a preceding map, can be detected by dense maps
into open-cover charts, and holds for spectra of injective ring maps.
These criteria do not assume that any scheme is reduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Schematic dominance cancels the first map, without a quasi-compactness premise. -/
theorem IsSchemeTheoreticallyDominant.of_comp_right {W Y Z : Scheme.{u}}
    (f : W ⟶ Y) (g : Y ⟶ Z) [IsSchemeTheoreticallyDominant (f ≫ g)] :
    IsSchemeTheoreticallyDominant g := by
  constructor
  exact le_bot_iff.mp ((f.le_ker_comp g).trans (by rw [Scheme.Hom.ker_eq_bot]))

/-- Dense maps into open-cover charts detect the kernel of a morphism whose
range contains their composites. -/
theorem isSchemeTheoreticallyDominant_of_openCover_ranges
    {Y Z : Scheme.{u}} (f : Z ⟶ Y) [IsOpenImmersion f] (C : Y.OpenCover)
    (W : C.I₀ → Scheme.{u}) (k : ∀ i, W i ⟶ C.X i)
    (hk : ∀ i, IsSchemeTheoreticallyDominant (k i))
    (h : ∀ i, Set.range (k i ≫ C.f i) ⊆ Set.range f) :
    IsSchemeTheoreticallyDominant f := by
  constructor
  apply le_bot_iff.mp
  have hcover := Scheme.Hom.iInf_ker_openCover_map_comp (𝟙 Y) C
  simp only [Category.comp_id, Scheme.Hom.ker_eq_bot_of_isIso] at hcover
  rw [← hcover]
  apply le_iInf
  intro i
  let := hk i
  have hh := (IsOpenImmersion.lift f (k i ≫ C.f i) (h i)).le_ker_comp f
  rw [IsOpenImmersion.lift_fac, Scheme.Hom.ker_comp, (k i).ker_eq_bot,
    Scheme.IdealSheafData.map_bot] at hh
  exact hh

/-- An injective affine coordinate map is schematically dominant, including
nonreduced and zero rings. -/
theorem isSchemeTheoreticallyDominant_specMap_of_injective
    {A R : Type u} [CommRing A] [CommRing R] (f : A →+* R)
    (hf : Function.Injective f) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.specMap_kernel_top, (RingHom.injective_iff_ker_eq_bot f).mp hf]
  simpa only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using
    Ideal.comap_bot_of_injective (f := (Scheme.ΓSpecIso (.of A)).hom.hom)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).1

end AlgebraicGeometry
