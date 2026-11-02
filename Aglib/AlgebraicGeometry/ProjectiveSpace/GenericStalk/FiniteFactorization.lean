/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.GenericStalk
public import Aglib.AlgebraicGeometry.FunctionField.Finite
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# Original generic-field finiteness from a finite base factorization

An actual injective finite base map and the original birational triangle
supply dominance and finiteness for the unchanged genericImageBaseMap.
No dimension, properness, regularity or closed-immersion premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Injectivity is sufficient for the actual affine map to be dominant. -/
private theorem finiteFactorization_specMap_dominant
    {R A : Type u} [CommRing R] [CommRing A]
    (sigma : R →+* A) (hinj : Function.Injective sigma) :
    IsDominant (Spec.map (CommRingCat.ofHom sigma)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap sigma)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot sigma).mp hinj]
  exact bot_le

/-- The actual structural factorization supplies the required dominance instance. -/
theorem isDominant_of_injective_base_triangle
    {R A : Type u} [CommRing R] [CommRing A]
    (sigma : R →+* A) (hinj : Function.Injective sigma)
    (iota : Type u) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f]
    (i : X ⟶ ProjectiveSpace R iota)
    (hg : i ≫ ProjectiveSpace.toSpec R iota =
      f ≫ Spec.map (CommRingCat.ofHom sigma)) :
    IsDominant (i ≫ ProjectiveSpace.toSpec R iota) := by
  let := finiteFactorization_specMap_dominant sigma hinj
  rw [hg]
  infer_instance

/-- Finiteness for the original genericImageBaseMap, without a field-finiteness premise. -/
theorem genericImageBaseMap_finite_of_finite_base_triangle
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] [IsDomain A]
    (sigma : R →+* A) (hfinite : sigma.Finite) (hinj : Function.Injective sigma)
    (iota : Type u) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (i : X ⟶ ProjectiveSpace R iota)
    (hg : i ≫ ProjectiveSpace.toSpec R iota =
      f ≫ Spec.map (CommRingCat.ofHom sigma)) :
    letI := isDominant_of_injective_base_triangle sigma hinj iota f i hg
    (ProjectiveSpace.genericImageBaseMap R iota i).Finite := by
  let := isDominant_of_injective_base_triangle sigma hinj iota f i hg
  let s := Spec.map (CommRingCat.ofHom sigma)
  let : IsDominant s := finiteFactorization_specMap_dominant sigma hinj
  let : IsFinite s := (IsFinite.SpecMap_iff _).mpr hfinite
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) := hff
  have hs : (Scheme.functionFieldMap s).Finite := Scheme.functionFieldMap_finite s
  have hf : (Scheme.functionFieldMap f).Finite :=
    RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        (CommRingCat.ofHom (Scheme.functionFieldMap f))).2
  have hcongr {a b : X ⟶ Spec (CommRingCat.of R)}
      [IsDominant a] [IsDominant b] (hab : a = b) :
      Scheme.functionFieldMap a = Scheme.functionFieldMap b := by
    subst b
    rfl
  have hmap : ProjectiveSpace.genericImageBaseMap R iota i =
      (Scheme.functionFieldMap f).comp (Scheme.functionFieldMap s) := by
    change Scheme.functionFieldMap (i ≫ ProjectiveSpace.toSpec R iota) = _
    exact (hcongr hg).trans (Scheme.functionFieldMap_comp f s)
  rw [hmap]
  exact hf.comp hs


end AlgebraicGeometry.ProjectiveSpace
