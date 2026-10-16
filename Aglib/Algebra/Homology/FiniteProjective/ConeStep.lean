/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Aglib.Algebra.Homology.FiniteProjective.HomologyCover
public import Aglib.Algebra.Homology.Flat.BoundedAcyclic
public import Aglib.Algebra.Homology.MappingCone.Homology

/-!
# Reducing the top degree of an actual bounded flat complex

Over a Noetherian ring, finite original homology supplies a finite-free
single-complex map surjecting on the actual top homology. Its original cone
has a lower cohomological upper bound and finite homology. The unchanged
native good truncation is then bounded, flat, and one degree shorter. Its
inclusion into that actual cone is a quasi-isomorphism.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The actual top-degree reduction for a bounded flat complex with finite
original homology. All returned complexes and maps are the native single,
signed cone, good truncation and original inclusion. -/
theorem exists_finiteFree_single_top_reduction
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℕ)
    [K.IsStrictlyGE 0] [K.IsStrictlyLE ((n : ℤ) + 1)]
    [∀ i, Module.Flat R (K.X i)] [∀ i, Module.Finite R (K.homology i)] :
    ∃ P : ModuleCat.{max u v} R, Module.Finite R P ∧ Module.Free R P ∧
      ∃ φ : (single (ModuleCat.{max u v} R) (.up ℤ) ((n : ℤ) + 1)).obj P ⟶ K,
        Epi (homologyMap φ ((n : ℤ) + 1)) ∧
        (let L := (mappingCone φ).truncLE (n : ℤ);
          L.IsStrictlyGE 0 ∧ L.IsStrictlyLE (n : ℤ) ∧
          (∀ i, Module.Flat R (L.X i)) ∧
          (∀ i, Module.Finite R (L.homology i)) ∧
          QuasiIso ((mappingCone φ).ιTruncLE (n : ℤ))) := by
  let b : ℤ := (n : ℤ) + 1
  obtain ⟨P, hPfinite, hPfree, φ, hφ⟩ :=
    exists_finiteFree_single_homology_epi K b
  let : Module.Finite R P := hPfinite
  let : Module.Free R P := hPfree
  let J : CochainComplex (ModuleCat.{max u v} R) ℤ :=
    (single (ModuleCat.{max u v} R) (.up ℤ) b).obj P
  let : Epi (homologyMap φ b) := hφ
  let : J.IsStrictlyLE b := inferInstance
  let (i : ℤ) : Module.Flat R (J.X i) := by
    by_cases hi : i = b
    · subst i
      exact Module.Flat.of_linearEquiv (singleObjXSelf (.up ℤ) b P).toLinearEquiv
    · let := ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (.up ℤ) b P i hi)
      infer_instance
  let (i : ℤ) : Module.Finite R (J.homology i) := by
    by_cases hi : i = b
    · subst i
      exact Module.Finite.equiv (singleObjHomologySelfIso (.up ℤ) b P).symm.toLinearEquiv
    · let := ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_homology (.up ℤ) b P i hi)
      infer_instance
  let C := mappingCone φ
  let : C.IsStrictlyLE b := by
    rw [isStrictlyLE_iff]
    intro i hi
    exact (mappingCone.isZero_X_iff φ i).mpr
      ⟨J.isZero_of_isStrictlyLE b (i + 1) (by omega),
        K.isZero_of_isStrictlyLE b i hi⟩
  let : C.IsStrictlyGE 0 := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact (mappingCone.isZero_X_iff φ i).mpr
      ⟨isZero_single_obj_X (.up ℤ) b P (i + 1) (by dsimp [b]; omega),
        K.isZero_of_isStrictlyGE 0 i hi⟩
  let : C.IsLE (n : ℤ) := by
    have h := mappingCone.isLE_of_epi_top φ b
    change C.IsLE (b - 1) at h
    rw [show b - 1 = (n : ℤ) by dsimp [b]; omega] at h
    exact h
  let (i : ℤ) : Module.Flat R (C.X i) := flat_X_mappingCone φ i
  let (i : ℤ) : Module.Finite R (C.homology i) := by
    exact (ModuleCat.finiteModule R).prop_X₂_of_exact
      (mappingCone.homologyRightShortComplex_exact φ i)
      (inferInstanceAs (Module.Finite R (K.homology i)))
      (inferInstanceAs (Module.Finite R (J.homology (i + 1))))
  let L := C.truncLE (n : ℤ)
  let : QuasiIso (C.ιTruncLE (n : ℤ)) := inferInstance
  have hLflat (i : ℤ) : Module.Flat R (L.X i) :=
    C.flat_truncLE_X_of_exact_above b (n : ℤ)
      (fun j hj => C.exactAt_of_isLE (n : ℤ) j hj) i
  have hLfinite (i : ℤ) : Module.Finite R (L.homology i) :=
    Module.Finite.equiv (asIso (homologyMap (C.ιTruncLE (n : ℤ)) i)).symm.toLinearEquiv
  exact ⟨P, hPfinite, hPfree, φ, hφ, inferInstance, inferInstance,
    hLflat, hLfinite, inferInstance⟩

end CochainComplex
