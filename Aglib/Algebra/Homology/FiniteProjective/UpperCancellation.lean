/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.FiniteProjective.Cancellation

/-!
# Cancelling a highest degree detected by the residue field

The canonical base-change map in a strict highest degree is invertible for every
ring map. If that term is finite over a local ring, Nakayama therefore detects
vanishing of its actual homology from the actual residue-field homology.
The native upper truncation removes this degree by a quasi-isomorphism. For
finite free terms its boundary cycles and all resulting terms stay finite free.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Nakayama detects actual homology in the highest degree through the original
canonical scalar-extension comparison. Only the highest term must be finite. -/
theorem isZero_homology_of_residue_homology_isZero_of_isStrictlyLE
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    [Module.Finite R (K.X b)]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology b)) : IsZero (K.homology b) := by
  have : Module.Finite R ((K.sc b).X₂) := by
    change Module.Finite R (K.X b)
    infer_instance
  have : Module.Finite R (K.homology b) :=
    (K.sc b).moduleCat_finite_homology_of_g_eq_zero
      ((K.isZero_of_isStrictlyLE b _ (by simp)).eq_of_tgt _ _)
  let φ := algebraMap R (IsLocalRing.ResidueField R)
  have : IsIso (extendScalarsHomologyMap φ K b) :=
    extendScalarsHomologyMap_isIso_of_isStrictlyLE φ K b
  have hz : IsZero ((ModuleCat.extendScalars φ).obj (K.homology b)) :=
    IsZero.of_iso hfibre (asIso (extendScalarsHomologyMap φ K b))
  have : Subsingleton ((IsLocalRing.ResidueField R) ⊗[R] (K.homology b)) :=
    ModuleCat.subsingleton_of_isZero hz
  have : Subsingleton (K.homology b) :=
    (IsLocalRing.subsingleton_tensorProduct (R := R) (M := K.homology b)).mp inferInstance
  exact ModuleCat.isZero_of_subsingleton _

/-- Highest-degree cancellation lowers the actual cohomological upper bound. -/
theorem isLE_pred_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    [Module.Finite R (K.X b)]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology b)) : K.IsLE (b - 1) := by
  rw [K.isLE_iff]
  intro i hi
  by_cases hib : i = b
  · subst i
    exact (K.exactAt_iff_isZero_homology b).mpr
      (K.isZero_homology_of_residue_homology_isZero_of_isStrictlyLE b hfibre)
  · exact HomologicalComplex.ExactAt.of_isZero
      (K.isZero_of_isStrictlyLE b i (by lia))

/-- The canonical upper-truncation inclusion is a quasi-isomorphism after
cancelling a highest degree detected by the residue field. -/
theorem quasiIso_ιTruncLE_pred_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    [Module.Finite R (K.X b)]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology b)) : QuasiIso (K.ιTruncLE (b - 1)) := by
  have := K.isLE_pred_of_residue_homology_isZero b hfibre
  infer_instance

/-- The boundary cycles after this cancellation are finite projective, hence
free over the original local ring. -/
theorem free_cycles_pred_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Free R (K.X i)]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology b)) : Module.Free R (K.cycles (b - 1)) := by
  have (i : ℤ) : Module.Projective R (K.X i) := inferInstance
  have (i : ℤ) : Projective (K.X i) := inferInstance
  have := K.isLE_pred_of_residue_homology_isZero b hfibre
  have : Module.Finite R (K.cycles (b - 1)) :=
    K.finite_cycles_of_exact_above b (b - 1) (fun i hi => K.exactAt_of_isLE (b - 1) i hi)
  have : Projective (K.cycles (b - 1)) :=
    K.projective_cycles_of_exact_above b (b - 1) (fun i hi => K.exactAt_of_isLE (b - 1) i hi)
  have : Module.Projective R (K.cycles (b - 1)) := inferInstance
  exact Module.free_of_flat_of_isLocalRing

/-- Every term of the actual upper truncation is finite after this cancellation. -/
theorem finite_X_truncLE_pred_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (b i : ℤ) [K.IsStrictlyLE b]
    [∀ j, Module.Finite R (K.X j)] [∀ j, Module.Free R (K.X j)]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology b)) : Module.Finite R ((K.truncLE (b - 1)).X i) := by
  rcases lt_trichotomy i (b - 1) with hi | rfl | hi
  · exact Module.Finite.equiv (K.truncLEXIso (b - 1) i hi).symm.toLinearEquiv
  · have (j : ℤ) : Module.Projective R (K.X j) := inferInstance
    have := K.isLE_pred_of_residue_homology_isZero b hfibre
    have : Module.Finite R (K.cycles (b - 1)) :=
      K.finite_cycles_of_exact_above b (b - 1) (fun j hj => K.exactAt_of_isLE (b - 1) j hj)
    exact Module.Finite.equiv (K.truncLEXIsoCycles (b - 1)).symm.toLinearEquiv
  · have : Subsingleton ((K.truncLE (b - 1)).X i) :=
      ModuleCat.subsingleton_of_isZero
        ((K.truncLE (b - 1)).isZero_of_isStrictlyLE (b - 1) i hi)
    infer_instance

/-- Every term of the actual upper truncation stays free after this cancellation. -/
theorem free_X_truncLE_pred_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (b i : ℤ) [K.IsStrictlyLE b]
    [∀ j, Module.Finite R (K.X j)] [∀ j, Module.Free R (K.X j)]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology b)) : Module.Free R ((K.truncLE (b - 1)).X i) := by
  rcases lt_trichotomy i (b - 1) with hi | rfl | hi
  · exact Module.Free.of_equiv (K.truncLEXIso (b - 1) i hi).symm.toLinearEquiv
  · have := K.free_cycles_pred_of_residue_homology_isZero b hfibre
    exact Module.Free.of_equiv (K.truncLEXIsoCycles (b - 1)).symm.toLinearEquiv
  · have : Subsingleton ((K.truncLE (b - 1)).X i) :=
      ModuleCat.subsingleton_of_isZero
        ((K.truncLE (b - 1)).isZero_of_isStrictlyLE (b - 1) i hi)
    infer_instance

end CochainComplex
