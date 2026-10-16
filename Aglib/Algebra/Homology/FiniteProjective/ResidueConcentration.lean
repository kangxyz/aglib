/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.FiniteProjective.BaseChange
public import Aglib.Algebra.Homology.FiniteProjective.UpperCancellation

/-!
# Bounded cancellation from residue-field homology

The actual lower and upper truncation maps successively remove the nonzero
negative and positive term ranges of a bounded finite free complex over a local
ring when its residue-field homology vanishes there. Every cancellation is a
quasi-isomorphism between bounded-above projective complexes, hence an actual
homotopy equivalence. Mapping that equivalence transports the residue-field
homology without assuming that the residue-field ring map is flat.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Negative residue-field homology vanishing removes the negative term range
through native truncation maps and actual homotopy equivalences. -/
theorem exists_homotopyEquiv_isStrictlyGE_zero_of_residue_homology_neg
    (m : ℕ) (b : ℤ) (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [K.IsStrictlyGE (-(m : ℤ))] [K.IsStrictlyLE b]
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Free R (K.X i)]
    (hfibre : ∀ i : ℤ, i < 0 → IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology i)) :
    ∃ L : CochainComplex (ModuleCat.{max u v} R) ℤ,
      L.IsStrictlyGE 0 ∧ L.IsStrictlyLE b ∧
        (∀ i, Module.Finite R (L.X i)) ∧ (∀ i, Module.Free R (L.X i)) ∧
          Nonempty (HomotopyEquiv K L) := by
  induction m generalizing K with
  | zero =>
    have hge := (inferInstance : K.IsStrictlyGE (-((0 : ℕ) : ℤ)))
    have hz : -((0 : ℕ) : ℤ) = 0 := by decide
    rw [hz] at hge
    exact ⟨K, hge, inferInstance, fun _ => inferInstance,
      fun _ => inferInstance, ⟨HomotopyEquiv.refl K⟩⟩
  | succ m ih =>
    let a : ℤ := -((m + 1 : ℕ) : ℤ)
    have : K.IsStrictlyGE a := by change K.IsStrictlyGE (-((m + 1 : ℕ) : ℤ)); infer_instance
    have ha : a < 0 := by dsimp [a]; omega
    have hcut : a + 1 = -(m : ℤ) := by dsimp [a]; omega
    let L : CochainComplex (ModuleCat.{max u v} R) ℤ := K.truncGE (a + 1)
    have : L.IsStrictlyGE (-(m : ℤ)) := by rw [← hcut]; infer_instance
    have : L.IsStrictlyLE b := inferInstance
    have (i : ℤ) : Module.Finite R (L.X i) := K.finite_X_truncGE (a + 1) i
    have (i : ℤ) : Module.Free R (L.X i) :=
      K.free_X_truncGE_succ_of_residue_homology_isZero a i (hfibre a ha)
    let q : K ⟶ L := K.πTruncGE (a + 1)
    have : QuasiIso q := K.quasiIso_πTruncGE_succ_of_residue_homology_isZero a (hfibre a ha)
    have (i : ℤ) : Projective (K.X i) := inferInstance
    have (i : ℤ) : Projective (L.X i) := inferInstance
    have : K.IsKProjective := isKProjective_of_projective K b
    have : L.IsKProjective := isKProjective_of_projective L b
    obtain ⟨e, _⟩ := (IsKProjective.quasiIso_iff q).mp inferInstance
    let F := ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))
    have hL : ∀ i : ℤ, i < 0 → IsZero
        (((F.mapHomologicalComplex (.up ℤ)).obj L).homology i) := by
      intro i hi
      exact IsZero.of_iso (hfibre i hi) ((F.mapHomotopyEquiv e).toHomologyIso i).symm
    obtain ⟨L', hge, hle, hfinite, hfree, ⟨e'⟩⟩ := ih L hL
    exact ⟨L', hge, hle, hfinite, hfree, ⟨e.trans e'⟩⟩

/-- Positive residue-field homology vanishing removes the positive term range
by the actual upper truncation inclusions and homotopy equivalences. -/
theorem exists_homotopyEquiv_isStrictlyLE_zero_of_residue_homology_pos
    (n : ℕ) (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [K.IsStrictlyGE 0] [K.IsStrictlyLE (n : ℤ)]
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Free R (K.X i)]
    (hfibre : ∀ i : ℤ, 0 < i → IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology i)) :
    ∃ L : CochainComplex (ModuleCat.{max u v} R) ℤ,
      L.IsStrictlyGE 0 ∧ L.IsStrictlyLE 0 ∧
        (∀ i, Module.Finite R (L.X i)) ∧ (∀ i, Module.Free R (L.X i)) ∧
          Nonempty (HomotopyEquiv K L) := by
  induction n generalizing K with
  | zero => exact ⟨K, inferInstance, inferInstance, fun _ => inferInstance,
      fun _ => inferInstance, ⟨HomotopyEquiv.refl K⟩⟩
  | succ n ih =>
    let b : ℤ := ((n + 1 : ℕ) : ℤ)
    have : K.IsStrictlyLE b := by change K.IsStrictlyLE ((n + 1 : ℕ) : ℤ); infer_instance
    have hb : 0 < b := by dsimp [b]; omega
    have hcut : b - 1 = (n : ℤ) := by dsimp [b]; omega
    let L : CochainComplex (ModuleCat.{max u v} R) ℤ := K.truncLE (b - 1)
    have : L.IsStrictlyGE 0 := inferInstance
    have : L.IsStrictlyLE (n : ℤ) := by rw [← hcut]; infer_instance
    have : L.IsStrictlyLE b := inferInstance
    have (i : ℤ) : Module.Finite R (L.X i) :=
      K.finite_X_truncLE_pred_of_residue_homology_isZero b i (hfibre b hb)
    have (i : ℤ) : Module.Free R (L.X i) :=
      K.free_X_truncLE_pred_of_residue_homology_isZero b i (hfibre b hb)
    let q : L ⟶ K := K.ιTruncLE (b - 1)
    have : QuasiIso q := K.quasiIso_ιTruncLE_pred_of_residue_homology_isZero b (hfibre b hb)
    have (i : ℤ) : Projective (K.X i) := inferInstance
    have (i : ℤ) : Projective (L.X i) := inferInstance
    have : K.IsKProjective := isKProjective_of_projective K b
    have : L.IsKProjective := isKProjective_of_projective L b
    obtain ⟨e₀, _⟩ := (IsKProjective.quasiIso_iff q).mp inferInstance
    let e := e₀.symm
    let F := ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))
    have hL : ∀ i : ℤ, 0 < i → IsZero
        (((F.mapHomologicalComplex (.up ℤ)).obj L).homology i) := by
      intro i hi
      exact IsZero.of_iso (hfibre i hi) ((F.mapHomotopyEquiv e).toHomologyIso i).symm
    obtain ⟨L', hge, hle, hfinite, hfree, ⟨e'⟩⟩ := ih L hL
    exact ⟨L', hge, hle, hfinite, hfree, ⟨e.trans e'⟩⟩

end CochainComplex
