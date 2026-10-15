/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.FiniteProjective.LocalCriterion
public import Aglib.Algebra.Homology.FiniteProjective.Cycles

/-!
# Cancelling a lowest degree detected by the residue field

If a complex over a local ring has no terms below `a`, and its actual
residue-field homology vanishes at `a`, the first differential is a split
injection as soon as its source is finite and its target is finite flat.
The actual truncation `K.truncGE (a + 1)` then gives a quasi-isomorphic complex.
For finite free terms its boundary cokernel and all resulting terms are finite
free. No upper bound or Noetherian hypothesis is needed for this one step.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace CochainComplex

/-- Actual opcycles are finite whenever their displayed term is finite. -/
theorem finite_opcycles {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) [Module.Finite R (K.X n)] :
    Module.Finite R (K.opcycles n) := by
  have : Module.Finite R ((K.sc n).X₂) := by
    change Module.Finite R (K.X n)
    infer_instance
  exact Module.Finite.equiv (K.sc n).moduleCatOpcyclesIso.symm.toLinearEquiv

/-- The native lower truncation preserves finite terms over an arbitrary ring. -/
theorem finite_X_truncGE {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (n i : ℤ)
    [∀ j, Module.Finite R (K.X j)] : Module.Finite R ((K.truncGE n).X i) := by
  rcases lt_trichotomy i n with hi | rfl | hi
  · have : Subsingleton ((K.truncGE n).X i) :=
      ModuleCat.subsingleton_of_isZero ((K.truncGE n).isZero_of_isStrictlyGE n i hi)
    infer_instance
  · have := K.finite_opcycles i
    exact Module.Finite.equiv (K.truncGEXIsoOpcycles i).symm.toLinearEquiv
  · exact Module.Finite.equiv (K.truncGEXIso n i hi).symm.toLinearEquiv

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Vanishing of actual residue-field homology in the lowest degree detects
injectivity of the residue-field first differential. -/
theorem residue_d_injective_of_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology a)) :
    Function.Injective ((K.d a (a + 1)).hom.lTensor (IsLocalRing.ResidueField R)) := by
  let L : CochainComplex (ModuleCat.{max u v} (IsLocalRing.ResidueField R)) ℤ :=
    ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
      (.up ℤ)).obj K
  have : L.IsStrictlyGE a := inferInstance
  have he : (L.sc' (a - 1) a (a + 1)).Exact :=
    (L.exactAt_iff' (a - 1) a (a + 1) (by simp) (by simp)).mp
      ((L.exactAt_iff_isZero_homology a).mpr hfibre)
  have hz : (L.sc' (a - 1) a (a + 1)).f = 0 :=
    (L.isZero_of_isStrictlyGE a (a - 1) (by lia)).eq_of_src _ _
  have hm : Mono (L.d a (a + 1)) := he.mono_g hz
  exact (ModuleCat.mono_iff_injective (L.d a (a + 1))).mp hm

/-- The first differential splits when its residue-field homology vanishes,
its source is finite, and its target is finite flat over the local ring. -/
theorem isSplitMono_d_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    [Module.Finite R (K.X a)] [Module.Finite R (K.X (a + 1))]
    [Module.Flat R (K.X (a + 1))]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology a)) : IsSplitMono (K.d a (a + 1)) := by
  let : Module.Free R (K.X (a + 1)) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective (K.d a (a + 1)).hom).mpr
      (K.residue_d_injective_of_homology_isZero a hfibre)
  exact IsSplitMono.mk'
    { retraction := ModuleCat.ofHom r
      id := ModuleCat.hom_ext hr }

/-- The same residue-field condition makes the original complex exact in its
lowest degree; exactness concerns the actual native homology. -/
theorem exactAt_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    [Module.Finite R (K.X a)] [Module.Finite R (K.X (a + 1))]
    [Module.Flat R (K.X (a + 1))]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology a)) : K.ExactAt a := by
  have := K.isSplitMono_d_of_residue_homology_isZero a hfibre
  apply (K.exactAt_iff' (a - 1) a (a + 1) (by simp) (by simp)).mpr
  apply ((K.sc' (a - 1) a (a + 1)).exact_iff_mono
    ((K.isZero_of_isStrictlyGE a (a - 1) (by lia)).eq_of_src _ _)).mpr
  change Mono (K.d a (a + 1))
  infer_instance

/-- Lowest-degree cancellation raises the actual cohomological lower bound. -/
theorem isGE_succ_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    [Module.Finite R (K.X a)] [Module.Finite R (K.X (a + 1))]
    [Module.Flat R (K.X (a + 1))]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology a)) : K.IsGE (a + 1) := by
  rw [K.isGE_iff]
  intro i hi
  by_cases hia : i < a
  · exact HomologicalComplex.ExactAt.of_isZero (K.isZero_of_isStrictlyGE a i hia)
  · have : i = a := by lia
    subst i
    exact K.exactAt_of_residue_homology_isZero a hfibre

/-- The canonical truncation map is a quasi-isomorphism after cancelling the
lowest degree detected by the residue field. -/
theorem quasiIso_πTruncGE_succ_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    [Module.Finite R (K.X a)] [Module.Finite R (K.X (a + 1))]
    [Module.Flat R (K.X (a + 1))]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology a)) : QuasiIso (K.πTruncGE (a + 1)) := by
  have := K.isGE_succ_of_residue_homology_isZero a hfibre
  infer_instance

/-- The boundary opcycles after cancellation are free over the original local
ring, via the actual cokernel of the first differential. -/
theorem free_opcycles_succ_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    [Module.Finite R (K.X a)] [Module.Finite R (K.X (a + 1))]
    [Module.Flat R (K.X (a + 1))]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology a)) : Module.Free R (K.opcycles (a + 1)) := by
  let : Module.Free R (K.X (a + 1)) := Module.free_of_flat_of_isLocalRing
  have : Module.Free R (K.X (a + 1) ⧸ LinearMap.range (K.d a (a + 1)).hom) :=
    Module.free_of_lTensor_residueField_injective (K.d a (a + 1)).hom _
      (Submodule.mkQ_surjective _) (K.d a (a + 1)).hom.exact_map_mkQ_range
      (K.residue_d_injective_of_homology_isZero a hfibre)
  let e : K.opcycles (a + 1) ≅
      ModuleCat.of R (K.X (a + 1) ⧸ LinearMap.range (K.d a (a + 1)).hom) :=
    K.opcyclesIsoSc' a (a + 1) (a + 2) (by simp) (by simp; omega) ≪≫
      (K.sc' a (a + 1) (a + 2)).moduleCatOpcyclesIso
  exact Module.Free.of_equiv e.symm.toLinearEquiv

/-- Every term of the actual truncation remains free after this cancellation.
Finiteness of its terms is supplied independently by `finite_X_truncGE`. -/
theorem free_X_truncGE_succ_of_residue_homology_isZero
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a i : ℤ) [K.IsStrictlyGE a]
    [∀ j, Module.Finite R (K.X j)] [∀ j, Module.Free R (K.X j)]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology a)) : Module.Free R ((K.truncGE (a + 1)).X i) := by
  rcases lt_trichotomy i (a + 1) with hi | rfl | hi
  · have : Subsingleton ((K.truncGE (a + 1)).X i) :=
      ModuleCat.subsingleton_of_isZero
        ((K.truncGE (a + 1)).isZero_of_isStrictlyGE (a + 1) i hi)
    infer_instance
  · have := K.free_opcycles_succ_of_residue_homology_isZero a hfibre
    exact Module.Free.of_equiv (K.truncGEXIsoOpcycles (a + 1)).symm.toLinearEquiv
  · exact Module.Free.of_equiv (K.truncGEXIso (a + 1) i hi).symm.toLinearEquiv

end CochainComplex
