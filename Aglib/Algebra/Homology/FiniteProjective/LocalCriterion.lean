/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.FiniteProjective.HomologyBaseChange
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A two-term local criterion from residue-field homology

For a complex supported in degrees `-1, 0` over a local ring, vanishing of the
actual residue-field homology in degree `-1` makes the degree-zero homology free,
provided the degree `-1` term is finite and the degree-zero term is finite flat.
The homology remains the native `HomologicalComplex.homology`, and the canonical
map after every ring base change is the original adjunction-unit comparison.

No Noetherian hypothesis is used. This is the two-term algebraic criterion; it
does not construct a two-term model for the cohomology of a proper scheme.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u v w

namespace CategoryTheory.ShortComplex

/-- A rightmost homology module is finite whenever its middle term is finite. -/
theorem moduleCat_finite_homology_of_g_eq_zero {R : Type u} [Ring R]
    (T : ShortComplex (ModuleCat.{v} R)) [Module.Finite R T.X₂] (hg : T.g = 0) :
    Module.Finite R T.homology :=
  Module.Finite.equiv (T.asIsoHomologyι hg ≪≫ T.moduleCatOpcyclesIso).symm.toLinearEquiv

/-- A finite presentation over a local ring has free cokernel when its target
is finite flat and its residue-field first arrow is injective. This statement
uses the actual rightmost homology of the short complex. -/
theorem moduleCat_free_homology_of_residue_injective {R : Type u} [CommRing R]
    [IsLocalRing R] (T : ShortComplex (ModuleCat.{v} R))
    [Module.Finite R T.X₁] [Module.Finite R T.X₂] [Module.Flat R T.X₂]
    (hg : T.g = 0)
    (hf : Function.Injective (T.f.hom.lTensor (IsLocalRing.ResidueField R))) :
    Module.Free R T.homology := by
  let : Module.Free R T.X₂ := Module.free_of_flat_of_isLocalRing
  have : Module.Free R (T.X₂ ⧸ LinearMap.range T.f.hom) :=
    Module.free_of_lTensor_residueField_injective T.f.hom _
      (Submodule.mkQ_surjective _) T.f.hom.exact_map_mkQ_range hf
  exact Module.Free.of_equiv
    (T.asIsoHomologyι hg ≪≫ T.moduleCatOpcyclesIso).symm.toLinearEquiv

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [CommRing R] [IsLocalRing R] {ι : Type*} {c : ComplexShape ι}

/-- The local residue-injectivity criterion concerns actual complex homology. -/
theorem free_homology_of_residue_injective
    (K : HomologicalComplex (ModuleCat.{v} R) c) (n : ι)
    [Module.Finite R (K.X (c.prev n))] [Module.Finite R (K.X n)] [Module.Flat R (K.X n)]
    (hg : K.d n (c.next n) = 0)
    (hf : Function.Injective ((K.d (c.prev n) n).hom.lTensor (IsLocalRing.ResidueField R))) :
    Module.Free R (K.homology n) := by
  have : Module.Finite R ((K.sc n).X₁) := by
    change Module.Finite R (K.X (c.prev n))
    infer_instance
  have : Module.Finite R ((K.sc n).X₂) := by
    change Module.Finite R (K.X n)
    infer_instance
  have : Module.Flat R ((K.sc n).X₂) := by
    change Module.Flat R (K.X n)
    infer_instance
  exact (K.sc n).moduleCat_free_homology_of_residue_injective hg hf

end HomologicalComplex

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- A strict upper term bound gives arbitrary canonical base change in that
rightmost degree of the actual complex. -/
theorem extendScalarsHomologyMap_isIso_of_isStrictlyLE
    {S : Type w} [CommRing S] (φ : R →+* S)
    (K : CochainComplex (ModuleCat.{max v w} R) ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    IsIso (extendScalarsHomologyMap φ K n) := by
  apply extendScalarsHomologyMap_isIso_of_d_eq_zero
  exact (K.isZero_of_isStrictlyLE n _ (by simp)).eq_of_tgt _ _

/-- The actual degree-zero homology of a complex with no positive terms is
finite when its degree-zero term is finite. -/
theorem finite_homology_zero_of_isStrictlyLE
    (K : CochainComplex (ModuleCat.{v} R) ℤ) [K.IsStrictlyLE 0]
    [Module.Finite R (K.X 0)] : Module.Finite R (K.homology 0) := by
  have : Module.Finite R ((K.sc 0).X₂) := by
    change Module.Finite R (K.X 0)
    infer_instance
  apply (K.sc 0).moduleCat_finite_homology_of_g_eq_zero
  exact (K.isZero_of_isStrictlyLE 0 _ (by simp)).eq_of_tgt _ _

/-- For a complex supported in degrees `-1, 0` over a local ring, vanishing
of its actual residue-field homology in degree `-1` makes its degree-zero
homology free. The two terms need only be finite and finite flat respectively. -/
theorem free_homology_zero_of_residue_homology_neg_one_isZero [IsLocalRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Finite R (K.X 0)] [Module.Flat R (K.X 0)]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology (-1))) : Module.Free R (K.homology 0) := by
  let L : CochainComplex (ModuleCat.{max u v} (IsLocalRing.ResidueField R)) ℤ :=
    ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
      (.up ℤ)).obj K
  have hL : L.IsStrictlyGE (-1) := inferInstance
  have he : L.ExactAt (-1) := (L.exactAt_iff_isZero_homology (-1)).mpr hfibre
  have hz : (L.sc (-1)).f = 0 :=
    (L.isZero_of_isStrictlyGE (-1) _ (by simp)).eq_of_src _ _
  have hm : Mono (L.sc (-1)).g := he.mono_g hz
  change Mono (L.d (-1) ((ComplexShape.up ℤ).next (-1))) at hm
  have hn : (ComplexShape.up ℤ).next (-1) = 0 := by simp
  rw [hn] at hm
  have hi : Function.Injective ((K.d (-1) 0).hom.lTensor (IsLocalRing.ResidueField R)) :=
    (ModuleCat.mono_iff_injective (L.d (-1) 0)).mp hm
  have hp0 : (ComplexShape.up ℤ).prev 0 = (-1) := by simp
  have hp : Module.Finite R (K.X ((ComplexShape.up ℤ).prev 0)) := by
    rw [hp0]
    infer_instance
  apply K.free_homology_of_residue_injective 0
  · exact (K.isZero_of_isStrictlyLE 0 _ (by simp)).eq_of_tgt _ _
  · rw [hp0]
    exact hi

/-- The finite free degree-zero homology has exactly the rank of its actual
residue-field degree-zero homology, through the canonical base-change map. -/
theorem finrank_homology_zero_eq_residue_homology_zero [IsLocalRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Finite R (K.X 0)] [Module.Flat R (K.X 0)]
    (hfibre : IsZero
      ((((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj K).homology (-1))) :
    Module.finrank R (K.homology 0) =
      Module.finrank (IsLocalRing.ResidueField R)
        ((((ModuleCat.extendScalars (algebraMap R
          (IsLocalRing.ResidueField R))).mapHomologicalComplex (.up ℤ)).obj K).homology 0) := by
  have : Module.Free R (K.homology 0) :=
    K.free_homology_zero_of_residue_homology_neg_one_isZero hfibre
  let φ := algebraMap R (IsLocalRing.ResidueField R)
  have : IsIso (extendScalarsHomologyMap φ K 0) :=
    extendScalarsHomologyMap_isIso_of_isStrictlyLE φ K 0
  let e := (asIso (extendScalarsHomologyMap φ K 0)).toLinearEquiv
  calc
    Module.finrank R (K.homology 0) =
        Module.finrank (IsLocalRing.ResidueField R)
          ((ModuleCat.extendScalars φ).obj (K.homology 0)) := by
      symm
      change Module.finrank (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] (K.homology 0)) = _
      exact Module.finrank_baseChange
    _ = _ := e.finrank_eq

end CochainComplex
