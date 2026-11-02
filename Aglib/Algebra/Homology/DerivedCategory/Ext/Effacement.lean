/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
/-
The homology calculation for the extreme component adapts the argument in
Mathlib/Algebra/Homology/DerivedCategory/Ext/EnoughProjectives.lean.
Copyright (c) 2025 Joël Riou. All rights reserved.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Classwise epimorphic effacement of the original Ext groups

A positive class is killed by an actual epimorphism to its original source.
The proof uses a native right fraction and its smart truncation. The extreme
component of the quasi-isomorphism is epi, and the single-complex map from
that component kills the positive target. No enough-projectives or
enough-injectives assumption, resolution choice, or derived model is public.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Abelian HomologicalComplex

universe u v w w'

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem epi_component_to_single_of_quasiIsoAt
    {X : C} {K : CochainComplex C ℤ} {i : ℤ}
    (π : K ⟶ (CochainComplex.singleFunctor C i).obj X)
    [K.IsStrictlyLE i] [QuasiIsoAt π i] : Epi (π.f i) := by
  let e := K.iCyclesIso i (i + 1) (by simp)
    ((K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt _ _)
  let α := e.inv ≫ K.homologyπ i ≫ homologyMap π i ≫ (singleObjHomologySelfIso _ _ _).hom
  have hπ : π.f i = α ≫ (singleObjXSelf (ComplexShape.up ℤ) i X).inv := by
    rw [← cancel_epi e.hom]
    dsimp [α, e]
    rw [assoc, assoc, assoc, iCyclesIso_hom_inv_id_assoc,
      homologyπ_naturality_assoc]
    dsimp [singleFunctor, singleFunctors]
    rw [homologyπ_singleObjHomologySelfIso_hom_assoc,
      ← singleObjCyclesSelfIso_inv_iCycles, Iso.hom_inv_id_assoc, ← cyclesMap_i]
  have : Epi α := by dsimp [α]; infer_instance
  rw [hπ]
  infer_instance

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]

private theorem exists_epi_comp_eq_zero_to_lower_complex {X : C}
    {L : CochainComplex C ℤ} {i : ℤ}
    (φ : Q.obj ((CochainComplex.singleFunctor C i).obj X) ⟶ Q.obj L)
    (n : ℤ) (hn : n < i) [L.IsStrictlyLE n] :
    ∃ (M : C) (f : M ⟶ X), Epi f ∧ (singleFunctor C i).map f ≫ φ = 0 := by
  obtain ⟨K, _, π, hπ, g, rfl⟩ := right_fac_of_isStrictlyLE φ i
  have : QuasiIso π := by rwa [← isIso_Q_map_iff_quasiIso]
  have : Epi (π.f i) := CochainComplex.epi_component_to_single_of_quasiIsoAt π
  let f : K.X i ⟶ X := π.f i ≫ (singleObjXSelf (ComplexShape.up ℤ) i X).hom
  have : Epi f := by dsimp [f]; infer_instance
  let j : (CochainComplex.singleFunctor C i).obj (K.X i) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (𝟙 _) (by
      rintro _ rfl
      apply (K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt)
  have hjπ : j ≫ π = (CochainComplex.singleFunctor C i).map f := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, j, HomologicalComplex.mkHomFromSingle_f,
      comp_id]
    rw [HomologicalComplex.single_map_f_self]
    simp [f]
  have hjg : j ≫ g = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    apply (L.isZero_of_isStrictlyLE n i hn).eq_of_tgt
  refine ⟨K.X i, f, inferInstance, ?_⟩
  change Q.map ((CochainComplex.singleFunctor C i).map f) ≫
    (inv (Q.map π) ≫ Q.map g) = 0
  rw [← hjπ, Q.map_comp, assoc, IsIso.hom_inv_id_assoc, ← Q.map_comp, hjg, Q.map_zero]

end DerivedCategory

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Every individual positive original Ext class is killed by an actual
epimorphism to its source. The epimorphism may depend on the class; no
projective or injective supply is assumed. -/
theorem exists_epi_mk₀_comp_eq_zero {X Y : C} {n : ℕ} (x : Ext.{w} X Y (n + 1)) :
    ∃ (M : C) (f : M ⟶ X), Epi f ∧ (mk₀ f).comp x (zero_add (n + 1)) = 0 := by
  let := HasDerivedCategory.standard C
  let e := ((DerivedCategory.singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).app Y
  obtain ⟨M, f, hf, hzero⟩ :=
    DerivedCategory.exists_epi_comp_eq_zero_to_lower_complex (x.hom ≫ e.hom)
      (-(n + 1)) (by lia)
  refine ⟨M, f, hf, ?_⟩
  apply Ext.ext
  rw [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp, zero_hom]
  apply (cancel_mono e.hom).mp
  simpa only [assoc, Limits.zero_comp] using hzero

end CategoryTheory.Abelian.Ext
