/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Resolution
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.BoundedPullback
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Aglib.AlgebraicGeometry.Modules.Flat.Closure


/-!
# Actual bounded-above flat replacements of module sheaves

The flat chain resolution extends along `n ↦ -n` to the actual integer-indexed
cochain category. The augmentation is proved to be
a quasi-isomorphism. Arbitrary geometric pullback can be applied to these genuine flat
representatives for single sheaves.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/FlatCochainResolution.lean`.
SHA-256: `9cfb49d5e5dae48f3aa71d7aa8e3708e0668b89a6e9a37eaee9a402da4e85dad`.
Selected source lines: 1–114.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual flat resolution reindexed in nonpositive cochain degrees. -/
def flatCochainResolution (X : Scheme.{u}) : X.Modules ⥤ CochainComplex X.Modules ℤ :=
  flatResolution X ⋙ ComplexShape.embeddingDownNat.extendFunctor X.Modules

/-- Every term of the actual cochain replacement has flat module stalks. -/
theorem flatCochainResolution_term_flat (X : Scheme.{u}) (M : X.Modules) (n : ℤ) :
    stalkwiseFlat X (((flatCochainResolution X).obj M).X n) := by
  classical
  by_cases h : ∃ i : ℕ, ComplexShape.embeddingDownNat.f i = n
  · obtain ⟨i, hi⟩ := h
    exact (stalkwiseFlat X).prop_of_iso
      (((flatResolution X).obj M).extendXIso ComplexShape.embeddingDownNat hi).symm
      (flatResolution_term_flat X M i)
  · exact stalkwiseFlat_of_isZero _
      (((flatResolution X).obj M).isZero_extend_X _ n (by simpa using h))

/-- The genuine replacement is strictly zero above degree zero. -/
theorem flatCochainResolution_isZero_above (X : Scheme.{u}) (M : X.Modules)
    (n : ℤ) (hn : 0 < n) : IsZero (((flatCochainResolution X).obj M).X n) :=
  ((flatResolution X).obj M).isZero_extend_X _ n (by
    intro i
    simp only [ComplexShape.embeddingDownNat_f]
    omega)

/-- The actual augmentation to the sheaf placed in cochain degree zero. -/
def flatCochainResolutionπ (X : Scheme.{u}) (M : X.Modules) :
    (flatCochainResolution X).obj M ⟶ (HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
      0).obj M :=
  HomologicalComplex.extendMap (flatResolutionToSingle X M) ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat M 0 0 (by simp)).hom

instance flatCochainResolutionπ_quasiIso (X : Scheme.{u}) (M : X.Modules) :
    QuasiIso (flatCochainResolutionπ X M) := by
  unfold flatCochainResolutionπ
  infer_instance

/-- Every actual module sheaf has a bounded-above, stalkwise-flat cochain resolution. -/
theorem exists_boundedAbove_flat_resolution (X : Scheme.{u}) (M : X.Modules) :
    ∃ (P : CochainComplex X.Modules ℤ)
      (p : P ⟶ (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M),
      (∀ n, stalkwiseFlat X (P.X n)) ∧ (∀ n, 0 < n → IsZero (P.X n)) ∧ QuasiIso p :=
  ⟨(flatCochainResolution X).obj M, flatCochainResolutionπ X M,
    flatCochainResolution_term_flat X M, flatCochainResolution_isZero_above X M, inferInstance⟩

/-- Placing a flat module sheaf in degree zero gives an actual degreewise-flat complex. -/
theorem single_stalkwiseFlat (X : Scheme.{u}) (M : X.Modules) (hM : stalkwiseFlat X M)
    (n : ℤ) : stalkwiseFlat X
      (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M).X n) := by
  by_cases hn : n = 0
  · subst n
    exact (stalkwiseFlat X).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm hM
  · exact stalkwiseFlat_of_isZero _
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- As an end-to-end resolution consumer, a flat sheaf's actual flat-resolution
augmentation remains a quasi-isomorphism under every geometric pullback. -/
theorem quasiIso_pullback_flatCochainResolutionπ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (hM : stalkwiseFlat Y M) :
    QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map (flatCochainResolutionπ Y
      M)) :=
  quasiIso_pullback_of_boundedAbove_stalkwiseFlat f
    (flatCochainResolution_term_flat Y M) (single_stalkwiseFlat Y M hM) 0 0
    (flatCochainResolution_isZero_above Y M)
    (fun n hn => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
    (flatCochainResolutionπ Y M)

end AlgebraicGeometry.Scheme.Modules
