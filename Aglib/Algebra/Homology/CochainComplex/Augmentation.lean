/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
/-!
# Degree-zero comparison for augmented cochain complexes

In an abelian category, an augmentation from a complex concentrated in degree
zero induces an isomorphism on degree-zero homology when its degree-zero
component is monic and the augmented short complex is exact.

Extraction source: the category-generic SingleZero block of
`R5Lab.AlgebraicGeometry.Curves.Cohomology.CechComparison` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. The statement and proof are retained
under the native `CochainComplex` owner; the original block has no scheme input.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits HomologicalComplex
namespace CochainComplex
universe v
section SingleZero
variable {C : Type v} [Category C] [Abelian C]
variable {B : C} {K : CochainComplex C ℕ}

/-- Exactness and injectivity of an augmentation give its actual degree-zero quasi-isomorphism. -/
theorem quasiIsoAtZero_of_augmentation_exact
    (f : (CochainComplex.single₀ C).obj B ⟶ K)
    (hf : (ShortComplex.mk (f.f 0) (K.d 0 1) (by simp)).Exact)
    [Mono (f.f 0)] : QuasiIsoAt f 0 := by
  let S := (CochainComplex.single₀ C).obj B
  let l : B ⟶ K.cycles 0 := K.liftCycles (f.f 0) 1 (by simp) (by simp)
  have : IsIso l := (CochainComplex.isIso_liftCycles_iff _ _ _).mpr ⟨hf, inferInstance⟩
  have : IsIso (S.iCycles 0) := S.isIso_iCycles 0 1 (by simp) (by simp [S])
  have h : cyclesMap f 0 = S.iCycles 0 ≫ l := by
    apply (cancel_mono (K.iCycles 0)).mp
    simp [l, S]
  have : IsIso (cyclesMap f 0) := by rw [h]; infer_instance
  rw [quasiIsoAt_iff_isIso_homologyMap, ← isIso_comp_left_iff (S.homologyπ 0),
    homologyπ_naturality]
  infer_instance

end SingleZero

end CochainComplex
