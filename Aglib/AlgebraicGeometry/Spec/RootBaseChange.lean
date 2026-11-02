/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RootBaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The literal root algebra as the original affine base change

The native tensor-spectrum comparison and the existing original root tensor
equivalence identify the actual root algebra with the actual pullback. Both
projections retain the original coefficient and original root maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra.Kummer
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Kummer

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (N : ℕ) (f : R)

attribute [local instance] Algebra.Kummer.rootBaseChangeAlgebra

/-- The original root algebra after coefficient change is the native pullback
along the original root algebra's structural map. -/
def rootBaseChangeSpecIso :
    Spec (.of (RootAlgebra N (algebraMap R B f))) ≅
      pullback (Spec.algebraMap R B) (Spec.algebraMap R (RootAlgebra N f)) :=
  Scheme.Spec.mapIso (rootBaseChangeRightEquiv B N f).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R (RootAlgebra N f) B).symm ≪≫ pullbackSymmetry _ _

/-- The coefficient projection of the root comparison is the original algebra map. -/
@[reassoc (attr := simp)]
theorem rootBaseChangeSpecIso_hom_fst :
    (rootBaseChangeSpecIso R B N f).hom ≫ pullback.fst _ _ =
      Spec.algebraMap B (RootAlgebra N (algebraMap R B f)) := by
  simp only [rootBaseChangeSpecIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (rootBaseChangeRightEquiv B N f).toRingHom) ≫
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  exact (rootBaseChangeRightEquiv_tmul B N f 1 b).trans (by simp)

/-- The fixed-root projection is the original coefficient-change root map. -/
@[reassoc (attr := simp)]
theorem rootBaseChangeSpecIso_hom_snd :
    (rootBaseChangeSpecIso R B N f).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (rootBaseChangeHom B N f).toRingHom) := by
  simp only [rootBaseChangeSpecIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (rootBaseChangeRightEquiv B N f).toRingHom) ≫
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
  rw [← Spec.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.Kummer
