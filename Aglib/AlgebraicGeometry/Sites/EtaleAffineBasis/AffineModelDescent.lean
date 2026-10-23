/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Descent.Etale
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Actual affine etale models at a filtered stage

An affine etale object over the spectrum of a ring colimit has an affine etale
model at an actual stage. Its comparison is an isomorphism in the original
over category from the literal scheme pullback, so the structural triangle
is part of the comparison itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

/-- Every affine etale object over a filtered ring colimit descends to an actual
stage, with its original over-category base-change comparison. -/
theorem exists_affine_etale_model_of_isColimit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (Y : Over (Spec c.pt)) [IsAffine Y.left] [Etale Y.hom] :
    ∃ (i : I) (Yᵢ : Over (Spec (F.obj i))),
      IsAffine Yᵢ.left ∧ Etale Yᵢ.hom ∧
      Nonempty ((Over.pullback (Spec.map (c.ι.app i))).obj Yᵢ ≅ Y) := by
  obtain ⟨A, ⟨eA⟩⟩ := (essImage_algSpec (R := c.pt) (G := Y)).2 inferInstance
  have : IsIso eA.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec c.pt)).map eA.hom))
  have het : Etale ((algSpec c.pt).obj A).hom := by
    rw [← Over.w eA.hom]
    exact Etale.etale_comp eA.hom.left Y.hom
  let : Algebra.Etale c.pt A.unop :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 het)
  obtain ⟨i, B, _, _, hB, ⟨e⟩⟩ := Algebra.Etale.exists_model_of_isColimit F c hc A.unop
  let : Algebra.Etale (F.obj i) B := hB
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  let Yᵢ : Over (Spec (F.obj i)) := Over.mk (Spec.algebraMap (F.obj i) B)
  let eTensor : (Over.pullback (Spec.map (c.ι.app i))).obj Yᵢ ≅
      Over.mk (Spec.algebraMap c.pt (c.pt ⊗[F.obj i] B)) :=
    Over.isoMk
      (pullbackSymmetry (Spec.algebraMap (F.obj i) B)
        (Spec.algebraMap (F.obj i) c.pt) ≪≫ pullbackSpecIso (F.obj i) c.pt B)
      (by
        change (_ ≫ _) ≫ Spec.algebraMap c.pt (c.pt ⊗[F.obj i] B) = _
        rw [Category.assoc, pullbackSpecIso_hom_fst']
        exact pullbackSymmetry_hom_comp_fst _ _)
  let eAlg : Over.mk (Spec.algebraMap c.pt (c.pt ⊗[F.obj i] B)) ≅
      (algSpec c.pt).obj A :=
    Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).symm (by
      change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap c.pt A.unop)) =
          Spec.map (CommRingCat.ofHom (algebraMap c.pt (c.pt ⊗[F.obj i] B)))
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext e.symm.toAlgHom.comp_algebraMap))
  refine ⟨i, Yᵢ, ?_, ?_, ⟨eTensor ≪≫ eAlg ≪≫ eA⟩⟩
  · exact inferInstanceAs (IsAffine (Spec (.of B)))
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (RingHom.etale_algebraMap.2 hB)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
