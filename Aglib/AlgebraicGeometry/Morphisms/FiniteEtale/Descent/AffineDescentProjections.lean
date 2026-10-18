/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineEffectiveDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Aglib.RingTheory.Descent.Basic

/-! The second projection of effective affine descent is the literal
invariant-algebra inclusion; it is surjective, and etale when the base change is. -/

@[expose] public section

open _root_.Algebra.Descent (Datum)

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
variable [Module.FaithfullyFlat R S] [Module.Finite S B] [Algebra.Etale S B]
variable (D : Datum R S B)

lemma pullbackIso_inv_second :
    (pullbackIso D).inv ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (descendedCover D).obj.hom =
        Spec.map (CommRingCat.ofHom D.invariants.val.toRingHom) := by
  change ((Scheme.Spec.mapIso D.baseChangeEquiv.toRingEquiv.toCommRingCatIso.op).hom ≫
    (pullbackSpecIso R S D.invariants).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom D.baseChangeEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : D.invariants →ₐ[R] S ⊗[R] D.invariants).toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change D.baseChangeEquiv (1 ⊗ₜ[R] a) = (a : B)
  simp

theorem invariantInclusion_surjective :
    Surjective (Spec.map (CommRingCat.ofHom D.invariants.val.toRingHom)) := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    ((flat_and_surjective_SpecMap_iff _).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance)).2
  rw [← pullbackIso_inv_second D]
  infer_instance

theorem invariantInclusion_etale [Algebra.Etale R S] :
    Etale (Spec.map (CommRingCat.ofHom D.invariants.val.toRingHom)) := by
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 inferInstance)
  rw [← pullbackIso_inv_second D]
  infer_instance

end AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 692b5736085f0584cd2d861ad61bd45572696a54637dc65dc6dd434d82acf76c.
Definitions, hypotheses and universes are retained modulo native names. -/
