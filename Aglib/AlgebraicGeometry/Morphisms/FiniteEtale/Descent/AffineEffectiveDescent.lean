/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Descent.Basic
public import Aglib.RingTheory.Descent.Morphisms
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! Effective finite-etale affine scheme descent from algebra coaction data. -/

@[expose] public section

open _root_.Algebra.Descent (Datum)

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
open TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

universe u
variable (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- The cover associated to an actual finite etale algebra. -/
def specCover [Module.Finite R B] [Algebra.Etale R B] : Scheme.FiniteEtale (Spec (.of R)) :=
  ⟨Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))),
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance),
    (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (RingHom.etale_algebraMap.2 inferInstance)⟩

variable {R S B} (D : Datum R S B)
variable [Module.FaithfullyFlat R S] [Module.Finite S B] [Algebra.Etale S B]

/-- The descended affine cover is Spec of the constructed invariant algebra. -/
def descendedCover : Scheme.FiniteEtale (Spec (.of R)) := by
  have := D.invariants_finite
  have := D.invariants_etale
  exact specCover R D.invariants

/-- The actual pullback of the descended affine scheme is the original Spec. -/
def pullbackIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (descendedCover D).obj.hom ≅
      Spec (.of B) :=
  pullbackSpecIso R S D.invariants ≪≫
    (Scheme.Spec.mapIso D.baseChangeEquiv.toRingEquiv.toCommRingCatIso.op).symm

lemma pullbackIso_hom_base :
    (pullbackIso D).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) (descendedCover D).obj.hom := by
  have h :
      (Scheme.Spec.mapIso D.baseChangeEquiv.toRingEquiv.toCommRingCatIso.op).inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap S B)) =
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] D.invariants))) := by
    change Spec.map (CommRingCat.ofHom D.baseChangeEquiv.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S B)) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact D.baseChangeEquiv.symm.toAlgHom.comp_algebraMap
  change ((pullbackSpecIso R S D.invariants).hom ≫
    (Scheme.Spec.mapIso D.baseChangeEquiv.toRingEquiv.toCommRingCatIso.op).inv) ≫ _ =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R D.invariants)))
  rw [Category.assoc, h]
  exact pullbackSpecIso_hom_fst' R S D.invariants

/-- The isomorphism lies in the actual finite-etale cover category over Spec S. -/
def baseChangeCoverIso :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (descendedCover D) ≅
      specCover S B :=
  ObjectProperty.isoMk _ (Over.isoMk
    (pullbackSymmetry (descendedCover D).obj.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≪≫ pullbackIso D)
    (by
      change ((pullbackSymmetry (descendedCover D).obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom ≫ (pullbackIso D).hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S B)) =
            pullback.snd (descendedCover D).obj.hom
              (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      rw [Category.assoc, pullbackIso_hom_base D]
      exact pullbackSymmetry_hom_comp_fst _ _))

end AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 aa660d7cc8890e95129e6f5e253484c8ac99a242199c223a9244e6037ddf362c.
Definitions, hypotheses and universes are retained modulo native names. -/
