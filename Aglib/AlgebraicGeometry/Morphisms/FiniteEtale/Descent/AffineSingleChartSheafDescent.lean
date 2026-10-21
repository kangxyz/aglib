/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineSheafSectionCompatibility
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineDescentProjections
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.EtaleSectionDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.EtaleRestrictionConservative
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedTorsor
public import Aglib.RingTheory.Descent.Basic

/-! Descend the actual local identity section to the constructed affine cover. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite
open TensorProduct
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (forget toEtale)

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.AffineSheafAlgebraDatum

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
variable [Module.FaithfullyFlat R S]
variable (F : Scheme.EtaleCohomology.SetSheaf (Spec (.of R))) (B : Type u)
variable [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
variable [Module.Finite S B] [Algebra.Etale S B]
variable (e : Scheme.EtaleCohomology.finiteRepresentedSetSheaf (AffineDescent.specCover S B) ≅
  (Scheme.EtaleCohomology.setEtaleRestriction (chart R S)).obj F)

local notation "D" => datum F B e
local notation "A" => _root_.Algebra.Descent.Datum.invariants (datum F B e)

local instance relation_etale : Algebra.Etale S (B ⊗[A] B) := by
  have : Algebra.Etale R A := (D).invariants_etale
  have : Algebra.Etale R B := Algebra.Etale.comp R S B
  have : Algebra.Etale A B := Algebra.Etale.of_restrictScalars R A B
  exact Algebra.Etale.comp S B (B ⊗[A] B)

/-- The left tensor inclusion into `B ⊗[A] B`, as an `S`-algebra homomorphism. -/
def relationLeft : B →ₐ[S] B ⊗[A] B := Algebra.TensorProduct.includeLeft

/-- The right tensor inclusion into `B ⊗[A] B`, restricted to an `R`-algebra homomorphism. -/
def relationRight : B →ₐ[R] B ⊗[A] B :=
  (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).restrictScalars R

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
lemma relation_agree (a : A) : relationRight F B e a = relationLeft F B e a := by
  change (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (algebraMap A B a) =
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) (algebraMap A B a)
  simp only [AlgHom.commutes]

lemma identitySection_relation :
    map (S := S) F (relationRight F B e) (identitySection F B e) =
      map (S := S) F ((relationLeft F B e).restrictScalars R) (identitySection F B e) :=
  identitySection_invariant F B e (relationRight F B e) (relationLeft F B e)
    (relation_agree F B e)

/-- The literal inclusion of invariants gives a morphism on the small site. -/
def inclusionSite :
    (Scheme.EtaleCohomology.siteEtalePostcompose (chart R S)).obj (test S B) ⟶
      (toEtale (Spec (.of R))).obj (AffineDescent.descendedCover D) :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (A).val.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom (A).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫ chart R S
    simp only [chart, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    change (A).val.toRingHom.comp (algebraMap R A) =
      (algebraMap S B).comp (algebraMap R S)
    rw [← IsScalarTower.algebraMap_eq R S B]
    exact (A).val.comp_algebraMap) (by trivial)

/-- The morphism of étale test objects induced contravariantly by the left tensor inclusion. -/
def relationLeftSite := testMap (S := S) ((relationLeft F B e).restrictScalars R)
/-- The morphism of étale test objects induced contravariantly by the right tensor inclusion. -/
def relationRightSite := testMap (S := S) (relationRight F B e)

lemma relation_isPullback : IsPullback (relationLeftSite F B e) (relationRightSite F B e)
    (inclusionSite F B e) (inclusionSite F B e) := by
  apply IsPullback.of_map_of_faithful
    (F := Scheme.Etale.forget (Spec (.of R)) ⋙ Over.forget (Spec (.of R)))
  change IsPullback
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B)))
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (IsPushout.of_isColimit (CommRingCat.pushoutCoconeIsColimit A B B))

theorem identitySection_matching (W : (Spec (.of R)).Etale)
    (a b : W ⟶ (Scheme.EtaleCohomology.siteEtalePostcompose (chart R S)).obj (test S B))
    (hab : a ≫ inclusionSite F B e = b ≫ inclusionSite F B e) :
    F.obj.map a.op (identitySection F B e) = F.obj.map b.op (identitySection F B e) := by
  let H := relation_isPullback F B e
  let l := H.lift a b hab
  calc
    F.obj.map a.op (identitySection F B e) =
        F.obj.map (l ≫ relationLeftSite F B e).op (identitySection F B e) := by
      rw [H.lift_fst]
    _ = F.obj.map l.op
        (F.obj.map (relationLeftSite F B e).op (identitySection F B e)) := by simp
    _ = F.obj.map l.op
        (F.obj.map (relationRightSite F B e).op (identitySection F B e)) :=
      congrArg (F.obj.map l.op) (identitySection_relation F B e).symm
    _ = F.obj.map b.op (identitySection F B e) := by
      rw [← Functor.map_comp_apply, ← op_comp, H.lift_snd]

theorem existsUnique_descendedSection :
    ∃! s : F.obj.obj (op ((toEtale (Spec (.of R))).obj (AffineDescent.descendedCover D))),
      F.obj.map (inclusionSite F B e).op s = identitySection F B e := by
  have : Surjective (inclusionSite F B e).left := AffineDescent.invariantInclusion_surjective D
  exact etaleSheaf_existsUnique_descend F (inclusionSite F B e) (identitySection F B e)
    (identitySection_matching F B e)

/-- The section on the descended cover chosen as the unique descent of `identitySection`. -/
def descendedSection :
    F.obj.obj (op ((toEtale (Spec (.of R))).obj (AffineDescent.descendedCover D))) :=
  (existsUnique_descendedSection F B e).choose

lemma descendedSection_restrict :
    F.obj.map (inclusionSite F B e).op (descendedSection F B e) = identitySection F B e :=
  (existsUnique_descendedSection F B e).choose_spec.1

/-- The actual morphism from the constructed affine section sheaf to F. -/
def descendedMap : Scheme.EtaleCohomology.finiteRepresentedSetSheaf (AffineDescent.descendedCover
  D) ⟶ F :=
  finiteRepresentedSectionMap (AffineDescent.descendedCover D) (descendedSection F B e)

/-- Identify the original affine cover with the restriction of the reconstructed one. -/
def localComparison : Scheme.EtaleCohomology.finiteRepresentedSetSheaf (AffineDescent.specCover S
  B) ≅
    (Scheme.EtaleCohomology.setEtaleRestriction (chart R S)).obj
      (Scheme.EtaleCohomology.finiteRepresentedSetSheaf (AffineDescent.descendedCover D)) :=
  Scheme.EtaleCohomology.finiteRepresentedSetSheafMapIso
    ((forget (Spec (.of S))).mapIso (AffineDescent.baseChangeCoverIso D).symm) ≪≫
    (finiteRepresentedRestrictionIso (chart R S) (AffineDescent.descendedCover D)).symm

lemma localComparison_identity :
    (localComparison F B e).hom.hom.app
      (op ((toEtale (Spec (.of S))).obj (AffineDescent.specCover S B)))
      (ULift.up (𝟙 (AffineDescent.specCover S B).obj)) =
    ULift.up ((Scheme.Etale.forget (Spec (.of R))).map (inclusionSite F B e)) := by
  apply ULift.ext
  apply Over.OverMorphism.ext
  change ((AffineDescent.pullbackIso D).inv ≫
    (pullbackSymmetry (AffineDescent.descendedCover D).obj.hom (chart R S)).inv) ≫
      pullback.fst (AffineDescent.descendedCover D).obj.hom (chart R S) =
        Spec.map (CommRingCat.ofHom (A).val.toRingHom)
  rw [Category.assoc, pullbackSymmetry_inv_comp_fst]
  exact AffineDescent.pullbackIso_inv_second D

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
lemma identitySection_eq_e : identitySection F B e =
    e.hom.hom.app (op ((toEtale (Spec (.of S))).obj (AffineDescent.specCover S B)))
      (ULift.up (𝟙 (AffineDescent.specCover S B).obj)) := by
  change e.hom.hom.app (op (test S B))
    (ULift.up (algHomOverEquiv S B B (AlgHom.id S B))) = _
  congr 1
  apply congrArg ULift.up
  apply Over.OverMorphism.ext
  exact Spec.map_id _

lemma descendedMap_local : (localComparison F B e).hom ≫
    (Scheme.EtaleCohomology.setEtaleRestriction (chart R S)).map (descendedMap F B e) = e.hom := by
  apply (finiteRepresentedSectionEquiv (AffineDescent.specCover S B)).injective
  change (descendedMap F B e).hom.app
    (op ((Scheme.EtaleCohomology.siteEtalePostcompose (chart R S)).obj (test S B)))
      ((localComparison F B e).hom.hom.app
        (op ((toEtale (Spec (.of S))).obj (AffineDescent.specCover S B)))
        (ULift.up (𝟙 (AffineDescent.specCover S B).obj))) = _
  rw [localComparison_identity]
  change F.obj.map (inclusionSite F B e).op (descendedSection F B e) = _
  rw [descendedSection_restrict, identitySection_eq_e]
  rfl

theorem descendedMap_isIso : IsIso (descendedMap F B e) := by
  have : IsIso ((localComparison F B e).hom ≫
      (Scheme.EtaleCohomology.setEtaleRestriction (chart R S)).map (descendedMap F B e)) := by
    rw [descendedMap_local]
    infer_instance
  have : IsIso ((Scheme.EtaleCohomology.setEtaleRestriction (chart R S)).map (descendedMap F B e))
    :=
    IsIso.of_isIso_comp_left (localComparison F B e).hom _
  have : Surjective (chart R S) :=
    ((flat_and_surjective_SpecMap_iff _).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance)).2
  exact isIso_of_setEtaleRestriction_map (chart R S) (descendedMap F B e)

/-- The reconstructed affine finite-etale cover represents the original sheaf. -/
def descendedIso : Scheme.EtaleCohomology.finiteRepresentedSetSheaf (AffineDescent.descendedCover
  D) ≅ F
  := by
  letI := descendedMap_isIso F B e
  exact asIso (descendedMap F B e)

include e in
theorem exists_affine_representative :
    ∃ Y : Scheme.FiniteEtale (Spec (.of R)), Nonempty
      (Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y
      ≅ F) :=
  ⟨AffineDescent.descendedCover D, ⟨descendedIso F B e⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.AffineSheafAlgebraDatum

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 c9610f3240309fc999d770dc4f128920541dc8aac67420b48415a686079fc110.
Definitions, hypotheses and universes are retained modulo native names. -/
