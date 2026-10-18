/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.TensorProduct.PurelyInseparable
public import Aglib.RingTheory.Descent.Basic
public import Aglib.RingTheory.Descent.Morphisms
public import Aglib.RingTheory.Descent.Nilpotent
public import Aglib.RingTheory.Descent.PurelyInseparable.BaseChange
public import Aglib.RingTheory.Descent.Canonical
public import Aglib.RingTheory.Descent.PurelyInseparable.Morphisms
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineCoverAlgebra

/-!
# GlobalFinitePureAffine

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

open _root_.Algebra.Descent.PurelyInseparable (baseChangedPureDatum)

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange baseChangeForgetIso)
open AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u

/-- Faithful flat base change is faithful on the actual finite étale cover category. -/
theorem baseChange_faithful_of_flat_surjective {X T : Scheme.{u}} (f : T ⟶ X)
    [Flat f] [Surjective f] : (baseChange f).Faithful := by
  let (Z : Scheme.{u}) (g : Z ⟶ X) : Epi (pullback.fst g f) :=
    Flat.epi_of_flat_of_surjective _
  let : (Over.pullback f).Faithful := inferInstance
  exact Functor.Faithful.of_comp_iso (baseChangeForgetIso f)

@[reassoc] theorem baseChangeMap_fst {X T : Scheme.{u}} (f : T ⟶ X)
    {Y Z : Scheme.FiniteEtale X} (g : Y ⟶ Z) :
    ((baseChange f).map g).hom.left ≫ pullback.fst Z.obj.hom f =
      pullback.fst Y.obj.hom f ≫ g.hom.left := by
  exact pullback.lift_fst _ _ _

@[reassoc] theorem baseChangeMap_snd {X T : Scheme.{u}} (f : T ⟶ X)
    {Y Z : Scheme.FiniteEtale X} (g : Y ⟶ Z) :
    ((baseChange f).map g).hom.left ≫ pullback.snd Z.obj.hom f =
      pullback.snd Y.obj.hom f := Over.w ((baseChange f).map g).hom

section Spec

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Algebra.Etale R A] [Module.Finite R B] [Algebra.Etale R B]

/-- The morphism `Spec B ⟶ Spec A` of finite étale covers over `Spec R` induced
contravariantly by the `R`-algebra homomorphism `f`. -/
def specCoverHom (f : A →ₐ[R] B) : specCover R B ⟶ specCover R A :=
  ObjectProperty.homMk ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)

@[simp] theorem specCoverHom_left (f : A →ₐ[R] B) :
    (specCoverHom R A B f).hom.left = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism from the base change of `Spec A` along `Spec S ⟶ Spec R`
to `Spec (S ⊗[R] A)`, as finite étale covers of `Spec S`. -/
def specBaseChangeIso :
    (baseChange (Spec.algebraMap R S)).obj (specCover R A) ≅ specCover S (S ⊗[R] A) :=
  ObjectProperty.isoMk _ (Over.isoMk
    (pullbackSymmetry (Spec.algebraMap R A) (Spec.algebraMap R S) ≪≫ pullbackSpecIso R S A)
    (by
      change (_ ≫ _) ≫ Spec.algebraMap S (S ⊗[R] A) = _
      rw [Category.assoc, pullbackSpecIso_hom_fst']
      exact pullbackSymmetry_hom_comp_fst _ _))

theorem specBaseChangeIso_hom_left :
    (specBaseChangeIso R S A).hom.hom.left =
      (pullbackSymmetry (Spec.algebraMap R A) (Spec.algebraMap R S)).hom ≫
        (pullbackSpecIso R S A).hom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem specBaseChangeIso_naturality (f : A →ₐ[R] B) :
    (baseChange (Spec.algebraMap R S)).map (specCoverHom R A B f) ≫
      (specBaseChangeIso R S A).hom =
    (specBaseChangeIso R S B).hom ≫
      specCoverHom S (S ⊗[R] A) (S ⊗[R] B)
        (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.algebraMap R A =
      Spec.algebraMap R B := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext f.comp_algebraMap)
  let g := pullback.lift
    (pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R S) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom))
    (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R S))
    (by rw [Category.assoc, hf]; exact pullback.condition)
  change g ≫ ((pullbackSymmetry (Spec.algebraMap R A) (Spec.algebraMap R S)).hom ≫
      (pullbackSpecIso R S A).hom) =
    ((pullbackSymmetry (Spec.algebraMap R B) (Spec.algebraMap R S)).hom ≫
      (pullbackSpecIso R S B).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom)
  have hS : CommRingCat.ofHom (algebraMap S (S ⊗[R] A)) ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom =
        CommRingCat.ofHom (algebraMap S (S ⊗[R] B)) :=
    CommRingCat.hom_ext (Algebra.TensorProduct.map (AlgHom.id S S) f).comp_algebraMap
  have hA : CommRingCat.ofHom
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)) ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom =
        CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom
          (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)) := by
    ext x
    rfl
  apply (cancel_mono (pullbackSpecIso R S A).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst']
    rw [← Spec.map_comp, hS]
    simp only [pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst, g, pullback.lift_snd]
  · simp only [Category.assoc, pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp, hA, Spec.map_comp]
    simp only [pullbackSpecIso_hom_snd_assoc, pullbackSymmetry_hom_comp_snd_assoc,
      pullbackSpecIso_hom_snd, pullbackSymmetry_hom_comp_snd, g, pullback.lift_fst]

end Spec

section Pure

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L] [Module.Finite K L]
  (R : Type u) [CommRing R] [Algebra K R]

/-- Actual affine cover-object descent after any affine base change. -/
def affinePureCoverDescent (Y : Scheme.FiniteEtale (Spec (CommRingCat.of (R ⊗[K] L)))) :
    Σ U : Scheme.FiniteEtale (Spec (CommRingCat.of R)),
      (baseChange (Spec.algebraMap R (R ⊗[K] L))).obj U ≅ Y := by
  let M := algebraModel Y
  let B := M.algebra
  let : Algebra R B := ((algebraMap (R ⊗[K] L) B).comp
    (algebraMap R (R ⊗[K] L))).toAlgebra
  let : IsScalarTower R (R ⊗[K] L) B := IsScalarTower.of_algebraMap_eq' rfl
  let D := baseChangedPureDatum K L R B
  exact ⟨descendedCover D, baseChangeCoverIso D ≪≫ M.coverIso⟩

end Pure

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 440eb5c948821d477ab1597aaa722ddb3de6eca1e63cb7a99b79a40e5ece6476.
Definitions, hypotheses and universes are retained modulo native names. -/
