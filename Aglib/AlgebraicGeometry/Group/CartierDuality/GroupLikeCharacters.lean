/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.SpecUnitsTensor
public import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Group-like units and characters into the existing multiplicative group

All maps use native Hopf Spec and the existing unit-representing Gm. The
group-like equations are the actual unit and multiplication squares, through
the original native monoidal Spec comparisons.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

variable {R : Type u} [CommRing R]

/-- The native braided Spec structure used for Hopf algebra characters. -/
local instance instBraidedAlgSpecCharacters :
    (AlgebraicGeometry.algSpec (CommRingCat.of R)).Braided :=
  AlgebraicGeometry.braidedAlgSpec

/-- The original multiplicative group law on the target of the represented characters. -/
local instance instCommGrpObjCharacters :
    CommGrpObj (MultiplicativeGroup.scheme (Spec (CommRingCat.of R))) :=
  MultiplicativeGroup.commGroup _

/-- The represented unit map, typed at the original native Hopf-Spec group. -/
def hopfUnitMap (A : CommHopfAlgCat.{u} R) (u : Aˣ) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op A)).X ⟶
      MultiplicativeGroup.scheme (Spec (CommRingCat.of R)) :=
  specUnitMap (CommAlgCat.of R A) u

/-- The unit square is the original counit pullback of the given unit. -/
theorem hopfUnitMap_one_coordinates (A : CommHopfAlgCat.{u} R) (u : Aˣ) :
    (Functor.Monoidal.εIso (AlgebraicGeometry.algSpec (CommRingCat.of R))).inv ≫
        η[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op A)).X] ≫
          hopfUnitMap A u =
      specUnitMap (CommAlgCat.of R R)
        (Units.map (Bialgebra.counitAlgHom R A).toMonoidHom u) := by
  change (Functor.Monoidal.εIso (AlgebraicGeometry.algSpec (CommRingCat.of R))).inv ≫
    ((Functor.Monoidal.εIso (AlgebraicGeometry.algSpec (CommRingCat.of R))).hom ≫
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).map
        (CommAlgCat.ofHom (Bialgebra.counitAlgHom R A)).op) ≫
      specUnitMap (CommAlgCat.of R A) u = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, specUnitMap_naturality]
  rfl

/-- The multiplication square is the original comultiplication pullback of the unit. -/
theorem hopfUnitMap_mul_coordinates (A : CommHopfAlgCat.{u} R) (u : Aˣ) :
    (algSpecTensorIso (CommAlgCat.of R A) (CommAlgCat.of R A)).inv ≫
        μ[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op A)).X] ≫
          hopfUnitMap A u =
      specUnitMap (CommAlgCat.of R A ⊗ CommAlgCat.of R A)
        (Units.map (Bialgebra.comulAlgHom R A).toMonoidHom u) := by
  change (algSpecTensorIso (CommAlgCat.of R A) (CommAlgCat.of R A)).inv ≫
    ((algSpecTensorIso (CommAlgCat.of R A) (CommAlgCat.of R A)).hom ≫
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).map
        (CommAlgCat.ofHom (Bialgebra.comulAlgHom R A)).op) ≫
      specUnitMap (CommAlgCat.of R A) u = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, specUnitMap_naturality]
  rfl

/-- The product of the two characters uses the two original tensor inclusions. -/
theorem hopfUnitMap_tensor_coordinates (A : CommHopfAlgCat.{u} R) (u : Aˣ) :
    (algSpecTensorIso (CommAlgCat.of R A) (CommAlgCat.of R A)).inv ≫
        (hopfUnitMap A u ⊗ₘ hopfUnitMap A u) ≫
          μ[MultiplicativeGroup.scheme (Spec (CommRingCat.of R))] =
      specUnitMap (CommAlgCat.of R A ⊗ CommAlgCat.of R A)
        (Units.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toMonoidHom u *
          Units.map (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toMonoidHom u) := by
  exact specUnitMap_tensor_coordinates (CommAlgCat.of R A) u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original represented map is multiplicative exactly when its unit is group-like. -/
theorem isMonHom_hopfUnitMap_iff (A : CommHopfAlgCat.{u} R) (u : Aˣ) :
    IsMonHom (hopfUnitMap A u) ↔ IsGroupLikeElem R (u : A) := by
  constructor
  · intro h
    let := h
    constructor
    · have hunit := congrArg
        (fun q => (Functor.Monoidal.εIso
          (AlgebraicGeometry.algSpec (CommRingCat.of R))).inv ≫ q)
        (IsMonHom.one_hom (hopfUnitMap A u))
      rw [hopfUnitMap_one_coordinates, MonObj.one_eq_one,
        MonObj.comp_one, ← specUnitMap_one (CommAlgCat.of R R)] at hunit
      have hu := (specUnitsEquiv (CommAlgCat.of R R)).symm.injective hunit
      exact congrArg Units.val hu
    · have hmul := congrArg
        (fun q => (algSpecTensorIso (CommAlgCat.of R A) (CommAlgCat.of R A)).inv ≫ q)
        (IsMonHom.mul_hom (hopfUnitMap A u))
      rw [hopfUnitMap_mul_coordinates, hopfUnitMap_tensor_coordinates] at hmul
      have hu :=
        (specUnitsEquiv (CommAlgCat.of R A ⊗ CommAlgCat.of R A)).symm.injective hmul
      have hval := congrArg Units.val hu
      simpa using hval
  · intro h
    constructor
    · apply (cancel_epi
        (Functor.Monoidal.εIso (AlgebraicGeometry.algSpec (CommRingCat.of R))).inv).mp
      rw [hopfUnitMap_one_coordinates, MonObj.one_eq_one, MonObj.comp_one]
      have hu : Units.map (Bialgebra.counitAlgHom R A).toMonoidHom u = 1 :=
        Units.ext h.counit_eq_one
      rw [hu, specUnitMap_one]
    · apply (cancel_epi (algSpecTensorIso (CommAlgCat.of R A) (CommAlgCat.of R A)).inv).mp
      rw [hopfUnitMap_mul_coordinates, hopfUnitMap_tensor_coordinates]
      congr 1
      apply Units.ext
      simpa using h.comul_eq_tmul_self

/-- A native group-like element gives an actual character into the existing Gm. -/
def groupLikeCharacter (A : CommHopfAlgCat.{u} R) (a : GroupLike R A) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op A) ⟶
      MultiplicativeGroup.groupScheme (Spec (CommRingCat.of R)) := by
  exact Grp.homMk' {
    hom := hopfUnitMap A (GroupLike.toUnits R a)
    isMonHom_hom := (isMonHom_hopfUnitMap_iff A (GroupLike.toUnits R a)).2 a.2 }

/-- The original unit coordinate of an actual character is group-like. -/
def groupLikeOfCharacter (A : CommHopfAlgCat.{u} R)
    (f : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op A) ⟶
      MultiplicativeGroup.groupScheme (Spec (CommRingCat.of R))) : GroupLike R A := by
  let u := specUnitsEquiv (CommAlgCat.of R A) f.hom.hom
  refine ⟨u.val, (isMonHom_hopfUnitMap_iff A u).1 ?_⟩
  have hu : hopfUnitMap A u = f.hom.hom :=
    specUnitMap_specUnitsEquiv (CommAlgCat.of R A) f.hom.hom
  rw [hu]
  exact f.hom.isMonHom_hom

/-- Native group-like elements are exactly the actual group-scheme characters into existing Gm. -/
def groupLikeCharacterEquiv (A : CommHopfAlgCat.{u} R) :
    GroupLike R A ≃
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op A) ⟶
        MultiplicativeGroup.groupScheme (Spec (CommRingCat.of R))) where
  toFun := groupLikeCharacter A
  invFun := groupLikeOfCharacter A
  left_inv a := by
    apply GroupLike.val_injective
    change (specUnitsEquiv (CommAlgCat.of R A)
      (specUnitMap (CommAlgCat.of R A) (GroupLike.toUnits R a))).val = a.val
    rw [specUnitsEquiv_specUnitMap]
    rfl
  right_inv f := by
    apply Grp.hom_ext
    change hopfUnitMap A (GroupLike.toUnits R (groupLikeOfCharacter A f)) = f.hom.hom
    have hu : GroupLike.toUnits R (groupLikeOfCharacter A f) =
        specUnitsEquiv (CommAlgCat.of R A) f.hom.hom := by
      apply Units.ext
      rfl
    rw [hu]
    exact specUnitMap_specUnitsEquiv (CommAlgCat.of R A) f.hom.hom

/-- The comparison retains the actual represented unit, with its native antipode inverse. -/
theorem groupLikeCharacterEquiv_units (A : CommHopfAlgCat.{u} R) (a : GroupLike R A) :
    specUnitsEquiv (CommAlgCat.of R A) (groupLikeCharacterEquiv A a).hom.hom =
      GroupLike.toUnits R a :=
  specUnitsEquiv_specUnitMap (CommAlgCat.of R A) (GroupLike.toUnits R a)

/-- Contravariant native Hopf Spec and the original group-like map preserve the character. -/
theorem groupLikeCharacter_naturality {A B : CommHopfAlgCat.{u} R} (f : A ⟶ B)
    (a : GroupLike R A) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op ≫ groupLikeCharacter A a =
      groupLikeCharacter B ⟨f.hom a.val, a.2.map f.hom⟩ := by
  apply Grp.hom_ext
  change (AlgebraicGeometry.algSpec (CommRingCat.of R)).map
      (CommAlgCat.ofHom f.hom.toAlgHom).op ≫
      specUnitMap (CommAlgCat.of R A) (GroupLike.toUnits R a) =
    specUnitMap (CommAlgCat.of R B) (GroupLike.toUnits R ⟨f.hom a.val, a.2.map f.hom⟩)
  rw [specUnitMap_naturality]
  congr 1
  apply Units.ext
  rfl

end AlgebraicGeometry.Scheme.Group.CartierDuality
