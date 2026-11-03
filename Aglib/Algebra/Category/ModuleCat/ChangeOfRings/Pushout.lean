/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Composition
public import Mathlib.RingTheory.IsTensorProduct

/-! # Original regular-source comparison over an algebra pushout -/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings

universe u

namespace ModuleCat

section Source

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

/-- The original tensor pushout equivalence on the actual regular source module. -/
abbrev scalarExtensionPushoutIso :
    (extendScalars (algebraMap R S)).obj (ModuleCat.of R A) ≅ ModuleCat.of S B :=
  extendScalarsAlgebraObjIso R S (ModuleCat.of R A) ≪≫
    (Algebra.IsPushout.equiv R S A B).toLinearEquiv.toModuleIso

/-- The native pushout source comparison retains its original algebra unit. -/
theorem scalarExtensionPushoutIso_one_tmul (a : A) :
    (scalarExtensionPushoutIso R S A B).hom
      ((1 : S) ⊗ₜ[R,algebraMap R S] a) = algebraMap A B a := by
  change Algebra.IsPushout.equiv R S A B
    ((extendScalarsAlgebraObjIso R S (ModuleCat.of R A)).hom
      ((1 : S) ⊗ₜ[R,algebraMap R S] a)) = _
  rw [extendScalarsAlgebraObjIso_hom_tmul, Algebra.IsPushout.equiv_tmul, map_one, one_mul]

end Source

section Composition

variable (R S T A B C : Type u)
  [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [Algebra R A] [Algebra S B] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B] [IsScalarTower R S B]
  [Algebra R C] [Algebra S C] [Algebra T C] [Algebra A C] [Algebra B C]
  [IsScalarTower R T C] [IsScalarTower S T C] [IsScalarTower S B C]
  [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower A B C]
  [Algebra.IsPushout R S A B] [Algebra.IsPushout S T B C]

/-- Two actual pushout source comparisons compose through the original scalar
triangle; the composite pushout is derived from the two given stages. -/
theorem scalarExtensionPushoutIso_comp :
    letI : Algebra.IsPushout R T A C :=
      (Algebra.IsPushout.comp_iff R S A (S' := B) (T := T) (T' := C)).mpr inferInstance
    (scalarExtensionPushoutIso R T A C).hom =
      (extendScalarsCompOfEq (algebraMap R S) (algebraMap S T) (algebraMap R T)
        (IsScalarTower.algebraMap_eq R S T).symm).hom.app (ModuleCat.of R A) ≫
      (extendScalars (algebraMap S T)).map (scalarExtensionPushoutIso R S A B).hom ≫
      (scalarExtensionPushoutIso S T B C).hom := by
  let : Algebra.IsPushout R T A C :=
    (Algebra.IsPushout.comp_iff R S A (S' := B) (T := T) (T' := C)).mpr inferInstance
  apply ExtendScalars.hom_ext
  intro a
  let qRS := scalarExtensionPushoutIso R S A B
  let qST := scalarExtensionPushoutIso S T B C
  have hRS := scalarExtensionPushoutIso_one_tmul R S A B a
  have hST := scalarExtensionPushoutIso_one_tmul S T B C (algebraMap A B a)
  have hRT := scalarExtensionPushoutIso_one_tmul R T A C a
  have hc := extendScalarsCompOfEq_hom_app_one_tmul
    (algebraMap R S) (algebraMap S T) (algebraMap R T)
    (IsScalarTower.algebraMap_eq R S T).symm (ModuleCat.of R A) a
  have hm := ExtendScalars.map_tmul (algebraMap S T) qRS.hom (1 : T)
    ((1 : S) ⊗ₜ[R,algebraMap R S] a)
  have h₁ := congrArg
    (fun x : (extendScalars (algebraMap S T)).obj
        ((extendScalars (algebraMap R S)).obj (ModuleCat.of R A)) =>
      qST.hom ((extendScalars (algebraMap S T)).map qRS.hom x)) hc
  have h₂ := congrArg
    (fun x : (extendScalars (algebraMap S T)).obj (ModuleCat.of S B) => qST.hom x) hm
  have h₃ := congrArg (fun x : B => qST.hom ((1 : T) ⊗ₜ[S,algebraMap S T] x)) hRS
  exact hRT.trans
    (h₁.trans (h₂.trans (h₃.trans (hST.trans
      (IsScalarTower.algebraMap_apply A B C a).symm)))).symm

/-- The same original pushout comparisons retain their inverse-source square. -/
theorem scalarExtensionPushoutIso_inv_comp :
    letI : Algebra.IsPushout R T A C :=
      (Algebra.IsPushout.comp_iff R S A (S' := B) (T := T) (T' := C)).mpr inferInstance
    (scalarExtensionPushoutIso R T A C).inv ≫
      (extendScalarsCompOfEq (algebraMap R S) (algebraMap S T) (algebraMap R T)
        (IsScalarTower.algebraMap_eq R S T).symm).hom.app (ModuleCat.of R A) =
      (scalarExtensionPushoutIso S T B C).inv ≫
        (extendScalars (algebraMap S T)).map (scalarExtensionPushoutIso R S A B).inv := by
  let : Algebra.IsPushout R T A C :=
    (Algebra.IsPushout.comp_iff R S A (S' := B) (T := T) (T' := C)).mpr inferInstance
  apply ((scalarExtensionPushoutIso R T A C).inv_comp_eq).2
  rw [scalarExtensionPushoutIso_comp R S T A B C]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact (CategoryTheory.Category.comp_id
    (show (extendScalars (algebraMap R T)).obj (ModuleCat.of R A) ⟶
      (extendScalars (algebraMap S T)).obj
        ((extendScalars (algebraMap R S)).obj (ModuleCat.of R A)) from
      (extendScalarsCompOfEq (algebraMap R S) (algebraMap S T) (algebraMap R T)
        (IsScalarTower.algebraMap_eq R S T).symm).hom.app (ModuleCat.of R A))).symm

end Composition

end ModuleCat
