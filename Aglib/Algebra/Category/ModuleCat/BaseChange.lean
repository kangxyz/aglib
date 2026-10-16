/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Scalar extension across a commutative-ring pushout

The actual extension/restriction-of-scalars mate is the canonical tensor
pushout comparison. Its isomorphism and pure-tensor/unit equations require
no flatness, finiteness, schemes or reducedness.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/AffineModuleBaseChange.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`0739a4c1e7297a8f1dec99f8f53914339710e9240fa56c70a90ae2127581ed06`. Selected original ranges: [[254,
262], [311, 403], [837, 861], [924, 938]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits Module
namespace ModuleCat
universe u

/-- Identify categorical scalar extension with the tensor product for the given algebra structure.
-/
def extendScalarsAlgebraIso (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅
      ModuleCat.of S (TensorProduct R S M) := by
  let F : Algebra R S → ModuleCat S := fun a ↦
    letI := a
    ModuleCat.of S (TensorProduct R S M)
  have h := congrArg F (toAlgebra_algebraMap (R := R) (S := S))
  exact eqToIso h

open scoped ChangeOfRings in
lemma extendScalarsAlgebraIso_tmul (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) (s : S) (m : M) :
    (extendScalarsAlgebraIso R S M).hom (s ⊗ₜ[R,algebraMap R S] m) = s ⊗ₜ[R] m := by
  let F : Algebra R S → ModuleCat S := fun a ↦ letI := a; ModuleCat.of S (TensorProduct R S M)
  let t (a : Algebra R S) : F a := letI := a; s ⊗ₜ[R] m
  have ht (a b : Algebra R S) (h : a = b) :
      (eqToIso (congrArg F h)).hom (t a) = t b := by
    cases h
    rfl
  exact ht _ _ (toAlgebra_algebraMap (R := R) (S := S))

open scoped ChangeOfRings in
lemma extendScalarsAlgebraIso_inv_tmul (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) (s : S) (m : M) :
    (extendScalarsAlgebraIso R S M).inv (s ⊗ₜ[R] m) = s ⊗ₜ[R,algebraMap R S] m := by
  apply ((ConcreteCategory.bijective_of_isIso (extendScalarsAlgebraIso R S M).hom).1)
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    extendScalarsAlgebraIso_tmul]

/-- Identify categorical scalar restriction with the given compatible module structure. -/
def restrictScalarsAlgebraIso (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} S) [Module R M] [IsScalarTower R S M] :
    (ModuleCat.restrictScalars (algebraMap R S)).obj M ≅ ModuleCat.of R M := by
  refine (AddEquiv.toLinearEquiv (M := ↑((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    (M₂ := M) (AddEquiv.refl M) ?_).toModuleIso
  intro r m
  change M at m
  change algebraMap R S r • m = r • m
  exact IsScalarTower.algebraMap_smul S r m

section TensorBaseChange
open TensorProduct

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

/-- The tensor-product comparison induced by the given algebra pushout. -/
def tensorBaseChangeIso (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
      ((ModuleCat.restrictScalars (algebraMap R A)).obj M) ≅
    (ModuleCat.restrictScalars (algebraMap S B)).obj
      ((ModuleCat.extendScalars (algebraMap A B)).obj M) := by
  letI : Module R M := Module.compHom M (algebraMap R A)
  letI : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact extendScalarsAlgebraIso R S ((ModuleCat.restrictScalars (algebraMap R A)).obj M) ≪≫
    (Algebra.IsPushout.cancelBaseChange R S A B M).symm.toModuleIso ≪≫
    (restrictScalarsAlgebraIso S B (ModuleCat.of B (B ⊗[A] M))).symm ≪≫
    (ModuleCat.restrictScalars (algebraMap S B)).mapIso (extendScalarsAlgebraIso A B M).symm

open scoped ChangeOfRings in
lemma tensorBaseChangeIso_tmul (M : ModuleCat.{u} A) (s : S) (m : M) :
    (tensorBaseChangeIso R S A B M).hom
      (s ⊗ₜ[R,algebraMap R S] (show (ModuleCat.restrictScalars (algebraMap R A)).obj M from m)) =
      algebraMap S B s ⊗ₜ[A,algebraMap A B] m := by
  letI : Module R M := Module.compHom M (algebraMap R A)
  letI : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  change (extendScalarsAlgebraIso A B M).inv
      ((Algebra.IsPushout.cancelBaseChange R S A B M).symm
        ((extendScalarsAlgebraIso R S
          ((ModuleCat.restrictScalars (algebraMap R A)).obj M)).hom
          (s ⊗ₜ[R,algebraMap R S] m))) = _
  rw [extendScalarsAlgebraIso_tmul]
  change (extendScalarsAlgebraIso A B M).inv
      ((Algebra.IsPushout.cancelBaseChangeAux R S A B M).symm (s ⊗ₜ[R] m)) = _
  rw [Algebra.IsPushout.cancelBaseChangeAux_symm_tmul, extendScalarsAlgebraIso_inv_tmul]

/-- The scalar-extension comparison map obtained from the given algebra pushout. -/
def tensorBaseChangeMap (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
      ((ModuleCat.restrictScalars (algebraMap R A)).obj M) ⟶
    (ModuleCat.restrictScalars (algebraMap S B)).obj
      ((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _).symm
    ((ModuleCat.restrictScalars (algebraMap R A)).map
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).unit.app M) ≫
      (ModuleCat.restrictScalarsComp'App (algebraMap R A) (algebraMap A B)
        (algebraMap R B) (IsScalarTower.algebraMap_eq R A B) _).inv ≫
      (ModuleCat.restrictScalarsComp'App (algebraMap R S) (algebraMap S B)
        (algebraMap R B) (IsScalarTower.algebraMap_eq R S B) _).hom)

theorem tensorBaseChangeMap_eq (M : ModuleCat.{u} A) :
    tensorBaseChangeMap R S A B M = (tensorBaseChangeIso R S A B M).hom := by
  apply (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _ |>.injective
  rw [tensorBaseChangeMap, Equiv.apply_symm_apply]
  ext m
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, tensorBaseChangeIso_tmul]
  simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply,
    ModuleCat.restrictScalarsComp'App_hom_apply, map_one]
  rfl

instance tensorBaseChangeMap_isIso (M : ModuleCat.{u} A) :
    IsIso (tensorBaseChangeMap R S A B M) := by
  rw [tensorBaseChangeMap_eq]
  infer_instance


end TensorBaseChange

section Categorical
variable {R A S B : CommRingCat.{u}}

/-- The categorical module base-change map for a commutative square of ring maps. -/
def baseChangeMap (φ : R ⟶ A) (ψ : R ⟶ S) (ρ : A ⟶ B) (σ : S ⟶ B)
    (w : φ ≫ ρ = ψ ≫ σ) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.restrictScalars φ.hom).obj M) ⟶
      (ModuleCat.restrictScalars σ.hom).obj ((ModuleCat.extendScalars ρ.hom).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).symm
    ((ModuleCat.restrictScalars φ.hom).map ((ModuleCat.extendRestrictScalarsAdj ρ.hom).unit.app M) ≫
      (ModuleCat.restrictScalarsComp'App φ.hom ρ.hom (φ ≫ ρ).hom rfl _).inv ≫
      (ModuleCat.restrictScalarsComp'App ψ.hom σ.hom (φ ≫ ρ).hom
        (congrArg CommRingCat.Hom.hom w) _).hom)

theorem baseChangeMap_isIso (φ : R ⟶ A) (ψ : R ⟶ S)
    (ρ : A ⟶ B) (σ : S ⟶ B) (H : IsPushout φ ψ ρ σ) (M : ModuleCat.{u} A) :
    IsIso (baseChangeMap φ ψ ρ σ H.w M) := by
  letI : Algebra R A := φ.hom.toAlgebra
  letI : Algebra R S := ψ.hom.toAlgebra
  letI : Algebra A B := ρ.hom.toAlgebra
  letI : Algebra S B := σ.hom.toAlgebra
  letI : Algebra R B := (ρ.hom.comp φ.hom).toAlgebra
  letI : IsScalarTower R A B := .of_algebraMap_eq (fun _ ↦ rfl)
  letI : IsScalarTower R S B := .of_algebraMap_eq
    (fun r ↦ ConcreteCategory.congr_hom H.w r)
  letI : Algebra.IsPushout R S A B :=
    (CommRingCat.isPushout_iff_isPushout).mp H.flip
  change IsIso (tensorBaseChangeMap R S A B M)
  infer_instance

theorem baseChangeMap_unit_apply {R A S B : CommRingCat.{u}}
    (φ : R ⟶ A) (ψ : R ⟶ S) (ρ : A ⟶ B) (σ : S ⟶ B)
    (w : φ ≫ ρ = ψ ≫ σ) (M : ModuleCat.{u} A) (m : M) :
    baseChangeMap φ ψ ρ σ w M
      ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
        ((ModuleCat.restrictScalars φ.hom).obj M) m) =
      (ModuleCat.extendRestrictScalarsAdj ρ.hom).unit.app M m := by
  have hh := Equiv.apply_symm_apply
    ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _)
    ((ModuleCat.restrictScalars φ.hom).map ((ModuleCat.extendRestrictScalarsAdj ρ.hom).unit.app M) ≫
      (ModuleCat.restrictScalarsComp'App φ.hom ρ.hom (φ ≫ ρ).hom rfl _).inv ≫
      (ModuleCat.restrictScalarsComp'App ψ.hom σ.hom (φ ≫ ρ).hom
        (congrArg CommRingCat.Hom.hom w) _).hom)
  have ht := congrArg (fun z ↦ z m) hh
  exact ht

end Categorical
end ModuleCat
