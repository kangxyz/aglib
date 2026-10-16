/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.KernelBaseChange
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Quotient-flat base change of actual ring ideals

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits Opposite
open TensorProduct
open LinearMap

section
namespace Algebra

/-- Scalar extension of the ideal inclusion, followed by the canonical unit identification. -/
def extendedIdealInclusion (S : Type u) (A : Type v) [CommRing S] [CommRing A]
    [Algebra S A] (I : Ideal S) : A ⊗[S] I →ₗ[A] A :=
  (AlgebraTensorModule.rid S A A).toLinearMap.comp (I.subtype.baseChange A)

@[simp]
theorem extendedIdealInclusion_tmul (S : Type u) (A : Type v) [CommRing S]
    [CommRing A] [Algebra S A] (I : Ideal S) (a : A) (x : I) :
    _root_.Algebra.extendedIdealInclusion S A I (a ⊗ₜ[S] x) = (x : S) • a := rfl

end Algebra
end

section
namespace Algebra

variable (R : Type u) (S : Type v) (T : Type w) (A : Type t)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R T] [Algebra R A] [Algebra S T]
    [IsScalarTower R S T]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The quotient-flat kernel equivalence identifies the actual scalar-extended ideal inclusion.
No flatness of the ambient algebra or of the base-change algebra is assumed. -/
theorem flatQuotient_idealBaseChange_inclusion [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) :
    (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A A)
      (IsScalarTower.toAlgHom R S T))).subtype.comp
        (Algebra.kerTensorProductMapIdToAlgHomEquiv R S T A hsurj).symm.toLinearMap =
      _root_.Algebra.extendedIdealInclusion S (A ⊗[R] S) (RingHom.ker (algebraMap S T)) := by
  ext z
  change ((Algebra.kerTensorProductMapIdToAlgHomEquiv R S T A hsurj).symm
    (((1 : A) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] z)).val = _
  rw [Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply]
  simp [_root_.Algebra.extendedIdealInclusion, Algebra.smul_def,
    Algebra.TensorProduct.algebraMap_eq_includeRight]

/-- Tensoring the ideal inclusion stays injective when its quotient is flat over the base. -/
theorem flatQuotient_extendedIdealInclusion_injective [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) :
    Function.Injective
      (_root_.Algebra.extendedIdealInclusion S (A ⊗[R] S) (RingHom.ker (algebraMap S T))) := by
  rw [← _root_.Algebra.flatQuotient_idealBaseChange_inclusion R S T A hsurj]
  exact Subtype.val_injective.comp
    (Algebra.kerTensorProductMapIdToAlgHomEquiv R S T A hsurj).symm.injective

/-- The image is exactly the actual kernel of the base-changed quotient map. -/
theorem flatQuotient_extendedIdealInclusion_range [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) :
    LinearMap.range
      (_root_.Algebra.extendedIdealInclusion S (A ⊗[R] S) (RingHom.ker (algebraMap S T))) =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A A)
        (IsScalarTower.toAlgHom R S T)) := by
  rw [← _root_.Algebra.flatQuotient_idealBaseChange_inclusion R S T A hsurj]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    (Algebra.kerTensorProductMapIdToAlgHomEquiv R S T A hsurj).symm.surjective)]
  exact Submodule.range_subtype _

end Algebra
end

section
namespace Algebra

open scoped ChangeOfRings
variable (R S T A : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing A]
  [Algebra R S] [Algebra R T] [Algebra R A] [Algebra S T] [IsScalarTower R S T]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual tensor-product quotient map induced by the displayed algebra homomorphism. -/
abbrev tensorQuotientMap : (A ⊗[R] S) →+* (A ⊗[R] T) :=
  (Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom R S T)).toRingHom

theorem tensorQuotientSquare :
    CommRingCat.ofHom (algebraMap S T) ≫ CommRingCat.ofHom (algebraMap T (A ⊗[R] T)) =
      CommRingCat.ofHom (algebraMap S (A ⊗[R] S)) ≫
        CommRingCat.ofHom (_root_.Algebra.tensorQuotientMap R S T A) := by
  ext x
  simp [_root_.Algebra.tensorQuotientMap, Algebra.TensorProduct.algebraMap_eq_includeRight]

end Algebra
end

section
namespace ModuleCat

open scoped ChangeOfRings
variable (R S T A : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing A]
  [Algebra R S] [Algebra R T] [Algebra R A] [Algebra S T] [IsScalarTower R S T]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The quotient-flat scalar-extension comparison for the actual spectral ring kernels. -/
def quotientFlatSpectralIdealIso [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) :
    (ModuleCat.extendScalars (algebraMap S (A ⊗[R] S))).obj
        (ModuleCat.of S (RingHom.ker (algebraMap S T))) ≅
      ModuleCat.of (A ⊗[R] S) (RingHom.ker (_root_.Algebra.tensorQuotientMap R S T A)) :=
  ModuleCat.extendScalarsAlgebraIso S (A ⊗[R] S) _ ≪≫
    (Algebra.kerTensorProductMapIdToAlgHomEquiv R S T A hsurj).symm.toModuleIso

theorem quotientFlatSpectralIdealIso_hom_one_val [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) (x : RingHom.ker (algebraMap S T)) :
    ((ModuleCat.quotientFlatSpectralIdealIso R S T A hsurj).hom
      ((1 : A ⊗[R] S) ⊗ₜ[S,algebraMap S (A ⊗[R] S)] x) : A ⊗[R] S) =
      algebraMap S (A ⊗[R] S) x := by
  simp only [ModuleCat.quotientFlatSpectralIdealIso, _root_.Algebra.tensorQuotientMap,
    Iso.trans_hom,
    ConcreteCategory.comp_apply]
  rw [ModuleCat.extendScalarsAlgebraIso_tmul]
  change ((Algebra.kerTensorProductMapIdToAlgHomEquiv R S T A hsurj).symm
    (((1 : A) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] x)).val = _
  rw [Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply]
  simp [Algebra.TensorProduct.algebraMap_eq_includeRight]

theorem spectralExtendedIdealMap_eq_quotientFlatIso [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) :
    ModuleCat.extendedKernelMap
      (CommRingCat.ofHom (algebraMap S T))
      (CommRingCat.ofHom (_root_.Algebra.tensorQuotientMap R S T A))
      (CommRingCat.ofHom (algebraMap S (A ⊗[R] S)))
      (CommRingCat.ofHom (algebraMap T (A ⊗[R] T)))
      (_root_.Algebra.tensorQuotientSquare R S T A) =
      (ModuleCat.quotientFlatSpectralIdealIso R S T A hsurj).hom := by
  apply (ModuleCat.extendRestrictScalarsAdj (algebraMap S (A ⊗[R] S))).homEquiv _ _ |>.injective
  simp only [ModuleCat.extendedKernelMap, CommRingCat.hom_ofHom, Equiv.apply_symm_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  symm
  exact ModuleCat.quotientFlatSpectralIdealIso_hom_one_val R S T A hsurj x

end ModuleCat
end

section
namespace ModuleCat

open scoped ChangeOfRings

theorem spectralExtendedIdealMap_tmul
    {R₀ S₀ R₁ S₁ : CommRingCat.{u}} (φ : R₀ ⟶ S₀) (φ' : R₁ ⟶ S₁)
    (b : R₀ ⟶ R₁) (a : S₀ ⟶ S₁) (h : φ ≫ a = b ≫ φ')
    (r : R₁) (x : RingHom.ker φ.hom) :
    ((ModuleCat.extendedKernelMap φ φ' b a h) (r ⊗ₜ[R₀,b.hom] x) : R₁) = r * b x := by
  rfl

end ModuleCat
end

section
namespace Algebra

open scoped ChangeOfRings
variable (R S T A B C : Type u) [CommRing R] [CommRing S] [CommRing T]
  [CommRing A] [CommRing B] [CommRing C]
  [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B] [Algebra R C]
  [Algebra S T] [Algebra S B] [Algebra S C]
  [Algebra A B] [Algebra A C] [Algebra B C] [Algebra T C]
  [IsScalarTower R S T] [IsScalarTower R S B] [IsScalarTower R A B]
  [IsScalarTower R T C] [IsScalarTower R A C]
  [hABC : IsScalarTower A B C] [IsScalarTower S B C] [IsScalarTower S T C]
  [hpushB : Algebra.IsPushout R A S B] [hpushC : Algebra.IsPushout R A T C]

lemma pushoutKernelSquare :
    (IsScalarTower.toAlgHom A B C).comp (Algebra.IsPushout.equiv R A S B).toAlgHom =
      (Algebra.IsPushout.equiv R A T C).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom R S T)) := by
  ext s
  simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', IsScalarTower.coe_toAlgHom',
    AlgEquiv.coe_toAlgHom, Function.comp_apply, TensorProduct.includeRight_apply,
    TensorProduct.map_tmul, Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  rw [← IsScalarTower.algebraMap_apply S B C, ← IsScalarTower.algebraMap_apply S T C]

/-- The actual kernel comparison induced by the two specified algebra pushout equivalences. -/
def pushoutKernelEquiv :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A A)
      (IsScalarTower.toAlgHom R S T)) ≃ₗ[A] RingHom.ker (algebraMap B C) := by
  let e : A ⊗[R] S ≃ₐ[A] B := Algebra.IsPushout.equiv R A S B
  have he (z : A ⊗[R] S) :
      (Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom R S T)) z = 0 ↔
        algebraMap B C (e z) = 0 := by
    have h := congrArg (fun f : A ⊗[R] S →ₐ[A] C ↦ f z) (_root_.Algebra.pushoutKernelSquare R S T A
      B C)
    change algebraMap B C (e z) = (Algebra.IsPushout.equiv R A T C)
      ((Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom R S T)) z) at h
    rw [h]
    constructor
    · intro hz
      rw [hz, map_zero]
    · intro hz
      exact (Algebra.IsPushout.equiv R A T C).injective (hz.trans (map_zero _).symm)
  exact {
    __ := e.toEquiv.subtypeEquiv he
    map_add' := fun x y ↦ Subtype.ext (map_add e (x : A ⊗[R] S) (y : A ⊗[R] S))
    map_smul' := fun a x ↦ Subtype.ext (map_smul e a (x : A ⊗[R] S))
  }

@[simp] lemma pushoutKernelEquiv_apply_val
    (z : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A A)
      (IsScalarTower.toAlgHom R S T))) :
    ((_root_.Algebra.pushoutKernelEquiv R S T A B C) z : B) = (Algebra.IsPushout.equiv R A S B) z :=
      rfl

/-- The quotient-flat additive equivalence from the extended original kernel to the pushout kernel.
-/
def quotientFlatPushoutIdealAddEquiv [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) :
    B ⊗[S] RingHom.ker (algebraMap S T) ≃+ RingHom.ker (algebraMap B C) :=
  (Algebra.IsPushout.cancelBaseChange R A S B (RingHom.ker (algebraMap S T))).toAddEquiv.trans
    (((LinearMap.kerLTensorEquivOfSurjective
      (IsScalarTower.toAlgHom R S T).toLinearMap hsurj A).symm.toAddEquiv).trans
        (_root_.Algebra.pushoutKernelEquiv R S T A B C).toAddEquiv)

lemma quotientFlatPushoutIdealAddEquiv_apply_tmul [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) (a : A)
    (x : RingHom.ker (algebraMap S T)) :
    ((_root_.Algebra.quotientFlatPushoutIdealAddEquiv R S T A B C hsurj)
      (algebraMap A B a ⊗ₜ[S] x) : B) = algebraMap A B a * algebraMap S B x := by
  rw [← Algebra.IsPushout.cancelBaseChange_symm_tmul R A S B]
  change (Algebra.IsPushout.equiv R A S B)
    (((LinearMap.kerLTensorEquivOfSurjective (IsScalarTower.toAlgHom R S T).toLinearMap
      hsurj A).symm
      ((Algebra.IsPushout.cancelBaseChange R A S B (RingHom.ker (algebraMap S T)))
        ((Algebra.IsPushout.cancelBaseChange R A S B (RingHom.ker (algebraMap S T))).symm
          (a ⊗ₜ[R] x)))) : A ⊗[R] S) = _
  rw [LinearEquiv.apply_symm_apply,
    LinearMap.tensorKerEquivOfSurjective_symm_tmul, Algebra.IsPushout.equiv_tmul]

lemma pushoutQuotientSquare :
    CommRingCat.ofHom (algebraMap S T) ≫ CommRingCat.ofHom (algebraMap T C) =
      CommRingCat.ofHom (algebraMap S B) ≫ CommRingCat.ofHom (algebraMap B C) := by
  ext s
  change algebraMap T C (algebraMap S T s) = algebraMap B C (algebraMap S B s)
  rw [← IsScalarTower.algebraMap_apply S T C, ← IsScalarTower.algebraMap_apply S B C]

/-- The canonical scalar-extended ideal map into the actual pushout kernel. -/
def pushoutExtendedIdealMap :
    B ⊗[S] RingHom.ker (algebraMap S T) →ₗ[B] RingHom.ker (algebraMap B C) :=
  (ModuleCat.extendedKernelMap
    (CommRingCat.ofHom (algebraMap S T)) (CommRingCat.ofHom (algebraMap B C))
    (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom (algebraMap T C))
    (_root_.Algebra.pushoutQuotientSquare S T B C)).hom.comp
      (ModuleCat.extendScalarsAlgebraIso S B (ModuleCat.of S (RingHom.ker (algebraMap S
        T)))).inv.hom

lemma pushoutExtendedIdealMap_tmul (b : B) (x : RingHom.ker (algebraMap S T)) :
    ((_root_.Algebra.pushoutExtendedIdealMap S T B C) (b ⊗ₜ[S] x) : B) = b * algebraMap S B x := by
  change ((ModuleCat.extendedKernelMap
      (CommRingCat.ofHom (algebraMap S T)) (CommRingCat.ofHom (algebraMap B C))
      (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom (algebraMap T C))
      (_root_.Algebra.pushoutQuotientSquare S T B C))
    ((ModuleCat.extendScalarsAlgebraIso S B _).inv (b ⊗ₜ[S] x)) : B) = _
  rw [ModuleCat.extendScalarsAlgebraIso_inv_tmul, ModuleCat.spectralExtendedIdealMap_tmul]
  rfl

lemma pushoutExtendedIdealMap_eq_addEquiv [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T))
    (z : B ⊗[S] RingHom.ker (algebraMap S T)) :
    _root_.Algebra.pushoutExtendedIdealMap S T B C z =
      _root_.Algebra.quotientFlatPushoutIdealAddEquiv R S T A B C hsurj z := by
  obtain ⟨z, rfl⟩ := (Algebra.IsPushout.cancelBaseChange R A S B
    (RingHom.ker (algebraMap S T))).symm.surjective z
  induction z using _root_.TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    apply Subtype.ext
    rw [Algebra.IsPushout.cancelBaseChange_symm_tmul,
      _root_.Algebra.pushoutExtendedIdealMap_tmul,
        _root_.Algebra.quotientFlatPushoutIdealAddEquiv_apply_tmul]

end Algebra
end

section
namespace ModuleCat

open scoped ChangeOfRings
variable (R S T A B C : Type u) [CommRing R] [CommRing S] [CommRing T]
  [CommRing A] [CommRing B] [CommRing C]
  [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B] [Algebra R C]
  [Algebra S T] [Algebra S B] [Algebra S C]
  [Algebra A B] [Algebra A C] [Algebra B C] [Algebra T C]
  [IsScalarTower R S T] [IsScalarTower R S B] [IsScalarTower R A B]
  [IsScalarTower R T C] [IsScalarTower R A C]
  [hABC : IsScalarTower A B C] [IsScalarTower S B C] [IsScalarTower S T C]
  [hpushB : Algebra.IsPushout R A S B] [hpushC : Algebra.IsPushout R A T C]
include hABC hpushB hpushC

theorem flatQuotient_pushout_spectralExtendedIdealMap_isIso [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) :
    IsIso (ModuleCat.extendedKernelMap
      (CommRingCat.ofHom (algebraMap S T)) (CommRingCat.ofHom (algebraMap B C))
      (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom (algebraMap T C))
      (_root_.Algebra.pushoutQuotientSquare S T B C)) := by
  apply (isIso_comp_left_iff
    (ModuleCat.extendScalarsAlgebraIso S B (ModuleCat.of S (RingHom.ker (algebraMap S T)))).inv
      _).mp
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (_root_.Algebra.pushoutExtendedIdealMap S T B C)
  have he : ⇑(_root_.Algebra.pushoutExtendedIdealMap S T B C) =
      ⇑(_root_.Algebra.quotientFlatPushoutIdealAddEquiv R S T A B C hsurj) :=
    funext (_root_.Algebra.pushoutExtendedIdealMap_eq_addEquiv R S T A B C hsurj)
  rw [he]
  exact (_root_.Algebra.quotientFlatPushoutIdealAddEquiv R S T A B C hsurj).bijective

end ModuleCat
end

section
namespace ModuleCat

open scoped ChangeOfRings

theorem flatQuotient_categorical_spectralExtendedIdealMap_isIso
    {R S T A B C : CommRingCat.{u}} (p : R ⟶ S) (i : S ⟶ T) (q : R ⟶ A)
    (b : S ⟶ B) (p' : A ⟶ B) (a : T ⟶ C) (i' : B ⟶ C)
    (H : IsPushout p q b p') (H' : IsPushout i b a i')
    (hsurj : Function.Surjective i) (hflat : (p ≫ i).hom.Flat) :
    IsIso (ModuleCat.extendedKernelMap i i' b a H'.w) := by
  let : Algebra R S := p.hom.toAlgebra
  let : Algebra R T := (p ≫ i).hom.toAlgebra
  let : Algebra R A := q.hom.toAlgebra
  let : Algebra R B := (p ≫ b).hom.toAlgebra
  let : Algebra R C := (p ≫ b ≫ i').hom.toAlgebra
  let : Algebra S T := i.hom.toAlgebra
  let : Algebra S B := b.hom.toAlgebra
  let : Algebra S C := (b ≫ i').hom.toAlgebra
  let : Algebra A B := p'.hom.toAlgebra
  let : Algebra A C := (p' ≫ i').hom.toAlgebra
  let : Algebra B C := i'.hom.toAlgebra
  let : Algebra T C := a.hom.toAlgebra
  let : IsScalarTower R S T := .of_algebraMap_eq (fun _ ↦ rfl)
  let : IsScalarTower R S B := .of_algebraMap_eq (fun _ ↦ rfl)
  let : IsScalarTower R A B := .of_algebraMap_eq
    (fun r ↦ ConcreteCategory.congr_hom H.w r)
  let : IsScalarTower R T C := .of_algebraMap_eq (fun r ↦
    (ConcreteCategory.congr_hom H'.w (p r)).symm)
  let : IsScalarTower R A C := .of_algebraMap_eq (fun r ↦
    congrArg i' (ConcreteCategory.congr_hom H.w r))
  let : IsScalarTower A B C := .of_algebraMap_eq (fun _ ↦ rfl)
  let : IsScalarTower S B C := .of_algebraMap_eq (fun _ ↦ rfl)
  let : IsScalarTower S T C := .of_algebraMap_eq (fun s ↦
    (ConcreteCategory.congr_hom H'.w s).symm)
  let : Algebra.IsPushout R A S B := CommRingCat.isPushout_iff_isPushout.mp H.flip
  let : Algebra.IsPushout R A T C :=
    CommRingCat.isPushout_iff_isPushout.mp (H.paste_horiz H').flip
  let : Module.Flat R T := hflat
  exact ModuleCat.flatQuotient_pushout_spectralExtendedIdealMap_isIso R S T A B C hsurj

end ModuleCat
end

section
namespace Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A quotient-flat principal kernel extends to the principal kernel of the
actual scalar-extended quotient map. -/
theorem flatQuotient_principal_tensorKernel
    (R A B K : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R K] [Module.Flat R B]
    (hsurj : Function.Surjective (algebraMap A B)) (a : A)
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {a}) :
    RingHom.ker (_root_.Algebra.tensorQuotientMap R A B K) =
      Ideal.span {((1 : K) ⊗ₜ[R] a)} := by
  change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id K K)
    (IsScalarTower.toAlgHom R A B)) = _
  rw [← _root_.Algebra.flatQuotient_extendedIdealInclusion_range R A B K hsurj]
  rw [_root_.Algebra.extendedIdealInclusion, LinearMap.range_comp]
  change Submodule.map (AlgebraTensorModule.rid A (K ⊗[R] A) (K ⊗[R] A)).toLinearMap
    ((RingHom.ker (algebraMap A B)).baseChange (K ⊗[R] A)) = _
  rw [hker]
  change Submodule.map _ ((Submodule.span A {a}).baseChange (K ⊗[R] A)) = _
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_singleton, Set.image_singleton]
  congr 1
  ext
  simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_eq_includeRight]

end Algebra
end
