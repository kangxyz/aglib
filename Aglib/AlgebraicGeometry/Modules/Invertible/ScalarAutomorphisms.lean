/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.TrivializedPower
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.ScalarAutomorphisms` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`2f16e39500b749c647952ad898ab8f49c95c6275daac32bd7ec8a6a86e000963`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle tensorPowerLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.Modules
  (tensorSheaf tensorSheafIso tensorSheafMap)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Scalar automorphisms on arbitrary schemes

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

This file uses the existing literal sectionwise `TrivializedPower.scalarMap`
and `unitOfIso`. It proves their identities for arbitrary schemes and module
sheaves, without the unused curve hypotheses inherited by the original
geometric-scope lemmas. The original geometric results remain valid.
Multiplication by an actual global unit is an actual module isomorphism;
every automorphism of O is uniquely of this form. Tensor powers have the
literal nth-power scalar, and pullback under the actual structure-module
comparison is pullback of the actual global section. These statements use
no retained standard theorem, descent, or cohomological classification.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms
universe u
variable (X : Scheme.{u})
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower
  (scalarMap unitOfIso powerIso)
@[simp] theorem scalarMap_app (M : SheafOfModules.{u} X.ringCatSheaf) (a : Γ(X, ⊤))
    (U : X.Opensᵒᵖ) (m : M.val.obj U) :
    (scalarMap X M a).val.app U m = X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a • m := rfl

@[simp] theorem scalarMap_one (M : SheafOfModules.{u} X.ringCatSheaf) : scalarMap X M 1 = 𝟙 M := by
  ext U m
  simp only [scalarMap_app, map_one, one_smul]
  rfl

@[reassoc] theorem scalarMap_mul (M : SheafOfModules.{u} X.ringCatSheaf) (a b : Γ(X, ⊤)) :
    scalarMap X M a ≫ scalarMap X M b = scalarMap X M (a * b) := by
  ext U m
  change X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op b •
      (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a • m) =
    X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op (a * b) • m
  rw [map_mul, ← mul_smul, mul_comm]

@[reassoc] theorem scalarMap_naturality {M N : SheafOfModules.{u} X.ringCatSheaf}
    (a : Γ(X, ⊤)) (φ : M ⟶ N) : scalarMap X M a ≫ φ = φ ≫ scalarMap X N a := by
  ext U m
  exact (φ.val.app U).hom.map_smul _ _

/-- Actual multiplication by a global unit, with its actual inverse. -/
def scalarIso (M : SheafOfModules.{u} X.ringCatSheaf) (a : Γ(X, ⊤)ˣ) : M ≅ M where
  hom := scalarMap X M a
  inv := scalarMap X M ↑a⁻¹
  hom_inv_id := by rw [scalarMap_mul, Units.mul_inv, scalarMap_one]
  inv_hom_id := by rw [scalarMap_mul, Units.inv_mul, scalarMap_one]

/-- A module-sheaf endomorphism of the structure module is multiplication by
its actual global value at one. -/
theorem unit_hom_eq_scalar (φ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit
    X.ringCatSheaf) :
    φ = scalarMap X (SheafOfModules.unit X.ringCatSheaf) (φ.val.app (op ⊤) (1 : Γ(X, ⊤))) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let a' : Γ(X, U.unop) := a
  let ψ : Γ(X, U.unop) →ₗ[Γ(X, U.unop)] Γ(X, U.unop) := (φ.val.app U).hom
  have hnat := PresheafOfModules.naturality_apply φ.val (homOfLE le_top : U.unop ⟶ ⊤).op (1 :
      Γ(X, ⊤))
  change ψ (X.presheaf.map _ (1 : Γ(X, ⊤))) =
    X.presheaf.map _ (φ.val.app (op ⊤) (1 : Γ(X, ⊤))) at hnat
  rw [map_one] at hnat
  change ψ a' = X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op
    (φ.val.app (op ⊤) (1 : Γ(X, ⊤))) * a'
  have hlin := ψ.map_smul a' (1 : Γ(X, U.unop))
  change ψ (a' * 1) = a' * ψ 1 at hlin
  rw [mul_one, hnat, mul_comm] at hlin
  exact hlin

@[simp] theorem unitOfIso_hom (e : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit
    X.ringCatSheaf) :
    e.hom = scalarMap X (SheafOfModules.unit X.ringCatSheaf) (unitOfIso X e) :=
  unit_hom_eq_scalar X e.hom

/-- Every actual automorphism of O is multiplication by its unique global unit. -/
def unitAutoEquiv (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) ≃ Γ(X, ⊤)ˣ where
  toFun := unitOfIso X
  invFun := scalarIso X (SheafOfModules.unit X.ringCatSheaf)
  left_inv e := by
    apply Iso.ext
    exact (unitOfIso_hom X e).symm
  right_inv a := by
    apply Units.ext
    change X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op (a : Γ(X, ⊤)) * 1 = a
    rw [mul_one]
    change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) (a : Γ(X, ⊤)) = a
    rw [CategoryTheory.Functor.map_id]
    rfl


theorem tensorSheafMap_scalar (M N : SheafOfModules.{u} X.ringCatSheaf) (a b : Γ(X, ⊤)) :
    tensorSheafMap X (scalarMap X M a) (scalarMap X N b) =
      scalarMap X (tensorSheaf X M N) (a * b) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv P
    (tensorSheaf X M N)).injective
  change η ≫ (tensorSheafMap X (scalarMap X M a) (scalarMap X N b)).val =
    η ≫ (scalarMap X (tensorSheaf X M N) (a * b)).val
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      (scalarMap X M a).val (scalarMap X N b).val)
  change _ = η ≫ (tensorSheafMap X (scalarMap X M a) (scalarMap X N b)).val at hn
  rw [← hn]
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change η.app U ((X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a • m) ⊗ₜ
    (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op b • n)) =
      X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op (a * b) • η.app U (m ⊗ₜ n)
  rw [TensorProduct.smul_tmul_smul, (η.app U).hom.map_smul, map_mul]

theorem powerIso_scalar (L : LineBundle X) (a : Γ(X, ⊤)ˣ) (n : ℕ) :
    powerIso X (scalarIso X L.val a) n = scalarIso X (tensorPowerLineBundle X L n).val (a ^ n) := by
  induction n with
  | zero =>
    apply Iso.ext
    change 𝟙 _ = scalarMap X _ ↑(a ^ 0)
    rw [pow_zero, Units.val_one, scalarMap_one]
  | succ n ih =>
    apply Iso.ext
    change (tensorSheafIso X (scalarIso X L.val a)
      (powerIso X (scalarIso X L.val a) n)).hom = _
    rw [ih]
    change tensorSheafMap X (scalarMap X L.val a)
      (scalarMap X (tensorPowerLineBundle X L n).val ↑(a ^ n)) =
      scalarMap X _ ↑(a ^ (n + 1))
    rw [tensorSheafMap_scalar, pow_succ', Units.val_mul]


/-- Scalar pullback under the actual structure-module comparison. -/
theorem pullback_scalar_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (scalarMap Y (SheafOfModules.unit Y.ringCatSheaf) a) ≫
      (pullbackUnitIso f).hom =
    (pullbackUnitIso f).hom ≫ scalarMap X (SheafOfModules.unit X.ringCatSheaf) (f.appTop a) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have hu := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (pullbackUnitIso f).hom = _ at hu
  rw [hu]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  let b' : Γ(Y, U.unop) := b
  change f.app U.unop (Y.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a * b') =
    X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U.unop ⟶ ⊤).op (f.appTop a) * f.app U.unop b'
  rw [map_mul]
  congr 1
  exact ConcreteCategory.congr_hom (f.toLRSHom.c.naturality (homOfLE le_top : U.unop ⟶ ⊤).op) a

end AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms
