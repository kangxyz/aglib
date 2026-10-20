/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Torsion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.TrivializedPower` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`96337e8eca9a58e2b71fc22aedae1ce0684a757ff417b2530447570486f3123f`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle PicardGroup classOf classOf_tensorPower classOf_trivial
    class_eq_iff tensorLineBundle tensorLineBundleAssociator tensorPowerLineBundle
        trivialLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules
  (tensorSheaf tensorSheafBraiding tensorSheafIso tensorSheafLeftUnit tensorSheafMap)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual line bundles with a chosen tensor-power trivialization

C3 geometric algebraic Kummer classification, K2-018
`lem:k2018-geometric-exact-order`, frozen basis `7f86e4a`.
`Pair X n` consists of an actual line bundle L and an actual module-sheaf
isomorphism tau : L^n ≅ O. Its equivalence relation requires an actual
line-bundle isomorphism whose nth tensor power preserves tau. It is not the
quotient that merely remembers existence of some trivialization.

Tensor product uses the proved actual associators and braiding. Actual
global-unit scalar automorphisms, their tensor/power law, and the description
of automorphisms of O by global units are constructed. If every global unit
has an nth root, a root of the mismatch unit adjusts any underlying
line-bundle isomorphism to an isomorphism of the specified pairs. This proves
classification by actual Picard[n]; the root hypothesis is discharged from
algebraically closed constants and actual global-function surjectivity at
positive n. The transported group law is proved to be literal tensor product.
Level one is explicitly subsingleton.

Composing the independently proved algebraic-pair/Picard classification gives
a genuine additive equivalence from the divisor/function quotient to these
actual pair classes. On every representative it is proved to be
(D,f) ↦ (O(D), multiplication by f), with div(f)=nD. Actual tensor pairs
correspond to adding divisors and multiplying functions. The general units/n
exact sequence remains in KummerExactness; the pair-classification application
here has the assigned algebraically closed geometric scope.

No pair-classification, scalar-automorphism, Picard-equivalence or H1 theorem
is assumed. Source correspondence: Stacks Section 03PK, Lemma 59.28.5.
There is no etale H1 claim in this module. In later root-torsor applications,
normalized sections satisfy f*s^n=1, while trivializations phi:L→O with
phi^n=tau give a^n=f. Their inversion/sign comparison remains explicit C4 work.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower
universe u
variable (X : Scheme.{u})

/-- An actual line bundle with a specified trivialization of its nth tensor power. -/
structure Pair (n : ℕ) where
  lineBundle : LineBundle X
  trivialization : (tensorPowerLineBundle X lineBundle n).val ≅ SheafOfModules.unit X.ringCatSheaf

/-- Tensor-power transport of an actual line-bundle isomorphism. -/
def powerIso {L M : LineBundle X} (e : L.val ≅ M.val) :
    (n : ℕ) → (tensorPowerLineBundle X L n).val ≅ (tensorPowerLineBundle X M n).val
  | 0 => Iso.refl _
  | n + 1 => tensorSheafIso X e (powerIso e n)

/-- Pair isomorphisms preserve the chosen power trivialization, not just its existence. -/
def Isomorphic {n : ℕ} (P Q : Pair X n) : Prop :=
  ∃ e : P.lineBundle.val ≅ Q.lineBundle.val,
    (powerIso X e n).hom ≫ Q.trivialization.hom = P.trivialization.hom

theorem pair_class_nsmul {n : ℕ} (P : Pair X n) : n • classOf X P.lineBundle = 0 := by
  rw [← classOf_tensorPower]
  apply Quotient.sound
  exact ⟨P.trivialization ≪≫ (CategoryTheory.Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩

theorem tensorSheafIso_refl (M N : SheafOfModules.{u} X.ringCatSheaf) :
    tensorSheafIso X (Iso.refl M) (Iso.refl N) = Iso.refl (tensorSheaf X M N) := by
  apply Iso.ext
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 M.val) (𝟙 N.val)) = 𝟙 _
  have hh : PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 M.val) (𝟙 N.val) = 𝟙 _ := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl
  rw [hh, CategoryTheory.Functor.map_id]

theorem tensorSheafIso_trans {M M' M'' N N' N'' : SheafOfModules.{u} X.ringCatSheaf}
    (a : M ≅ M') (b : N ≅ N') (c : M' ≅ M'') (d : N' ≅ N'') :
    tensorSheafIso X (a ≪≫ c) (b ≪≫ d) = tensorSheafIso X a b ≪≫ tensorSheafIso X c d := by
  apply Iso.ext
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (a.hom.val ≫ c.hom.val) (b.hom.val ≫
          d.hom.val)) =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom a.hom.val b.hom.val) ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom c.hom.val d.hom.val)
  rw [← Functor.map_comp]
  congr 1
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

@[simp] theorem powerIso_refl (L : LineBundle X) (n : ℕ) :
    powerIso X (Iso.refl L.val) n = Iso.refl _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (congrArg (tensorSheafIso X (Iso.refl L.val)) ih).trans
      (tensorSheafIso_refl X _ _)

@[simp] theorem powerIso_trans {L M N : LineBundle X} (e : L.val ≅ M.val) (g : M.val ≅ N.val)
    (n : ℕ) :
    powerIso X (e ≪≫ g) n = powerIso X e n ≪≫ powerIso X g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tensorSheafIso X (e ≪≫ g) (powerIso X (e ≪≫ g) n) = _
    rw [ih, tensorSheafIso_trans]
    rfl

@[simp] theorem powerIso_symm {L M : LineBundle X} (e : L.val ≅ M.val) (n : ℕ) :
    powerIso X e.symm n = (powerIso X e n).symm := by
  apply Iso.ext
  apply (cancel_mono (powerIso X e n).hom).mp
  rw [Iso.symm_hom, Iso.inv_hom_id]
  have h := congrArg Iso.hom (powerIso_trans X e.symm e n)
  simpa only [Iso.symm_self_id, powerIso_refl, Iso.refl_hom, Iso.trans_hom] using h.symm

instance pairSetoid (n : ℕ) : Setoid (Pair X n) where
  r := Isomorphic X
  iseqv := {
    refl P := ⟨Iso.refl _, by simp⟩
    symm := by
      rintro P Q ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [powerIso_symm, Iso.symm_hom, ← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    trans := by
      rintro P Q R ⟨e, he⟩ ⟨g, hg⟩
      refine ⟨e ≪≫ g, ?_⟩
      rw [powerIso_trans, Iso.trans_hom, Category.assoc, hg, he] }

/-- Isomorphism classes of actual power-trivialized line bundles. -/
abbrev Classes (n : ℕ) := Quotient (pairSetoid X n)

def forgetClass {n : ℕ} (P : Classes X n) : PicardGroup X :=
  Quotient.liftOn P (fun P => classOf X P.lineBundle) (by
    rintro P Q ⟨e, _⟩
    exact Quotient.sound ⟨e⟩)

theorem forgetClass_nsmul {n : ℕ} (P : Classes X n) : n • forgetClass X P = 0 := by
  induction P using Quotient.inductionOn with
  | h P => exact pair_class_nsmul X P

def toPicardTorsion (n : ℕ) (P : Classes X n) :
    AlgebraicGeometry.Scheme.Modules.Invertible.Torsion.picardTorsion X n :=
  ⟨forgetClass X P, forgetClass_nsmul X P⟩

theorem toPicardTorsion_surjective (n : ℕ) : Function.Surjective (toPicardTorsion X n) := by
  intro c
  let L : LineBundle X := Quotient.out c.val
  have hL : classOf X L = c.val := Quotient.out_eq c.val
  have h0 : classOf X (tensorPowerLineBundle X L n) = classOf X (trivialLineBundle X) := by
    rw [classOf_tensorPower, hL, classOf_trivial]
    exact c.property
  obtain ⟨e⟩ := (class_eq_iff X _ _).mp h0
  let P : Pair X n := ⟨L, e ≪≫ CategoryTheory.Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)⟩
  exact ⟨Quotient.mk _ P, Subtype.ext hL⟩

/-- The actual middle-factor exchange, with canonical associators and braiding. -/
def tensorInterchangeIso (L M N P : LineBundle X) :
    tensorSheaf X (tensorSheaf X L.val M.val) (tensorSheaf X N.val P.val) ≅
      tensorSheaf X (tensorSheaf X L.val N.val) (tensorSheaf X M.val P.val) :=
  tensorLineBundleAssociator X L M (tensorLineBundle X N P) ≪≫
  tensorSheafIso X (Iso.refl L.val) (tensorLineBundleAssociator X M N P).symm ≪≫
  tensorSheafIso X (Iso.refl L.val)
    (tensorSheafIso X (tensorSheafBraiding X M.val N.val) (Iso.refl P.val)) ≪≫
  tensorSheafIso X (Iso.refl L.val) (tensorLineBundleAssociator X N M P) ≪≫
  (tensorLineBundleAssociator X L N (tensorLineBundle X M P)).symm

/-- Canonical distribution of tensor powers over actual tensor product. -/
def powerTensorIso (L M : LineBundle X) :
    (n : ℕ) → (tensorPowerLineBundle X (tensorLineBundle X L M) n).val ≅
      tensorSheaf X (tensorPowerLineBundle X L n).val (tensorPowerLineBundle X M n).val
  | 0 =>
    (tensorSheafLeftUnit X (trivialLineBundle X).val).symm ≪≫
      tensorSheafIso X (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm (Iso.refl _)
  | n + 1 =>
    tensorSheafIso X (Iso.refl (tensorSheaf X L.val M.val)) (powerTensorIso L M n) ≪≫
      tensorInterchangeIso X L M (tensorPowerLineBundle X L n) (tensorPowerLineBundle X M n)

/-- Literal tensor product of actual power-trivialized line bundles. -/
def tensor {n : ℕ} (P Q : Pair X n) : Pair X n where
  lineBundle := tensorLineBundle X P.lineBundle Q.lineBundle
  trivialization := powerTensorIso X P.lineBundle Q.lineBundle n ≪≫
    tensorSheafIso X P.trivialization Q.trivialization ≪≫
      tensorSheafLeftUnit X (SheafOfModules.unit X.ringCatSheaf)

@[simp] theorem tensor_class {n : ℕ} (P Q : Pair X n) :
    classOf X (tensor X P Q).lineBundle = classOf X P.lineBundle + classOf X Q.lineBundle := rfl

open Opposite
/-- Multiplication by an actual global regular section on a module sheaf. -/
def scalarMap (M : SheafOfModules.{u} X.ringCatSheaf) (a : Γ(X, ⊤)) : M ⟶ M where
  val := {
    app U := ModuleCat.ofHom {
      toFun m := X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a • m
      map_add' m n := smul_add _ _ _
      map_smul' r m := by
        change X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a •
          ((show Γ(X, U.unop) from r) • m) =
          (show Γ(X, U.unop) from r) • (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a • m)
        rw [← mul_smul, ← mul_smul, mul_comm] }
    naturality := by
      intro U V i
      ext m
      change X.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op a • M.val.map i m =
        M.val.map i (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a • m)
      rw [M.val.map_smul]
      change X.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op a • M.val.map i m =
        X.presheaf.map i (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a) • M.val.map i m
      rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
      rfl }

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

/-- The unit of global functions determined by an actual structure-module automorphism. -/
def unitOfIso (e : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    Γ(X, ⊤)ˣ where
  val := e.hom.val.app (op ⊤) (1 : Γ(X, ⊤))
  inv := e.inv.val.app (op ⊤) (1 : Γ(X, ⊤))
  val_inv := by
    have he := congrArg (fun φ : SheafOfModules.unit X.ringCatSheaf ⟶ _ => φ.val.app (op ⊤) (1
        : Γ(X, ⊤))) e.hom_inv_id
    change e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) at he
    have hl := (e.inv.val.app (op ⊤)).hom.map_smul (e.hom.val.app (op ⊤) (1 : Γ(X, ⊤))) (1 :
        Γ(X, ⊤))
    change e.inv.val.app (op ⊤) (_ * 1) = _ * _ at hl
    rw [mul_one] at hl
    exact hl.symm.trans he
  inv_val := by
    have he := congrArg (fun φ : SheafOfModules.unit X.ringCatSheaf ⟶ _ => φ.val.app (op ⊤) (1
        : Γ(X, ⊤))) e.inv_hom_id
    change e.hom.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) at he
    have hl := (e.hom.val.app (op ⊤)).hom.map_smul (e.inv.val.app (op ⊤) (1 : Γ(X, ⊤))) (1 :
        Γ(X, ⊤))
    change e.hom.val.app (op ⊤) (_ * 1) = _ * _ at hl
    rw [mul_one] at hl
    exact hl.symm.trans he

@[simp] theorem unitOfIso_hom (e : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit
    X.ringCatSheaf) :
    e.hom = scalarMap X (SheafOfModules.unit X.ringCatSheaf) (unitOfIso X e) :=
  unit_hom_eq_scalar X e.hom

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


variable [IsIntegral X]

theorem globalUnits_pow_surjective {k : Type u} [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (.of k))
    (hconstants : Function.Surjective (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom))
    (n : ℕ) (hn : 0 < n) : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n) := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  intro a
  let c := (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom)
  obtain ⟨z, hz⟩ := hconstants (a : Γ(X, ⊤))
  have hz0 : z ≠ 0 := by
    intro he
    subst z
    have h0 : (a : Γ(X, ⊤)) = 0 := by simpa using hz.symm
    exact a.ne_zero h0
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z hn
  have hw0 : w ≠ 0 := by
    intro he
    subst w
    rw [zero_pow (ne_of_gt hn)] at hw
    exact hz0 hw.symm
  refine ⟨Units.map c.toMonoidHom (Units.mk0 w hw0), ?_⟩
  apply Units.ext
  change (c w) ^ n = (a : Γ(X, ⊤))
  rw [← map_pow, hw]
  exact hz

omit [IsIntegral X] in
/-- A genuine nth root of the global mismatch unit adjusts an actual line-bundle
isomorphism so that it preserves the specified power trivializations. -/
theorem isomorphic_of_class_eq [IsIntegral X] {n : ℕ}
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n))
    {P Q : Pair X n} (hPQ : classOf X P.lineBundle = classOf X Q.lineBundle) :
    Isomorphic X P Q := by
  obtain ⟨e⟩ := (class_eq_iff X _ _).mp hPQ
  let α := P.trivialization.symm ≪≫ powerIso X e n ≪≫ Q.trivialization
  let a := unitOfIso X α
  obtain ⟨b, hb⟩ := hroot a⁻¹
  change b ^ n = a⁻¹ at hb
  have he : (powerIso X e n).hom ≫ Q.trivialization.hom =
      P.trivialization.hom ≫ scalarMap X (SheafOfModules.unit X.ringCatSheaf) a := by
    rw [← unitOfIso_hom X α]
    dsimp only [α, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine ⟨e ≪≫ scalarIso X Q.lineBundle.val b, ?_⟩
  rw [powerIso_trans, Iso.trans_hom, powerIso_scalar]
  change ((powerIso X e n).hom ≫ scalarMap X _ ↑(b ^ n)) ≫ Q.trivialization.hom = _
  rw [Category.assoc, scalarMap_naturality, ← Category.assoc, he,
    Category.assoc, scalarMap_mul, hb, Units.mul_inv, scalarMap_one, Category.comp_id]

theorem forgetClass_injective {n : ℕ}
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) :
    Function.Injective (forgetClass X (n := n)) := by
  intro P Q hPQ
  induction P using Quotient.inductionOn with
  | h P =>
    induction Q using Quotient.inductionOn with
    | h Q => exact Quotient.sound (isomorphic_of_class_eq X hroot hPQ)

/-- Actual pair classes classify actual Picard torsion when every global unit
has an nth root. This hypothesis is discharged over the geometric constants. -/
def picardTorsionEquiv (n : ℕ)
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) :
    Classes X n ≃ AlgebraicGeometry.Scheme.Modules.Invertible.Torsion.picardTorsion X n :=
  Equiv.ofBijective (toPicardTorsion X n)
    ⟨fun _ _ h => forgetClass_injective X hroot (congrArg Subtype.val h),
        toPicardTorsion_surjective X n⟩


/-- Level one of actual power-trivialized line bundles is trivial. -/
instance classesOneSubsingleton : Subsingleton (Classes X 1) where
  allEq P Q := by
    apply forgetClass_injective X (n := 1) (by intro a; exact ⟨a, pow_one a⟩)
    have hP := forgetClass_nsmul X P
    have hQ := forgetClass_nsmul X Q
    simpa only [one_nsmul] using hP.trans hQ.symm

/-- The group structure on actual pair classes, transported through the proved
classification. The next theorem identifies its addition with literal tensor. -/
abbrev classesAddCommGroup (n : ℕ)
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) : AddCommGroup (Classes X n) :=
  (picardTorsionEquiv X n hroot).addCommGroup

def picardTorsionAddEquiv (n : ℕ)
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) :
    letI := classesAddCommGroup X n hroot
    Classes X n ≃+ AlgebraicGeometry.Scheme.Modules.Invertible.Torsion.picardTorsion X n :=
  (picardTorsionEquiv X n hroot).addEquiv

theorem class_tensor (n : ℕ)
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) (P Q : Pair X n) :
    letI := classesAddCommGroup X n hroot
    (Quotient.mk (pairSetoid X n) (tensor X P Q) : Classes X n) =
      Quotient.mk (pairSetoid X n) P + Quotient.mk (pairSetoid X n) Q := by
  let := classesAddCommGroup X n hroot
  apply (picardTorsionAddEquiv X n hroot).injective
  rw [map_add]
  apply Subtype.ext
  exact tensor_class X P Q

end AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower
