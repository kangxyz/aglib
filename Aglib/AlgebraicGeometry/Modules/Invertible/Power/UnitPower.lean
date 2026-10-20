/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.UnitDescent
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.PullbackNaturality
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.UnitPower` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`cfc70a8787ec9ab2cfbb74c96b7940660d0ca167308132aea15805441a1deec4`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle pullbackLineBundle tensorPowerLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap pullbackTensorMap_leftUnit tensorSheaf tensorSheafIso tensorSheafLeftUnit
    tensorSheafLeftUnit_tmul tensorSheafMap tensorSheafMap_comp tensorSheafMap_tmul tensorSheafUnit)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual structure-module tensor powers and normalization

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The unit bundle is the actual structure-module sheaf. Its tensor powers are
normalized to O by recursive canonical left-unit maps, including the actual
free-module level zero. Positive scalar automorphisms induce the literal
nth-power scalar. Unit normalization commutes with the canonical power
pullback isomorphisms, using the actual tensor/unit comparison square.
The actual power-isomorphism functor obeys identity, composition and inverse
on arbitrary schemes; these unrestricted proofs avoid unused geometric
hypotheses inherited by the earlier geometric-scope support lemmas.
No descent, torsor-classification, cohomology or other standard family is
an assumption of this file. The fixed UnitDescent unitObject is used only
as the actual O-module with its proved local rank-one property.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower
open PowerPullback TrivializedPower
universe u

/-- The structure module as the actual locally free rank-one bundle. -/
def unitLineBundle (X : Scheme.{u}) : LineBundle X :=
  AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.toLineBundle X
      (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.unitObject X)

/-- Canonical multiplication O^{tensor n} ≅ O, including the actual free level zero. -/
def unitPowerIso (X : Scheme.{u}) :
    (n : ℕ) → (tensorPowerLineBundle X (unitLineBundle X) n).val ≅
      SheafOfModules.unit X.ringCatSheaf
  | 0 => freeUnitIso X
  | n + 1 => tensorSheafLeftUnit X (tensorPowerLineBundle X (unitLineBundle X) n).val ≪≫
      unitPowerIso X n

@[reassoc] theorem tensorSheafLeftUnit_naturality (X : Scheme.{u}) {M N : X.Modules}
    (φ : M ⟶ N) :
    tensorSheafMap X (𝟙 (SheafOfModules.unit X.ringCatSheaf)) φ ≫
      (tensorSheafLeftUnit X N).hom = (tensorSheafLeftUnit X M).hom ≫ φ := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r m
  change (tensorSheafLeftUnit X N).hom.val.app U
      ((tensorSheafMap X (𝟙 (SheafOfModules.unit X.ringCatSheaf)) φ).val.app U
        ((tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) M).app U (r ⊗ₜ m))) =
    φ.val.app U ((tensorSheafLeftUnit X M).hom.val.app U
      ((tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) M).app U (r ⊗ₜ m)))
  rw [tensorSheafMap_tmul, tensorSheafLeftUnit_tmul, tensorSheafLeftUnit_tmul]
  exact ((φ.val.app U).hom.map_smul r m).symm

/-- Scalar frames induce the literal nth-power scalar under unit normalization. -/
theorem unitPowerIso_scalar (X : Scheme.{u}) (a : Γ(X, ⊤)ˣ) (n : ℕ) :
    (powerIso X (L := unitLineBundle X) (M := unitLineBundle X)
      (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X
          (SheafOfModules.unit X.ringCatSheaf) a) n).hom ≫
        (unitPowerIso X n).hom =
      (unitPowerIso X n).hom ≫ scalarMap X (SheafOfModules.unit X.ringCatSheaf) (a ^ n : Γ(X,
          ⊤)ˣ) := by
  erw [AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.powerIso_scalar X
      (unitLineBundle X) a n]
  exact AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarMap_naturality X
      (a ^ n : Γ(X, ⊤)ˣ) (unitPowerIso X n).hom

/-- Unit normalization commutes with the actual tensor-power pullback map. -/
theorem unitPowerIso_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (pullbackPowerIso f (unitLineBundle Y) n).hom ≫
      (powerIso X (L := pullbackLineBundle f (unitLineBundle Y)) (M := unitLineBundle X)
        (pullbackUnitIso f) n).hom ≫ (unitPowerIso X n).hom =
    (Scheme.Modules.pullback f).map (unitPowerIso Y n).hom ≫ (pullbackUnitIso f).hom := by
  induction n with
  | zero =>
    change ((Scheme.Modules.pullback f).map (freeUnitIso Y).hom ≫
      (pullbackUnitIso f).hom ≫ (freeUnitIso X).inv) ≫ 𝟙 _ ≫ (freeUnitIso X).hom = _
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  | succ n ih =>
    change (pullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf)
        (tensorPowerLineBundle Y (unitLineBundle Y) n).val ≫
      tensorSheafMap X (𝟙 _) (pullbackPowerIso f (unitLineBundle Y) n).hom) ≫
      tensorSheafMap X (pullbackUnitIso f).hom
        (powerIso X (L := pullbackLineBundle f (unitLineBundle Y)) (M := unitLineBundle X)
          (pullbackUnitIso f) n).hom ≫
      (tensorSheafLeftUnit X (tensorPowerLineBundle X (unitLineBundle X) n).val).hom ≫
        (unitPowerIso X n).hom =
      (Scheme.Modules.pullback f).map
        ((tensorSheafLeftUnit Y (tensorPowerLineBundle Y (unitLineBundle Y) n).val).hom ≫
          (unitPowerIso Y n).hom) ≫ (pullbackUnitIso f).hom
    rw [Category.assoc, Scheme.Modules.tensorSheafMap_comp_assoc,
        Category.id_comp]
    have hfactor := tensorSheafMap_comp X (pullbackUnitIso f).hom
      (𝟙 ((Scheme.Modules.pullback f).obj (tensorPowerLineBundle Y (unitLineBundle Y) n).val))
      (𝟙 (SheafOfModules.unit X.ringCatSheaf))
      ((pullbackPowerIso f (unitLineBundle Y) n).hom ≫
        (powerIso X (L := pullbackLineBundle f (unitLineBundle Y)) (M := unitLineBundle X)
          (pullbackUnitIso f) n).hom)
    simp only [Category.comp_id, Category.id_comp] at hfactor
    rw [← hfactor]
    simp only [Category.assoc]
    rw [tensorSheafLeftUnit_naturality_assoc]
    have hu := congrArg (fun v => v ≫
      ((pullbackPowerIso f (unitLineBundle Y) n).hom ≫
        (powerIso X (L := pullbackLineBundle f (unitLineBundle Y)) (M := unitLineBundle X)
          (pullbackUnitIso f) n).hom) ≫ (unitPowerIso X n).hom)
      (pullbackTensorMap_leftUnit f (tensorPowerLineBundle Y (unitLineBundle Y) n).val)
    simp only [Category.assoc] at hu
    erw [hu]
    simp only [Category.assoc, CategoryTheory.Functor.map_comp]
    rw [ih]

variable (X : Scheme.{u})

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

theorem powerIso_refl (L : LineBundle X) (n : ℕ) :
    powerIso X (Iso.refl L.val) n = Iso.refl _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (congrArg (tensorSheafIso X (Iso.refl L.val)) ih).trans
      (tensorSheafIso_refl X _ _)

theorem powerIso_trans {L M N : LineBundle X} (e : L.val ≅ M.val) (g : M.val ≅ N.val)
    (n : ℕ) :
    powerIso X (e ≪≫ g) n = powerIso X e n ≪≫ powerIso X g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tensorSheafIso X (e ≪≫ g) (powerIso X (e ≪≫ g) n) = _
    rw [ih, tensorSheafIso_trans]
    rfl

theorem powerIso_symm {L M : LineBundle X} (e : L.val ≅ M.val) (n : ℕ) :
    powerIso X e.symm n = (powerIso X e n).symm := by
  apply Iso.ext
  apply (cancel_mono (powerIso X e n).hom).mp
  rw [Iso.symm_hom, Iso.inv_hom_id]
  have h := congrArg Iso.hom (powerIso_trans X e.symm e n)
  simpa only [Iso.symm_self_id, powerIso_refl, Iso.refl_hom, Iso.trans_hom] using h.symm


end AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower
