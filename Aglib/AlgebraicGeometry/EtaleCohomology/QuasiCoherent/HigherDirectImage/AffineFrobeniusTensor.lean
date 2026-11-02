/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.QuasiCoherent
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.FrobeniusAdditive
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.UnitBaseChangeScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.Affine

/-! # Original affine higher-image Frobenius on pure tensors

The full native base-change square on original pure tensor sections is proved
before additive tensor extensionality or any relative cohomology transport.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct

universe u eX eY

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge Scheme.Modules.isQuasicoherent_unit
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
  (B : CommAlgCat.{u} A)
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap A B) : CommRingCat.of A ⟶ CommRingCat.of B))]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eY} (AbelianSheaf.{u, u + 1}
    (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A B) : CommRingCat.of A ⟶ CommRingCat.of B)) f))]

local instance :
    (((Scheme.Modules.pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent :=
  moduleHigherDirectImage_isQuasicoherent f (SheafOfModules.unit X.ringCatSheaf) q

/-- The literal affine Frobenius and original native base-change maps commute
on every original pure tensor section. -/
theorem higherDirectImageFrobenius_affineFrobenius_tmul
    (r : B) (m : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
    let j := Spec.map φ
    let a := Limits.pullback.snd j f
    let b := Limits.pullback.fst j f
    let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
    let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf)
    let x := (specTensorSectionsIso A Q B).hom (r ⊗ₜ[A] m)
    let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
      (higherDirectImageFrobenius.{u, eX} f q p hp hA)
    let D := (moduleSpecΓFunctor (R := CommRingCat.of B)).map
      (((Scheme.Modules.pushforward b).rightDerived q).map
        (Scheme.Modules.pullbackUnitIso a).hom)
    let C := (moduleSpecΓFunctor (R := CommRingCat.of B)).map
      ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app
        (SheafOfModules.unit X.ringCatSheaf))
    let hB : (p : CommRingCat.of B) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (algebraMap A B) hA
    @Eq ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj
      (((Scheme.Modules.pushforward b).rightDerived q).obj
        (SheafOfModules.unit (Limits.pullback j f).ringCatSheaf)))
      (D (C ((Ψ.hom.app (op (Scheme.Etale.mk j)) (ULift.up x)).down)))
      (higherDirectImageFrobenius.{u, eY} b q p hp hB (D (C x))) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let j := Spec.map φ
  let a := Limits.pullback.snd j f
  let b := Limits.pullback.fst j f
  let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let Q : (Spec (CommRingCat.of A)).Modules := ((Scheme.Modules.pushforward f).rightDerived q).obj O
  let V := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj
    ((Scheme.Modules.pullback j).obj Q)
  let D := (moduleSpecΓFunctor (R := CommRingCat.of B)).map
    (((Scheme.Modules.pushforward b).rightDerived q).map (Scheme.Modules.pullbackUnitIso a).hom)
  let C := (moduleSpecΓFunctor (R := CommRingCat.of B)).map
    ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app O)
  let Φ := higherDirectImageFrobenius.{u, eX} f q p hp hA
  let hB : (p : CommRingCat.of B) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A B) hA
  let η : moduleSpecΓFunctor.obj Q → V := fun s =>
    (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app Q).app ⊤) s
  have he (r : B) (s : moduleSpecΓFunctor.obj Q) :
      (specTensorSectionsIso A Q B).hom (r ⊗ₜ[A] s) = r • η s := by
    have ht : r ⊗ₜ[A] s = r • ((1 : B) ⊗ₜ[A] s) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul]
    exact congrArg (fun z : V => r • z) (specTensorSectionsIso_one_tmul A Q B s)
  have hψ := affineFrobenius_specTensor (CommRingCat.of A) Q p hp hA Φ B r m
  have hu := higherDirectImageFrobenius_flatBaseChange_smul_unit.{u, eX, eY}
    a b f φ h q p hp hA r m
  dsimp only at hu
  have h₁ := congrArg (fun z : V => D (C z)) hψ
  conv at hu =>
    lhs
    arg -1
    arg -1
    arg -1
    rw [← he r m]
  conv at hu =>
    rhs
    arg -1
    arg -1
    rw [← he (r ^ p) (Φ m)]
  have hfull := h₁.trans hu.symm
  dsimp +instances only [D, C, Φ, η, Q, O, V, a, b, j, φ] at hfull
  dsimp only
  convert hfull using 1

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
