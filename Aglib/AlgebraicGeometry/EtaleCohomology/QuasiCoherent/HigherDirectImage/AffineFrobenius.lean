/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.UnitAffineComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.UnitBaseChangeScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineFrobeniusTensor
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.FrobeniusAdditive

/-! # Original affine higher-image Frobenius comparison

The original affine semilinear coefficient map agrees with original geometric
Frobenius under the actual relative comparison, on all affine-test sections.
The native tensor comparison and its surjectivity extend the scalar-unit law.
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

/-- The original complete base-change Frobenius equation on two actual
pulled-back higher-image sections. Both producers and unit consumers retain
this same formula rather than expanding its original derived maps separately. -/
def AffineUnitBaseChangeFrobenius
    {R T : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [QuasiCompact f] [QuasiSeparated f]
    (j : Spec T ⟶ Spec R) [Etale j] (q p : ℕ) (hp : p.Prime)
    (hT : (p : T) = 0)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]
    (x y : (moduleSpecΓFunctor (R := T)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf)))) : Prop :=
  let a := Limits.pullback.snd j f
  let b := Limits.pullback.fst j f
  let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
  let D := (moduleSpecΓFunctor (R := T)).map
    (((Scheme.Modules.pushforward b).rightDerived q).map
      (Scheme.Modules.pullbackUnitIso a).hom)
  let C := (moduleSpecΓFunctor (R := T)).map
    ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app
      (SheafOfModules.unit X.ringCatSheaf))
  @Eq ((moduleSpecΓFunctor (R := T)).obj
    (((Scheme.Modules.pushforward b).rightDerived q).obj
      (SheafOfModules.unit (Limits.pullback j f).ringCatSheaf)))
    (D (C y)) (higherDirectImageFrobenius.{u, eY} b q p hp hT (D (C x)))

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

/-- The unchanged affine coefficient operator commutes with the native flat
base-change and derived-unit maps on every actual pullback section. -/
theorem higherDirectImageFrobenius_affineFrobenius
    (x : (moduleSpecΓFunctor (R := CommRingCat.of B)).obj
      ((Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A B) : CommRingCat.of A ⟶ CommRingCat.of B))).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf)))) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
    let j := Spec.map φ
    let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf)
    let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
      (higherDirectImageFrobenius.{u, eX} f q p hp hA)
    let hB : (p : CommRingCat.of B) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (algebraMap A B) hA
    AffineUnitBaseChangeFrobenius.{u, eY} f j q p hp hB x
      ((Ψ.hom.app (op (Scheme.Etale.mk j)) (ULift.up x)).down) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let j := Spec.map φ
  let Y := Limits.pullback j f
  let a := Limits.pullback.snd j f
  let b := Limits.pullback.fst j f
  let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let Q : (Spec (CommRingCat.of A)).Modules := ((Scheme.Modules.pushforward f).rightDerived q).obj O
  let V := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj
    ((Scheme.Modules.pullback j).obj Q)
  let W := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj
    (((Scheme.Modules.pushforward b).rightDerived q).obj
      (SheafOfModules.unit (Limits.pullback j f).ringCatSheaf))
  let Φ : moduleSpecΓFunctor.obj Q →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
      moduleSpecΓFunctor.obj Q := higherDirectImageFrobenius.{u, eX} f q p hp hA
  let hB : (p : CommRingCat.of B) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A B) hA
  let Φ' : W →+ W := (higherDirectImageFrobenius.{u, eY} b q p hp hB).toAddMonoidHom
  let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA Φ
  let ψ : V →+ V := AddEquiv.ulift.toAddMonoidHom.comp
    (((Ψ.hom.app (op (Scheme.Etale.mk j))).hom).comp
      AddEquiv.ulift.symm.toAddMonoidHom)
  let D := (moduleSpecΓFunctor (R := CommRingCat.of B)).map
    (((Scheme.Modules.pushforward b).rightDerived q).map (Scheme.Modules.pullbackUnitIso a).hom)
  let C := (moduleSpecΓFunctor (R := CommRingCat.of B)).map
    ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app O)
  let d : V →+ W := D.hom.toAddMonoidHom.comp C.hom.toAddMonoidHom
  let e : B ⊗[A] moduleSpecΓFunctor.obj Q →+ V := tensorSectionsAddHom A Q B
  let L : B ⊗[A] moduleSpecΓFunctor.obj Q →+ W := (d.comp ψ).comp e
  let t : V →+ W := Φ'.comp d
  let R : B ⊗[A] moduleSpecΓFunctor.obj Q →+ W := t.comp e
  have hd_eval (z : V) : d z = D (C z) := rfl
  have hL_eval (z) : L z = d (ψ (e z)) := rfl
  have hR_eval (z) : R z = Φ' (d (e z)) := rfl
  have ht_eval (z) : t z = Φ' (d z) := rfl
  have hψ_eval (z : V) : ψ z =
      (Ψ.hom.app (op (Scheme.Etale.mk j)) (ULift.up z)).down := rfl
  have he_eval (z) : e z = (specTensorSectionsIso A Q B).hom z := rfl
  have hgen (r : B) (m : moduleSpecΓFunctor.obj Q) :
      L (r ⊗ₜ[A] m) = R (r ⊗ₜ[A] m) := by
    have hpure := higherDirectImageFrobenius_affineFrobenius_tmul.{u, eX, eY}
      f q B p hp hA r m
    have hproj := higherDirectImageFrobenius_toAddMonoidHom_apply.{u, eY}
      b q p hp hB (D (C (e (r ⊗ₜ[A] m))))
    have h₀ := (hL_eval (r ⊗ₜ[A] m)).trans (hd_eval (ψ (e (r ⊗ₜ[A] m))))
    have h₁ := h₀.trans
      (congrArg (fun z : V => D (C z)) (hψ_eval (e (r ⊗ₜ[A] m))))
    have h₂ := h₁.trans hpure
    have h₂' : L (r ⊗ₜ[A] m) =
        higherDirectImageFrobenius.{u, eY} b q p hp hB (D (C (e (r ⊗ₜ[A] m)))) := by
      convert h₂ using 1
      conv_lhs =>
        arg -1
        arg -1
        arg -1
        rw [he_eval]
    have hproj' :
        higherDirectImageFrobenius.{u, eY} b q p hp hB (D (C (e (r ⊗ₜ[A] m)))) =
          Φ' (D (C (e (r ⊗ₜ[A] m)))) := by
      convert hproj.symm using 1
    have h₃ := h₂'.trans hproj'
    have h₄ := h₃.trans (congrArg Φ' (hd_eval (e (r ⊗ₜ[A] m))).symm)
    exact h₄.trans (hR_eval (r ⊗ₜ[A] m)).symm
  have hLR : L = R := by
    apply TensorProduct.addHom_ext
    intro r m
    convert hgen r m using 1
  have hes : Function.Surjective e := by
    intro z
    exact (ConcreteCategory.bijective_of_isIso (specTensorSectionsIso A Q B).hom).2 z
  have hd : d.comp ψ = t := (AddMonoidHom.cancel_right hes).mp hLR
  have hx := DFunLike.congr_fun hd x
  have heval := (AddMonoidHom.comp_apply d ψ x).symm.trans
    (hx.trans (ht_eval x))
  have hraw := (hd_eval (ψ x)).symm.trans
    (heval.trans (congrArg Φ' (hd_eval x)))
  have hevalΦ := higherDirectImageFrobenius_toAddMonoidHom_apply.{u, eY}
    b q p hp hB (D (C x))
  have hinput := congrArg (fun z : V => D (C z)) (hψ_eval x)
  have hfinal := hinput.symm.trans (hraw.trans hevalΦ)
  dsimp +instances only [Ψ, Φ, Φ', D, C, d, Q, O, W, V, Y, a, b, j, φ] at hfinal
  dsimp only [AffineUnitBaseChangeFrobenius]
  convert hfinal using 1

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
