/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.UnitAffineComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.UnitBaseChangeScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.UnitPullbackCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineUnitFrobenius

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

/-- The original affine comparison equation for an arbitrary additive coefficient
endomorphism, before the coefficient or section values are specialized. -/
def AffineCohomologyCoefficientValues
    {T : CommRingCat.{u}} {X S : Scheme.{u}}
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (j : Spec T ⟶ S) [Etale j] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
    (g : additiveCoefficient X M ⟶ additiveCoefficient X M)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]
    (x y : (moduleSpecΓFunctor (R := T)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) : Prop :=
  let a := Limits.pullback.snd j f
  @Eq (Sheaf.H.{eY} ((inverseImage a).obj (additiveCoefficient X M)) q)
    (higherDirectImageAffineSectionsEquiv.{u, eY} f j M q y)
    (Sheaf.H.map ((inverseImage a).map g) q
      (higherDirectImageAffineSectionsEquiv.{u, eY} f j M q x))

/-- The complete original Frobenius equation on two actual pullback sections.
The affine algebra and literal-test consumers retain this same proposition. -/
def AffineCohomologyFrobenius
    {R T : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [QuasiCompact f] [QuasiSeparated f]
    (j : Spec T ⟶ Spec R) [Etale j] (q p : ℕ) (hp : p.Prime)
    (hR : (p : R) = 0)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]
    (x y : (moduleSpecΓFunctor (R := T)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf)))) : Prop :=
  AffineCohomologyCoefficientValues.{u, eY} f j
    (SheafOfModules.unit X.ringCatSheaf) q
    (unitFrobenius X p hp (higherDirectImage_primeCast_source f p hR)) x y

/-- Cancel the actual unit comparison and its full original Frobenius square
before substituting geometric comparison values. -/
private theorem originalUnitPullback_frobenius
    {X Y : Scheme.{u}} (a : Y ⟶ X) [Etale a] (q p : ℕ)
    (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    {x y : Sheaf.H.{eY} ((inverseImage a).obj
      (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf))) q}
    (hxy :
      Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).hom) q
        (Sheaf.H.map (additiveCoefficientPullback a
          (SheafOfModules.unit X.ringCatSheaf)) q y) =
      Sheaf.H.map (unitFrobenius Y p hp hY) q
        (Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).hom) q
          (Sheaf.H.map (additiveCoefficientPullback a
            (SheafOfModules.unit X.ringCatSheaf)) q x))) :
    y = Sheaf.H.map ((inverseImage a).map (unitFrobenius X p hp hX)) q x := by
  have hf := unitFrobenius_inverseImage_cohomology.{u, eY} a q p hp hX hY x
  exact unitPullbackCohomology_injective.{u, eY} a q (hxy.trans hf.symm)

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

/-- The actual affine semilinear coefficient action intertwines with original
geometric Frobenius under the original affine-test cohomology comparison. -/
theorem higherDirectImageAffineSectionsEquiv_affineFrobenius
    (x : (moduleSpecΓFunctor (R := CommRingCat.of B)).obj
      ((Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A B) : CommRingCat.of A ⟶ CommRingCat.of B))).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf)))) :
    let j := Spec.map (CommRingCat.ofHom (algebraMap A B) : CommRingCat.of A ⟶ CommRingCat.of B)
    let O := SheafOfModules.unit X.ringCatSheaf
    let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj O
    let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
      (higherDirectImageFrobenius.{u, eX} f q p hp hA)
    AffineCohomologyFrobenius.{u, eY} f j q p hp hA x
      ((Ψ.hom.app (op (Scheme.Etale.mk j)) (ULift.up x)).down) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let j := Spec.map φ
  let a := Limits.pullback.snd j f
  let b := Limits.pullback.fst j f
  let hB : (p : CommRingCat.of B) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A B) hA
  let hX := higherDirectImage_primeCast_source f p hA
  let hY := higherDirectImage_primeCast_source b p hB
  have hc := higherDirectImageAffineSectionsEquiv_unit_affineFrobenius.{u, eX, eY}
    f q B p hp hA x
  have hfinal := originalUnitPullback_frobenius a q p hp hX hY hc
  dsimp only [a, j, φ] at hfinal
  dsimp only [AffineCohomologyFrobenius, AffineCohomologyCoefficientValues]
  exact hfinal

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
