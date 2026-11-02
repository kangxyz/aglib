/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.UnitAffineComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.UnitBaseChangeScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineFrobenius

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

/-- Compose the full intertwining and both original value comparisons before
specializing an operator at a concrete input. -/
private theorem semiconj_of_comparison_values
    {V : Type*} {H : Type*} {Φ : V → V} {x y : V} (hxy : y = Φ x)
    (E : V → H) (F : H → H) (hEF : Function.Semiconj E Φ F)
    {cx cy : H} (hx : cx = E x) (hy : cy = E y) : cy = F cx :=
  hy.trans ((congrArg E hxy).trans ((hEF x).trans (congrArg F hx).symm))

/-- The complete original value law over a variable source scheme and its
actual structural arrow, before a fibre-product source is substituted. -/
private theorem originalFrobenius_comparison_values
    {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [QuasiCompact f] [QuasiSeparated f]
    (q p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} X)]
    {x y : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))}
    (hxy : y = higherDirectImageFrobenius.{u, eY} f q p hp hR x)
    {cx cy : Sheaf.H.{eY} (additiveCoefficient X
      (SheafOfModules.unit X.ringCatSheaf)) q}
    (hx : cx = higherDirectImageUnitCohomologyEquiv.{u, eY} f q x)
    (hy : cy = higherDirectImageUnitCohomologyEquiv.{u, eY} f q y) :
    cy = Sheaf.H.map
      (unitFrobenius X p hp (higherDirectImage_primeCast_source f p hR)) q cx :=
  semiconj_of_comparison_values hxy
    (higherDirectImageUnitCohomologyEquiv.{u, eY} f q)
    (Sheaf.H.map (unitFrobenius X p hp (higherDirectImage_primeCast_source f p hR)) q)
    (higherDirectImageFrobenius_apply.{u, eY} f q p hp hR) hx hy

/-- Compose the original relative unit comparison and the genuine cohomological
Frobenius law before specializing either affine-section input. -/
private theorem originalAffineUnit_frobenius
    {R T : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [QuasiCompact f] [QuasiSeparated f]
    (j : Spec T ⟶ Spec R) [Etale j] (q p : ℕ) (hp : p.Prime)
    (hT : (p : T) = 0)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]
    (x y : (moduleSpecΓFunctor (R := T)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf))))
    (hxy : AffineUnitBaseChangeFrobenius.{u, eY} f j q p hp hT x y) :
    let Y := Limits.pullback j f
    let a := Limits.pullback.snd j f
    let b := Limits.pullback.fst j f
    let O := SheafOfModules.unit X.ringCatSheaf
    let c := fun z => Sheaf.H.map
      (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).hom) q
      (Sheaf.H.map (additiveCoefficientPullback a O) q
        (higherDirectImageAffineSectionsEquiv.{u, eY} f j O q z))
    c y = Sheaf.H.map
      (unitFrobenius Y p hp (higherDirectImage_primeCast_source b p hT)) q (c x) := by
  have hl := higherDirectImageAffineSectionsEquiv_unit.{u, eY} f j q y
  have hr := higherDirectImageAffineSectionsEquiv_unit.{u, eY} f j q x
  dsimp only at hl hr
  dsimp only [AffineUnitBaseChangeFrobenius] at hxy
  have hfinal := originalFrobenius_comparison_values _ q p hp hT hxy hr hl
  exact hfinal

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
theorem higherDirectImageAffineSectionsEquiv_unit_affineFrobenius
    (x : (moduleSpecΓFunctor (R := CommRingCat.of B)).obj
      ((Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A B) : CommRingCat.of A ⟶ CommRingCat.of B))).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf)))) :
    let j := Spec.map (CommRingCat.ofHom (algebraMap A B) : CommRingCat.of A ⟶ CommRingCat.of B)
    let a := Limits.pullback.snd j f
    let O := SheafOfModules.unit X.ringCatSheaf
    let Q := ((Scheme.Modules.pushforward f).rightDerived q).obj O
    let Ψ := affineFrobenius (CommRingCat.of A) Q p hp hA
      (higherDirectImageFrobenius.{u, eX} f q p hp hA)
    let b := Limits.pullback.fst j f
    let hB : (p : CommRingCat.of B) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (algebraMap A B) hA
    let hY := higherDirectImage_primeCast_source b p hB
    @Eq (Sheaf.H.{eY} (additiveCoefficient (Limits.pullback j f)
      (SheafOfModules.unit (Limits.pullback j f).ringCatSheaf)) q)
      (Sheaf.H.map (additiveCoefficientMap (Limits.pullback j f)
        (Scheme.Modules.pullbackUnitIso a).hom) q
        (Sheaf.H.map (additiveCoefficientPullback a O) q
          (higherDirectImageAffineSectionsEquiv.{u, eY} f j O q
            ((Ψ.hom.app (op (Scheme.Etale.mk j)) (ULift.up x)).down))))
      (Sheaf.H.map (unitFrobenius (Limits.pullback j f) p hp hY) q
        (Sheaf.H.map (additiveCoefficientMap (Limits.pullback j f)
          (Scheme.Modules.pullbackUnitIso a).hom) q
          (Sheaf.H.map (additiveCoefficientPullback a O) q
            (higherDirectImageAffineSectionsEquiv.{u, eY} f j O q x)))) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let j := Spec.map φ
  let hB : (p : CommRingCat.of B) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A B) hA
  have hs := higherDirectImageFrobenius_affineFrobenius.{u, eX, eY} f q B p hp hA x
  have hfinal := originalAffineUnit_frobenius.{u, eY} f j q p hp hB x _ hs
  dsimp only [j, φ] at hfinal
  dsimp only
  exact hfinal

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
