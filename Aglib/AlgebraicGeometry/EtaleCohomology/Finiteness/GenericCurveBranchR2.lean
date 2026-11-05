/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Normalization.GenericFiniteCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PointedCurveCyclicDegreeTwo
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Closure

/-! # Cyclic R2 on the actual branches of the generic finite cover

The integral affine coefficient base, smooth curve maps, and sections are taken
from the original cover. Point branches use finite higher-image vanishing.
No branch constructibility or coefficient coordinate is supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

namespace AlgebraicGeometry.Scheme.OverField.Curve.Normalization

universe u

attribute [local instance] hasSheafifyLarge

/-- Each original branch has constructible literal cyclic second higher image.
The point and positive-dimensional cases retain the same structural map. -/
theorem GenericFiniteCoverData.isConstructible_branch_cyclic_R2
    {R K : Type u} [CommRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K]
    {s : Finset (AlgebraicClosure K)} [Algebra R (FiniteField.stage K s)]
    {X : Scheme.{u}} {p : X ⟶ Spec (.of R)}
    (D : GenericFiniteCoverData R K s p)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : R)) (i : D.I) :
    IsConstructible ((higherDirectImage (D.M i).f 2).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (D.M i).X)) := by
  classical
  let T := genericCoverBase D.B D.r D.d
  let : IsAffine T := D.baseAffine
  let : IsIntegral T := D.baseIntegral
  let : IsNoetherianRing (Localization.Away D.r) :=
    IsLocalization.isNoetherianRing (Submonoid.powers D.r) _ inferInstance
  let U : (Spec (.of (Localization.Away D.r))).Opens := PrimeSpectrum.basicOpen D.d
  let β := genericCoverBaseMap D.B D.r
  let fT : T ⟶ U := pullback.snd β U.ι
  let : IsFinite fT := D.finite_base
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian fT
  let : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  let b : T ⟶ Spec (.of R) := pullback.fst β U.ι ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away (algebraMap R D.B D.r))))
  have hunit : IsUnit (n : Γ(T, ⊤)) := by
    have hR := hinv.map (Scheme.ΓSpecIso (.of R)).inv.hom
    simpa only [map_natCast] using hR.map b.appTop.hom
  by_cases hi : i ∈ D.P
  · let : IsIso (D.M i).f := D.point_M ⟨i, hi⟩
    let : HasDerivedCategory (AbelianSheaf.{u, u + 1} (D.M i).X) :=
      HasDerivedCategory.standard _
    let : HasDerivedCategory (AbelianSheaf.{u, u + 1} (Spec Γ(T, ⊤))) :=
      HasDerivedCategory.standard _
    exact isConstructible_of_isFiniteLocallyConstant
      (FiniteColimits.isFiniteLocallyConstant_of_isZero
        (EtaleCohomology.Finite.isZero_higherDirectImage_obj_of_isFinite
          (D.M i).f _ 2 (by decide)))
  · let j : {i : D.I // i ∉ D.P} := ⟨i, hi⟩
    let : IsProper (D.M i).f := D.proper_M i
    let : SmoothOfRelativeDimension 1 (D.M i).f := D.smooth_M j
    let : GeometricallyIntegral (D.M i).f := D.integral_M j
    let : GeometricallyConnected (D.M i).f := by
      constructor
      intro L _ t Z fst snd H
      let : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral t fst snd H
      infer_instance
    have hbase : IsUnit (n : Γ(Spec Γ(T, ⊤), ⊤)) := by
      simpa only [map_natCast] using
        hunit.map (Scheme.ΓSpecIso (CommRingCat.of Γ(T, ⊤))).inv.hom
    exact isConstructible_cyclicHigherDirectImage_two_pointedCurve
      (D.M i).f (D.sections i) (D.sections_w i) n hn hbase

end AlgebraicGeometry.Scheme.OverField.Curve.Normalization
