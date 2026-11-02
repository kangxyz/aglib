/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.GenericCurveBranchR1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.HigherImageCoproduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.FiniteSurjectiveDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperConstantDegreeZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherOuterComposition
public import Aglib.AlgebraicGeometry.Curves.Normalization.GenericFiniteCoverComposite

/-! # Generic cyclic R1 for the original proper curve family

The finite field cover and its spread are selected internally. The original
finite coproduct, followed by the actual finite base map, is one finite
surjection onto the original restricted family. Only the degree-zero image of
the actual unit cokernel is used. All constant-coefficient pullbacks use the
original constant inverse-image comparison, not definitional identifications.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve.Normalization

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

private theorem generic_cover_cyclic_R1
    {R K : Type u} [CommRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K]
    {s : Finset (AlgebraicClosure K)} [Algebra R (FiniteField.stage K s)]
    {X : Scheme.{u}} {p : X ⟶ Spec (.of R)} [IsProper p]
    (D : GenericFiniteCoverData R K s p)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : R)) :
    let U : (Spec (.of (Localization.Away D.r))).Opens := PrimeSpectrum.basicOpen D.d
    let u := U.ι ≫ Spec.algebraMap R (Localization.Away D.r)
    Constructible.IsConstructible ((higherDirectImage (pullback.snd p u) 1).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (pullback p u))) := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : Finite D.I := D.finiteI
  let T := genericCoverBase D.B D.r D.d
  let : IsAffine T := D.baseAffine
  let : IsNoetherianRing (Localization.Away D.r) :=
    IsLocalization.isNoetherianRing (Submonoid.powers D.r) _ inferInstance
  let U : (Spec (.of (Localization.Away D.r))).Opens := PrimeSpectrum.basicOpen D.d
  let : IsAffine U.toScheme := by
    change IsAffineOpen (X := Spec (.of (Localization.Away D.r)))
      (PrimeSpectrum.basicOpen D.d)
    exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (Localization.Away D.r)) D.d
  let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
  let : IsNoetherian U.toScheme := ⟨⟩
  let u : U.toScheme ⟶ Spec (.of R) := U.ι ≫ Spec.algebraMap R (Localization.Away D.r)
  let β := genericCoverBaseMap D.B D.r
  let b : Spec Γ(T, ⊤) ⟶ U := T.isoSpec.inv ≫ pullback.snd β U.ι
  let : IsFinite (pullback.snd β U.ι) := D.finite_base
  let : IsFinite b := inferInstanceAs (IsFinite (T.isoSpec.inv ≫ pullback.snd β U.ι))
  let XU := pullback p u
  let f : XU ⟶ U := pullback.snd p u
  let : IsProper f := inferInstance
  let : IsLocallyNoetherian XU := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace XU := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian XU := ⟨⟩
  let Y := fun i : D.I => (D.M i).X
  let g : (∐ Y) ⟶ Spec Γ(T, ⊤) := Sigma.desc fun i => (D.M i).f
  let value := ConstantFinite.value (ULift.{u} (ZMod n))
  let FY := ConstantFinite.coefficient (ULift.{u} (ZMod n)) (∐ Y)
  have hbranches : ∀ i, Constructible.IsConstructible
      ((higherDirectImage (D.M i).f 1).obj ((inverseImage (Sigma.ι Y i)).obj FY)) := by
    intro i
    exact (Constructible.isConstructible_iff_of_iso
      ((higherDirectImage (D.M i).f 1).mapIso
        ((inverseImageConstantIso (Sigma.ι Y i)).app value))).mpr
      (D.isConstructible_branch_cyclic_R1 n hn hinv i)
  have hg : Constructible.IsConstructible ((higherDirectImage g 1).obj FY) :=
    higherDirectImage_isConstructible_of_finiteCoproduct Y (fun i => (D.M i).f)
      FY 1 hbranches
  have hgb : Constructible.IsConstructible ((higherDirectImage (g ≫ b) 1).obj FY) :=
    (Constructible.isConstructible_iff_of_iso
      ((Finite.higherDirectImageFiniteOuterIso b g 1).app FY)).mpr
      (Finite.isConstructible_directImage_of_isNoetherian b hg)
  obtain ⟨k, _, _, _, _, hfinite, hsurj, hcomp⟩ := D.exists_composite_cover
  let c : (∐ Y) ⟶ XU := (Sigma.desc fun i => (D.arrows i).hom.left) ≫ k
  let : IsFinite c := hfinite
  let : Surjective c := hsurj
  let F := ConstantFinite.coefficient (ULift.{u} (ZMod n)) XU
  have hF : Constructible.IsConstructible F := Constructible.isConstructible_constant XU value
  have hc : Constructible.IsConstructible ((higherDirectImage (c ≫ f) 1).obj
      ((inverseImage c).obj F)) := by
    have hconst : Constructible.IsConstructible ((higherDirectImage (c ≫ f) 1).obj FY) := by
      rw [show c ≫ f = g ≫ b from hcomp]
      exact hgb
    exact (Constructible.isConstructible_iff_of_iso
      ((higherDirectImage (c ≫ f) 1).mapIso ((inverseImageConstantIso c).app value))).mpr hconst
  have hQ := isConstructible_cokernel_finite_unit c hF
  have hQ0 : Constructible.IsConstructible ((higherDirectImage f 0).obj
      (cokernel ((inverseImageAdjunction c).unit.app F))) :=
    (Constructible.isConstructible_iff_of_iso
      ((directImage f).rightDerivedZeroIsoSelf.app _)).mpr
      (isConstructible_properDirectImage f hQ)
  exact higherDirectImage_isConstructible_succ_of_finiteSurjective f c F 0 hQ0 hc

/-- Over an actual nonempty iterated principal base open, the original proper
family of generic dimension at most one has constructible cyclic R1. The
finite cover and every branch proof are produced internally. -/
theorem exists_generic_curve_cyclic_R1
    (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    (hd : topologicalKrullDim (pullback p (Spec.algebraMap R K) : Scheme.{u}) ≤ 1)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : R)) :
    ∃ r : R, r ≠ 0 ∧ ∃ d : Localization.Away r, d ≠ 0 ∧
      (let U : (Spec (.of (Localization.Away r))).Opens := PrimeSpectrum.basicOpen d
       let u := U.ι ≫ Spec.algebraMap R (Localization.Away r)
       Constructible.IsConstructible ((higherDirectImage (pullback.snd p u) 1).obj
         (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (pullback p u)))) := by
  classical
  obtain ⟨s, hD⟩ := exists_generic_finite_cover R K p hd
  let : Algebra R (FiniteField.stage K s) := (FiniteField.stage K s).algebra'
  obtain ⟨D⟩ := hD
  exact ⟨D.r, D.r_ne_zero, D.d, D.d_ne_zero, generic_cover_cyclic_R1 D n hn hinv⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
