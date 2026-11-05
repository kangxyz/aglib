/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.GenericCurveCyclicR2
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.RelativeCurveCyclicR1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.GenericProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.GenericLocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Bounded
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ZMod
public import Aglib.Topology.KrullDimension.Surjective
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! # Constructibility of invertible cyclic R2 for proper relative curves

The existing Noetherian generic-property partition is applied to the original
higher image. Generic cyclic R2 and actual proper exchange provide its genuine
nonempty finite-locally-constant opens. No new Noetherian induction or external
constructibility certificate is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- The original cyclic second higher direct image is constructible on a
Noetherian base when the positive level is invertible and every geometric
fibre of the proper morphism has dimension at most one. -/
theorem cyclicHigherDirectImage_R2_isConstructible_of_relativeCurve
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(S, ⊤))) :
    Constructible.IsConstructible ((higherDirectImage f 2).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X)) := by
  classical
  let F := (higherDirectImage f 2).obj
    (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X)
  obtain ⟨t, ht⟩ := Constructible.exists_finitePartition_of_generic_open
    (fun {Y} (i : Y ⟶ S) => IsFiniteLocallyConstant ((inverseImage i).obj F))
    (fun Y _ _ _ i _ => by
      let A := Γ(Y, ⊤)
      let : IsNoetherianRing A :=
        IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
      let K := FractionRing A
      let k : Spec (.of A) ⟶ S := Y.isoSpec.inv ≫ i
      let fY := pullback.snd f k
      have hA : IsUnit (n : A) := by simpa only [map_natCast] using hinv.map i.appTop.hom
      have hdimY : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (η : Spec (.of Ω) ⟶ Spec (.of A)),
          topologicalKrullDim (pullback fY η : Scheme.{u}) ≤ 1 := by
        intro Ω _ _ η
        let e := pullbackLeftPullbackSndIso f k η
        exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans_le
          (hdim Ω (η ≫ k))
      obtain ⟨r, hr, d, hd, hR⟩ := exists_generic_curve_cyclic_R2 A K fY hdimY n hn hA
      let Ar := Localization.Away r
      let : IsDomain Ar := IsLocalization.Away.isDomain Ar hr
      let U : (Spec (.of Ar)).Opens := PrimeSpectrum.basicOpen d
      let : IsAffine U.toScheme := by
        change IsAffineOpen (X := Spec (.of Ar)) (PrimeSpectrum.basicOpen d)
        exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of Ar) d
      let : Nonempty U.toScheme := by
        refine ⟨⟨⟨⊥, inferInstance⟩, ?_⟩⟩
        change d ∉ (⊥ : Ideal Ar)
        simpa only [Ideal.mem_bot] using hd
      let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
      let j : U.toScheme ⟶ Spec (.of A) := U.ι ≫ Spec.algebraMap A Ar
      let : IsOpenImmersion (Spec.algebraMap A Ar) := IsOpenImmersion.of_isLocalization r
      let : IsOpenImmersion j := inferInstance
      have hR' : Constructible.IsConstructible ((inverseImage j).obj
          ((higherDirectImage fY 2).obj
            (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (pullback f k)))) :=
        (Constructible.isConstructible_iff_of_iso
          (cyclicHigherDirectImageBaseChangeIso fY j n hn 2)).mpr hR
      have hjF : Constructible.IsConstructible ((inverseImage (j ≫ k)).obj F) :=
        (Constructible.isConstructible_iff_of_iso ((inverseImageComp k j).app F)).mpr
          ((Constructible.isConstructible_iff_of_iso
            ((inverseImage j).mapIso (cyclicHigherDirectImageBaseChangeIso f k n hn 2))).mpr hR')
      obtain ⟨V, a, ha, hV, hloc⟩ :=
        Constructible.exists_nonempty_finiteLocallyConstant_open hjF
      let : IsOpenImmersion a := ha
      let b : V ⟶ Y := a ≫ j ≫ Y.isoSpec.inv
      refine ⟨V, b, inferInstance, hV, ?_⟩
      have hh := (isFiniteLocallyConstant_iff_of_iso
        ((inverseImageComp (j ≫ k) a).app F)).mpr hloc
      simpa only [b, k, Category.assoc] using hh)
  exact Constructible.isConstructible_of_partition
    { toFiniteLocallyClosedPartition := t, locally_constant := ht }

end AlgebraicGeometry.Scheme.EtaleCohomology
