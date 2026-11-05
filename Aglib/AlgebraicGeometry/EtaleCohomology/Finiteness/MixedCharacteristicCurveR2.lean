/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.RelativeCurveCyclicR2
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstructibleCyclicPrimary

/-! # Prime-power curve R2 without an invertibility hypothesis

On each actual integral affine immersion the prime either vanishes, where
existing Artin--Schreier constructibility applies, or becomes invertible on
the actual nonempty principal open. Existing generic-property stratification
then gives the original higher image on the whole Noetherian base. The invertible
branch uses the actual degree-two curve producer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Actual cyclic prime-power R2 is constructible for a proper relative curve
on a Noetherian base, including mixed characteristic. -/
theorem cyclicPrimePowerHigherDirectImage_R2_isConstructible_of_relativeCurve
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (p : ℕ) (hp : p.Prime) (r : ℕ) :
    Constructible.IsConstructible ((higherDirectImage f 2).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) X)) := by
  classical
  have hn : 0 < p ^ r := pow_pos hp.pos _
  let F := (higherDirectImage f 2).obj
    (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) X)
  obtain ⟨t, ht⟩ := Constructible.exists_finitePartition_of_generic_open
    (fun {Y} (i : Y ⟶ S) => IsFiniteLocallyConstant ((inverseImage i).obj F))
    (fun Y _ _ _ i _ => by
      let A := Γ(Y, ⊤)
      let : IsNoetherianRing A :=
        IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
      let k : Spec (.of A) ⟶ S := Y.isoSpec.inv ≫ i
      let fY := pullback.snd f k
      have finish (Z : Scheme.{u}) [IsAffine Z] [IsIntegral Z]
          (a : Z ⟶ Y) [IsOpenImmersion a]
          (h : Constructible.IsConstructible ((inverseImage (a ≫ i)).obj F)) :
          ∃ (V : Scheme.{u}) (b : V ⟶ Y), IsOpenImmersion b ∧ Nonempty V ∧
            IsFiniteLocallyConstant ((inverseImage (b ≫ i)).obj F) := by
        obtain ⟨V, j, hj, hV, hloc⟩ := Constructible.exists_nonempty_finiteLocallyConstant_open h
        let : IsOpenImmersion j := hj
        refine ⟨V, j ≫ a, inferInstance, hV, ?_⟩
        have hh := (isFiniteLocallyConstant_iff_of_iso
          ((inverseImageComp (a ≫ i) j).app F)).mpr hloc
        simpa only [Category.assoc] using hh
      by_cases hzero : (p : A) = 0
      · have hspec : (p : Γ(Spec (.of A), ⊤)) = 0 := by
          simpa only [map_natCast, map_zero] using
            congrArg (Scheme.ΓSpecIso (.of A)).inv.hom hzero
        have hAS := cyclicPrimePowerHigherDirectImage_isConstructible fY p hp hspec r 2
        apply finish (Spec (.of A)) Y.isoSpec.inv
        exact (Constructible.isConstructible_iff_of_iso
          (cyclicHigherDirectImageBaseChangeIso f k (p ^ r) hn 2)).mpr hAS
      · let B := Localization.Away (p : A)
        let : IsDomain B := IsLocalization.Away.isDomain B hzero
        let : IsNoetherianRing B :=
          IsLocalization.isNoetherianRing (Submonoid.powers (p : A)) B inferInstance
        let j : Spec (.of B) ⟶ Spec (.of A) := Spec.algebraMap A B
        let : IsOpenImmersion j := IsOpenImmersion.of_isLocalization (p : A)
        let fB := pullback.snd fY j
        have hdimB : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (η : Spec (.of Ω) ⟶ Spec (.of B)),
            topologicalKrullDim (pullback fB η : Scheme.{u}) ≤ 1 := by
          intro Ω _ _ η
          let e₁ := pullbackLeftPullbackSndIso fY j η
          let e₂ := pullbackLeftPullbackSndIso f k (η ≫ j)
          exact (IsHomeomorph.topologicalKrullDim_eq _
            (e₁ ≪≫ e₂).hom.homeomorph.isHomeomorph).trans_le
              (hdim Ω ((η ≫ j) ≫ k))
        have hpB : IsUnit (p : B) := by
          simpa only [map_natCast] using
            (IsLocalization.Away.algebraMap_isUnit (S := B) (p : A))
        have hunit : IsUnit ((p ^ r : ℕ) : Γ(Spec (.of B), ⊤)) := by
          let σ : B →+* Γ(Spec (.of B), ⊤) := (Scheme.ΓSpecIso (.of B)).inv.hom
          have hσ : σ (p : B) = (p : Γ(Spec (.of B), ⊤)) := _root_.map_natCast σ p
          have hpΓ : IsUnit (p : Γ(Spec (.of B), ⊤)) := hσ ▸ (hpB.map σ)
          simpa only [Nat.cast_pow] using hpΓ.pow r
        have hB := cyclicHigherDirectImage_R2_isConstructible_of_relativeCurve
          fB hdimB (p ^ r) hn hunit
        have hj : Constructible.IsConstructible ((inverseImage j).obj
            ((higherDirectImage fY 2).obj
              (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) (pullback f k)))) :=
          (Constructible.isConstructible_iff_of_iso
            (cyclicHigherDirectImageBaseChangeIso fY j (p ^ r) hn 2)).mpr hB
        have hwhole : Constructible.IsConstructible ((inverseImage (j ≫ k)).obj F) :=
          (Constructible.isConstructible_iff_of_iso ((inverseImageComp k j).app F)).mpr
            ((Constructible.isConstructible_iff_of_iso ((inverseImage j).mapIso
              (cyclicHigherDirectImageBaseChangeIso f k (p ^ r) hn 2))).mpr hj)
        apply finish (Spec (.of B)) (j ≫ Y.isoSpec.inv)
        simpa only [k, Category.assoc] using hwhole)
  exact Constructible.isConstructible_of_partition
    { toFiniteLocallyClosedPartition := t, locally_constant := ht }

end AlgebraicGeometry.Scheme.EtaleCohomology
