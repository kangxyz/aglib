/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.GenericCurveCyclicR1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.GenericProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.GenericLocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Bounded
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ZMod
public import Aglib.Topology.KrullDimension.Surjective
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! # Constructibility of invertible cyclic R1 for proper relative curves

The existing Noetherian generic-property partition is applied to the original
higher image. Generic cyclic R1 and actual proper exchange provide its genuine
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

/-- Original bounded proper exchange with the same literal cyclic coefficient. -/
def cyclicHigherDirectImageBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) [IsProper f] (g : T ⟶ S)
    (n : ℕ) (hn : 0 < n) (q : ℕ) :
    (inverseImage g).obj ((higherDirectImage f q).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X)) ≅
    (higherDirectImage (pullback.snd f g) q).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (pullback f g)) := by
  let F := ConstantFinite.coefficient (ULift.{u} (ZMod n)) X
  have hk : n • 𝟙 F = 0 := by
    apply (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).nsmul_id_eq_zero_obj
    ext a
    exact ZModModule.char_nsmul_eq_zero n a.down.down
  let α := (higherBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
    (IsPullback.of_hasPullback f g).w.symm q).app F
  let : IsIso α := by
    simpa only [α, higherBaseChangeMapFromDerived_eq] using
      Proper.properHigherBaseChange_isIso_of_killed f (pullback.snd f g) g
        (pullback.fst f g) (IsPullback.of_hasPullback f g) n (Nat.ne_of_gt hn) F hk q
  exact asIso α ≪≫ (higherDirectImage (pullback.snd f g) q).mapIso
    ((inverseImageConstantIso (pullback.fst f g)).app
      (ConstantFinite.value (ULift.{u} (ZMod n))))

/-- The geometric dimension bound descends along the actual algebraic-closure fibre projection. -/
theorem relativeCurve_fieldFibre_dimension_le_one
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (K : Type u) [Field K] (η : Spec (.of K) ⟶ S) :
    topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1 := by
  let Ω := AlgebraicClosure K
  let a : Spec (.of Ω) ⟶ Spec (.of K) := Spec.algebraMap K Ω
  let p := pullback.snd f η
  let z := pullback.fst p a
  let : IsIntegralHom a := by
    change IsIntegralHom (Spec.map
      (CommRingCat.ofHom (algebraMap K Ω)))
    apply IsIntegralHom.SpecMap_iff.mpr
    exact algebraMap_isIntegral_iff.mpr inferInstance
  let : Surjective a := inferInstance
  let : IsIntegralHom z := inferInstanceAs (IsIntegralHom (pullback.fst p a))
  let : Surjective z := inferInstanceAs (Surjective (pullback.fst p a))
  have hz : topologicalKrullDim (pullback f η : Scheme.{u}) ≤
      topologicalKrullDim (pullback p a : Scheme.{u}) :=
    TopologicalSpace.topologicalKrullDim_le_of_isClosedMap_of_surjective z z.continuous
      z.isClosedMap z.surjective
  let e := pullbackLeftPullbackSndIso f η a
  exact hz.trans ((IsHomeomorph.topologicalKrullDim_eq _
    e.hom.homeomorph.isHomeomorph).trans_le (hdim Ω (a ≫ η)))

/-- The original cyclic first higher direct image is constructible on a
Noetherian base when the positive level is invertible and every geometric
fibre of the proper morphism has dimension at most one. -/
theorem cyclicHigherDirectImage_R1_isConstructible_of_relativeCurve
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(S, ⊤))) :
    Constructible.IsConstructible ((higherDirectImage f 1).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X)) := by
  classical
  let F := (higherDirectImage f 1).obj
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
      have hdY : topologicalKrullDim
          (pullback fY (Spec.algebraMap A K) : Scheme.{u}) ≤ 1 := by
        let e := pullbackLeftPullbackSndIso f k (Spec.algebraMap A K)
        exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans_le
          (relativeCurve_fieldFibre_dimension_le_one f hdim K (Spec.algebraMap A K ≫ k))
      obtain ⟨r, hr, d, hd, hR⟩ := exists_generic_curve_cyclic_R1 A K fY hdY n hn hA
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
          ((higherDirectImage fY 1).obj
            (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (pullback f k)))) :=
        (Constructible.isConstructible_iff_of_iso
          (cyclicHigherDirectImageBaseChangeIso fY j n hn 1)).mpr hR
      have hjF : Constructible.IsConstructible ((inverseImage (j ≫ k)).obj F) :=
        (Constructible.isConstructible_iff_of_iso ((inverseImageComp k j).app F)).mpr
          ((Constructible.isConstructible_iff_of_iso
            ((inverseImage j).mapIso (cyclicHigherDirectImageBaseChangeIso f k n hn 1))).mpr hR')
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
