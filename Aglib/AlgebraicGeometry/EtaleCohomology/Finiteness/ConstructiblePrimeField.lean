/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.GenericPrimeField
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PrimeFieldBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.GenericProperty

/-! # Constructibility of original proper prime-field higher images

Actual proper base change and the nonzero principal Artin--Schreier shrink
supply the generic step of the original Noetherian finite partition.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- On a Noetherian characteristic-p base the actual higher direct image of
the constant prime field has an actual finite constructible partition. -/
theorem exists_primeFieldHigherDirectImage_constructiblePartition
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) (q : ℕ) :
    Nonempty (Constructible.ConstructiblePartition
      ((higherDirectImage f q).obj (primeFieldSheaf X p))) := by
  let F := (higherDirectImage f q).obj (primeFieldSheaf X p)
  obtain ⟨t, ht⟩ := Constructible.exists_finitePartition_of_generic_open
    (fun {Y} (i : Y ⟶ S) => IsFiniteLocallyConstant ((inverseImage i).obj F))
    (fun Y _ _ _ i _ => by
      let A := Γ(Y, ⊤)
      have : IsNoetherianRing A :=
        IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
      have hA : (p : A) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg i.appTop.hom hS
      let k : Spec (CommRingCat.of A) ⟶ S := Y.isoSpec.inv ≫ i
      let fY := pullback.snd f k
      obtain ⟨r, hr, R, hR, hAR, hloc, het, hfinite⟩ :=
        exists_restricted_primeFieldHigherDirectImage_finiteLocallyConstant A fY q p hp hA
      let j : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A) :=
        Spec.map (CommRingCat.ofHom (algebraMap A R))
      have : IsOpenImmersion j := by
        exact IsOpenImmersion.of_isLocalization r
      have : IsDomain R := IsLocalization.Away.isDomain R hr
      let a : Spec (CommRingCat.of R) ⟶ Y := j ≫ Y.isoSpec.inv
      refine ⟨_, a, inferInstance, inferInstance, ?_⟩
      have he := primeFieldHigherDirectImageBaseChangeIso f k p hp q
      have hfinite' : IsFiniteLocallyConstant
          ((inverseImage j).obj ((higherDirectImage fY q).obj
            (primeFieldSheaf (pullback f k) p))) :=
        (isFiniteLocallyConstant_iff_of_iso ((inverseImageEtaleIso j).app _)).mpr hfinite
      have hfinite'' := (isFiniteLocallyConstant_iff_of_iso
        ((inverseImage j).mapIso he)).mpr hfinite'
      have hh := (isFiniteLocallyConstant_iff_of_iso ((inverseImageComp k j).app F)).mpr
        hfinite''
      simpa only [a, k, Category.assoc] using hh)
  exact ⟨{ toFiniteLocallyClosedPartition := t, locally_constant := ht }⟩

/-- Proper prime-field higher direct images are constructible over every
locally Noetherian base on which the prime vanishes. -/
theorem primeFieldHigherDirectImage_isConstructible
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f]
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) (q : ℕ) :
    Constructible.IsConstructible ((higherDirectImage f q).obj (primeFieldSheaf X p)) := by
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsNoetherian U.1.toScheme := ⟨⟩
  have hU : (p : Γ(U.1.toScheme, ⊤)) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg U.1.ι.appTop.hom hS
  obtain ⟨t⟩ := exists_primeFieldHigherDirectImage_constructiblePartition
    (pullback.snd f U.1.ι) p hp hU q
  exact ⟨t.ofIso (primeFieldHigherDirectImageBaseChangeIso f U.1.ι p hp q).symm⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
