/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.StalkInjectiveDimension
public import Aglib.RingTheory.Gorenstein.NormalQuotientCanonical

/-!
# Intrinsic Gorensteinness and the original canonical stalk

At each original point of a normal integral surface in the specified
projective embedding, finite self-injective dimension of its actual local
ring is equivalent to a frame of its actual canonical stalk. The original
polynomial quotient chart, coefficient-line frame, source-linear canonical
stalk comparison and open-stalk ring isomorphism supply the construction.

This is a pointwise statement. It neither defines Gorensteinness through a
canonical frame nor asserts a sheaf-local or global trivialization. No
later stalk is assumed complete or finite over the initial regular base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.FiniteSourceStalk

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] RingHomInvPair.of_ringEquiv

local instance canonicalStalkGorensteinDerived (B : Type u) [CommRing B] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} B) := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
  (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
  [IsDominant (i ≫ toSpec R ι)]
  (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι i).Finite)

include hX hXdim e hfin in
/-- Intrinsic finite self-injective dimension produces an actual frame of the
same original canonical stalk. The frame is chosen, not canonically normalized. -/
def normalSurfaceCanonicalStalkLinearEquivOfSelfInjectiveDimension
    (x : X) (d : ℕ)
    [HasInjectiveDimensionLE
      (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) d] :
    ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) ≃ₗ[
      X.presheaf.stalk x] X.presheaf.stalk x := by
  classical
  refine Classical.choice ?_
  let : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨_, r, _, hrX, hr2, _⟩ := normalSurface_localVanishing R ι i hX hXdim n e x
  obtain ⟨k, y, hy⟩ := normalSurface_exists_polynomialPoint R ι (i x)
  let P : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ k} R)
  let j := eulerPolynomialChart R ι k
  let C := closedImmersionAffineQuotientChart i P j
  obtain ⟨z, hz, _⟩ := C.exists_point x y hy.symm
  subst x
  let : IsOpenImmersion C.sourceMap := C.isOpenImmersion
  let : IsIso (C.sourceMap.stalkMap z) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp C.isOpenImmersion).2 z
  let S : CommRingCat.{u} := ambientRing C.ideal z
  let B : CommRingCat.{u} := sourceRing C.ideal z
  let eB := (asIso (C.sourceMap.stalkMap z)).commRingCatIsoToRingEquiv
  let : IsDomain (X.presheaf.stalk (C.sourceMap z)) := (hX _).1
  let : IsIntegrallyClosed (X.presheaf.stalk (C.sourceMap z)) := (hX _).2
  let : IsDomain B := eB.symm.toMulEquiv.isDomain _
  let : IsIntegrallyClosed B := IsIntegrallyClosed.of_equiv eB
  let : IsRegularLocalRing S := normalSurface_polynomialStalk_regular R ι k
    (imagePoint C.ideal z)
  have hrB : ringKrullDim B = (r : ℕ) :=
    (ringKrullDim_eq_of_ringEquiv eB).symm.trans hrX
  have hS : ringKrullDim S = ((n + r : ℕ) : ℕ) := by
    rw [normalSurfaceCanonicalQuotientStalk_dimension R ι i hX hXdim n e hfin P j C z,
      hrB, Nat.cast_add]
  let q := (stalkMap C.ideal z).hom
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk C.ideal))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective)
  have hq : Function.Surjective q :=
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk C.ideal))).stalkMap_surjective z
  let N := (moduleStalk (Spec P) (imagePoint C.ideal z)).obj
    ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))
  let K := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} B) (n : ℤ)).obj
    ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} S) 0).obj N))
  let eSelf : ModuleCat.of (X.presheaf.stalk (C.sourceMap z))
      (X.presheaf.stalk (C.sourceMap z)) ≃ₛₗ[RingHomClass.toRingHom eB]
      ModuleCat.of B B := eB.toSemilinearEquiv
  let : HasInjectiveDimensionLE (ModuleCat.of B B) d :=
    (ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv eB eSelf d).mp inferInstance
  let F : K ≃ₗ[B] B :=
    q.coinducedHomologyLinearEquivOfNormalQuotientOfIso hq n r hS hrB hr2 N
      (normalSurfacePolynomialCoefficientStalkIso R ι n e k (imagePoint C.ideal z)) d
  let E := normalSurfaceCanonicalOriginalStalkCoinductionLinearEquiv R ι i n e P j C z
  let E' : ((moduleStalk X (C.sourceMap z)).obj (normalSurfaceCanonicalModule R ι i n)) ≃ₛₗ[
      RingHomClass.toRingHom eB] K :=
    { __ := E.toAddEquiv
      map_smul' := fun a v => E.map_smul a v }
  let G : ((moduleStalk X (C.sourceMap z)).obj (normalSurfaceCanonicalModule R ι i n)) ≃ₛₗ[
      RingHomClass.toRingHom eB] ModuleCat.of B B := E'.trans F
  exact ⟨G.trans eSelf.symm⟩

include hX hXdim e hfin in
/-- At the original point, native finite self-injective dimension is equivalent
to a frame of the same actual canonical stalk, under the full surface hypotheses. -/
theorem normalSurfaceCanonicalStalk_finiteSelfInjectiveDimension_iff (x : X) :
    (∃ d : ℕ, HasInjectiveDimensionLE
      (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) d) ↔
      Nonempty (((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) ≃ₗ[
        X.presheaf.stalk x] X.presheaf.stalk x) := by
  constructor
  · rintro ⟨d, hd⟩
    let : HasInjectiveDimensionLE
        (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) d := hd
    exact ⟨normalSurfaceCanonicalStalkLinearEquivOfSelfInjectiveDimension
      R ι i hX hXdim n e hfin x d⟩
  · rintro ⟨eω⟩
    obtain ⟨r, _, _, hω⟩ :=
      normalSurfaceCanonicalStalk_hasInjectiveDimension R ι i hX hXdim n e hfin x
    exact ⟨r, (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv eω r).mp hω⟩

end AlgebraicGeometry.Scheme.Cohomology
