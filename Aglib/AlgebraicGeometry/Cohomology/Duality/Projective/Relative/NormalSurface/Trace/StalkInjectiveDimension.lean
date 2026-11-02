/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.StalkAction
public import Aglib.RingTheory.Gorenstein.NormalQuotient

/-!
# Finite injective dimension of the original canonical stalk

The actual polynomial chart supplies a regular ambient stalk and the original
coefficient-line frame. The source-linear stalk comparison reaches the native
derived-coinduction homology, whose quotient-Baer bound is transported back
along the original open-stalk ring isomorphism. No later stalk is assumed
finite over or complete over the initial regular base.
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

local instance canonicalStalkInjectiveDerived (B : Type u) [CommRing B] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} B) := HasDerivedCategory.standard _

/-- The original canonical module at each actual point has injective dimension
at most that point's actual local dimension. This is the forward canonical
finite-injective-dimension theorem, not a dualizing uniqueness assertion. -/
theorem normalSurfaceCanonicalStalk_hasInjectiveDimension
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    [IsDominant (i ≫ toSpec R ι)]
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι i).Finite)
    (x : X) :
    ∃ r : ℕ, ringKrullDim (X.presheaf.stalk x) = (r : ℕ) ∧ r ≤ 2 ∧
      HasInjectiveDimensionLE
        ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) r := by
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
  have hK : HasInjectiveDimensionLE K r :=
    q.coinducedHomology_hasInjectiveDimensionLE_of_iso hq n r hS hrB hr2 N
      (normalSurfacePolynomialCoefficientStalkIso R ι n e k (imagePoint C.ideal z))
  let E := normalSurfaceCanonicalOriginalStalkCoinductionLinearEquiv R ι i n e P j C z
  let E' : ((moduleStalk X (C.sourceMap z)).obj (normalSurfaceCanonicalModule R ι i n)) ≃ₛₗ[
      RingHomClass.toRingHom eB] K :=
    { __ := E.toAddEquiv
      map_smul' := fun a v => E.map_smul a v }
  exact ⟨r, hrX, hr2,
    (ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv eB E' r).mpr hK⟩

end AlgebraicGeometry.Scheme.Cohomology
