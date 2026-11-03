/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.TransverseStalk
public import Aglib.AlgebraicGeometry.Morphisms.Integral.GenericSection

/-! # The original transverse generic section on an arbitrary target

The original generic cover point extends uniquely through its actual integral
normalization. The original DVR map factors through its target stalk by the
native closed-point stalk map. The actual local parameter and complement square
then detect etaleness at the original extended closed point.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- Unique extension and pointwise etaleness of the original transverse generic
point, using the original local parameter at the DVR's image point. -/
theorem exists_transverseGenericLift_etaleAt
    {X U : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j]
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (d : Spec (.of D) ⟶ X)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra (X.presheaf.stalk (d (IsLocalRing.closedPoint D))) Ω]
    [IsLocalHom (algebraMap (X.presheaf.stalk (d (IsLocalRing.closedPoint D))) Ω)]
    (f : X.presheaf.stalk (d (IsLocalRing.closedPoint D)))
    (hf : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (d (IsLocalRing.closedPoint D))))
    [IsRegularLocalRing ((X.presheaf.stalk (d (IsLocalRing.closedPoint D))) ⧸ Ideal.span {f})]
    (hreg : IsSMulRegular (X.presheaf.stalk (d (IsLocalRing.closedPoint D))) f)
    (g : Spec (.of (Localization.Away f)) ⟶ U)
    (H : IsPullback g
      (Spec.algebraMap (X.presheaf.stalk (d (IsLocalRing.closedPoint D))) (Localization.Away f))
      j (X.fromSpecStalk (d (IsLocalRing.closedPoint D))))
    (Y : FiniteEtale U) [IsIntegral Y.obj.left]
    [CategoryTheory.PreGaloisCategory.IsGalois Y]
    (N : ℕ) (hN : 0 < N)
    (hunit : IsUnit (N : X.presheaf.stalk (d (IsLocalRing.closedPoint D))))
    (hcard : Nat.card (Aut Y) ∣ N)
    (htrans : Ideal.span {(Scheme.stalkClosedPointTo d).hom f} = IsLocalRing.maximalIdeal D)
    (a : Spec (Spec (.of D)).functionField ⟶ Y.obj.left)
    (ha : a ≫ Y.obj.hom ≫ j =
      (Spec (.of D)).fromSpecStalk (genericPoint (Spec (.of D))) ≫ d) :
    ∃ s : Spec (.of D) ⟶ (genericMap j Y.obj.hom).normalization,
      s ≫ (genericMap j Y.obj.hom).fromNormalization = d ∧
      (Spec (.of D)).fromSpecStalk (genericPoint (Spec (.of D))) ≫ s =
        a ≫ inclusion j Y.obj.hom ∧
      (∀ s' : Spec (.of D) ⟶ (genericMap j Y.obj.hom).normalization,
        s' ≫ (genericMap j Y.obj.hom).fromNormalization = d →
        (Spec (.of D)).fromSpecStalk (genericPoint (Spec (.of D))) ≫ s' =
          a ≫ inclusion j Y.obj.hom → s' = s) ∧
      (genericMap j Y.obj.hom).fromNormalization.etaleAt (s (IsLocalRing.closedPoint D)) := by
  let x := d (IsLocalRing.closedPoint D)
  let R := X.presheaf.stalk x
  let : Algebra R D := (Scheme.stalkClosedPointTo d).hom.toAlgebra
  let : IsLocalHom (algebraMap R D) := Scheme.isLocalHom_stalkClosedPointTo' d
  let q := genericMap j Y.obj.hom
  let : IsFinite q.fromNormalization := fromNormalization_isFinite j Y.obj.hom
  have hnormal : NormalStalks (Spec (.of D)) := fun z =>
    ⟨(isIntegrallyClosed_and_isDomain_stalk_Spec D z).2,
      (isIntegrallyClosed_and_isDomain_stalk_Spec D z).1⟩
  have ha' : (a ≫ inclusion j Y.obj.hom) ≫ q.fromNormalization =
      (Spec (.of D)).fromSpecStalk (genericPoint (Spec (.of D))) ≫ d := by
    rw [Category.assoc, inclusion_over]
    exact ha
  have hext := existsUnique_integralGenericLift (Spec (.of D)) hnormal d q.fromNormalization
    (a ≫ inclusion j Y.obj.hom) ha'
  obtain ⟨s, hs, huniq⟩ := hext
  have hs' : s ≫ q.fromNormalization = Spec.algebraMap R D ≫ X.fromSpecStalk x :=
    hs.1.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk d).symm
  have hetale := etaleAt_of_transverseStalkSection j x Ω D f hf hreg g H Y N hN hunit hcard
    htrans s hs' (Classical.choice (inferInstance : Nonempty (GeometricEtaleNeighborhood R Ω)))
  refine ⟨s, hs.1, hs.2, ?_, hetale⟩
  intro s' hs' ha'
  exact huniq s' ⟨hs', ha'⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
