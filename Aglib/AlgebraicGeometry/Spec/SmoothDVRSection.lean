/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.SmoothDVRParameter
public import Aglib.AlgebraicGeometry.Stalk.SectionScalar
public import Aglib.AlgebraicGeometry.Spec.DVRGenericComplement

/-! # Original transverse data supplied by a smooth DVR section

The section itself gives a point of the actual special fibre. The structural
uniformizer is a regular parameter there, evaluates to the original uniformizer
along the section, and its principal complement is the restriction of the
original generic fibre. All these data are constructed rather than assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- A smooth DVR section supplies the exact local geometric inputs of the
transverse-normalization criterion on the original target stalk. -/
theorem exists_smoothDVRSection_transverseData
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Smooth p]
    (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 (Spec (.of R)))
    (t : R) (ht : Irreducible t) :
    let x := s (IsLocalRing.closedPoint R)
    let f := p.stalkScalar x t
    f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      IsSMulRegular (X.presheaf.stalk x) f ∧
      IsRegularLocalRing ((X.presheaf.stalk x) ⧸ Ideal.span {f}) ∧
      Ideal.span {(stalkClosedPointTo s).hom f} = IsLocalRing.maximalIdeal R ∧
      ∃ g : Spec (.of (Localization.Away f)) ⟶ pullback p (Spec.algebraMap R K),
        IsPullback g (Spec.algebraMap (X.presheaf.stalk x) (Localization.Away f))
          (pullback.fst p (Spec.algebraMap R K)) (X.fromSpecStalk x) ∧
        g ≫ pullback.snd p (Spec.algebraMap R K) =
          Spec.map (CommRingCat.ofHom (dvrFractionParameterMap R K (p.stalkScalar x) t ht)) := by
  let x := s (IsLocalRing.closedPoint R)
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let F : Scheme.{u} := pullback p r
  let m : Spec (.of (IsLocalRing.ResidueField R)) ⟶ F :=
    pullback.lift (r ≫ s) (𝟙 _) (by simp only [Category.assoc, hs, Category.comp_id,
      Category.id_comp])
  let y : F := m (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))
  let : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue R)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  have hy : pullback.fst p r y = x := by
    change (m ≫ pullback.fst p r) (IsLocalRing.closedPoint _) = x
    rw [pullback.lift_fst]
    change s (r (IsLocalRing.closedPoint _)) = x
    rw [AlgebraicGeometry.Spec_closedPoint]
  have hparameter := p.smoothDVR_stalk_regularParameter t ht y
  dsimp only at hparameter
  rw [hy] at hparameter
  have htrans : Ideal.span {(stalkClosedPointTo s).hom (p.stalkScalar x t)} =
      IsLocalRing.maximalIdeal R := by
    rw [stalkClosedPointTo_stalkScalar_of_section p s hs]
    exact ht.maximalIdeal_eq.symm
  exact ⟨hparameter.1, hparameter.2.1, hparameter.2.2, htrans,
    exists_dvrGenericStalk_complement R K t ht p x⟩

end AlgebraicGeometry.Scheme
