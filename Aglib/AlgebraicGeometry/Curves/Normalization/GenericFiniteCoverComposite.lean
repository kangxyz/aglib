/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Normalization.GenericFiniteCover

/-! # The original generic cover composed with its finite base

The target is the literal pullback of the original family to its original
principal base open. The comparison map is induced from the two existing
cartesian squares, and the branch coproduct is composed with that map once.
No field, branch, cover or affine realization is selected again.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.FinitePresentationDescent
open IsFractionRing

namespace AlgebraicGeometry.Scheme.OverField.Curve.Normalization

universe u

/-- Compose the actual branch cover and the actual finite base into one
finite surjection onto the original family restricted to its base open. -/
theorem GenericFiniteCoverData.exists_composite_cover
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {s : Finset (AlgebraicClosure K)} [Algebra R (FiniteField.stage K s)]
    {X : Scheme.{u}} {p : X ⟶ Spec (.of R)} (D : GenericFiniteCoverData R K s p) :
    letI := D.baseAffine
    letI := D.finiteI
    let U : (Spec (.of (Localization.Away D.r))).Opens := PrimeSpectrum.basicOpen D.d
    let β := genericCoverBaseMap D.B D.r
    let T := genericCoverBase D.B D.r D.d
    let b := T.isoSpec.inv ≫ pullback.snd β U.ι
    let u := U.ι ≫ Spec.algebraMap R (Localization.Away D.r)
    ∃ k : D.N.X ⟶ pullback p u,
      IsPullback k D.N.f (pullback.snd p u) b ∧
      k ≫ pullback.fst p u = D.ρ ∧
      IsFinite k ∧ Surjective k ∧
      IsFinite ((Sigma.desc fun i => (D.arrows i).hom.left) ≫ k) ∧
      Surjective ((Sigma.desc fun i => (D.arrows i).hom.left) ≫ k) ∧
      ((Sigma.desc fun i => (D.arrows i).hom.left) ≫ k) ≫ pullback.snd p u =
        (Sigma.desc fun i => (D.M i).f) ≫ b := by
  classical
  let : IsAffine (genericCoverBase D.B D.r D.d) := D.baseAffine
  let : Finite D.I := D.finiteI
  let Rr := Localization.Away D.r
  let Br := Localization.Away (algebraMap R D.B D.r)
  let U : (Spec (.of Rr)).Opens := PrimeSpectrum.basicOpen D.d
  let β := genericCoverBaseMap D.B D.r
  let T := genericCoverBase D.B D.r D.d
  let b : Spec Γ(T, ⊤) ⟶ U := T.isoSpec.inv ≫ pullback.snd β U.ι
  let u : U.toScheme ⟶ Spec (.of R) := U.ι ≫ Spec.algebraMap R Rr
  let δ := T.isoSpec.inv ≫ pullback.fst β U.ι
  have hβ : β ≫ Spec.algebraMap R Rr = Spec.algebraMap R Br := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (finiteSubalgebraAwayBaseMap D.B D.r).commutes x
  have hbase : b ≫ u = δ ≫ Spec.algebraMap R Br := by
    dsimp only [b, u, δ]
    calc
      (T.isoSpec.inv ≫ pullback.snd β U.ι) ≫
          (U.ι ≫ Spec.algebraMap R Rr) =
          T.isoSpec.inv ≫ ((pullback.snd β U.ι ≫ U.ι) ≫ Spec.algebraMap R Rr) := by
            simp only [Category.assoc]
      _ = T.isoSpec.inv ≫ ((pullback.fst β U.ι ≫ β) ≫ Spec.algebraMap R Rr) :=
        congrArg (fun z => T.isoSpec.inv ≫ (z ≫ Spec.algebraMap R Rr))
          (pullback.condition (f := β) (g := U.ι)).symm
      _ = (T.isoSpec.inv ≫ pullback.fst β U.ι) ≫ Spec.algebraMap R Br := by
        rw [Category.assoc, hβ, Category.assoc]
  have H : IsPullback D.ρ D.N.f p (b ≫ u) := by
    rw [hbase]
    exact D.ρ_square
  let Q := IsPullback.of_hasPullback p u
  let k : D.N.X ⟶ pullback p u :=
    Q.lift D.ρ (D.N.f ≫ b) (H.w.trans (Category.assoc _ _ _).symm)
  have hk : IsPullback k D.N.f (pullback.snd p u) b := H.of_right' Q
  have hkfst : k ≫ pullback.fst p u = D.ρ := Q.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd p u = D.N.f ≫ b := Q.lift_snd _ _ _
  let : IsFinite (pullback.snd β U.ι) := D.finite_base
  let : Surjective (pullback.snd β U.ι) := D.surjective_base
  let : IsFinite b := inferInstanceAs (IsFinite (T.isoSpec.inv ≫ pullback.snd β U.ι))
  let : Surjective b := inferInstanceAs (Surjective (T.isoSpec.inv ≫ pullback.snd β U.ι))
  let : IsFinite k := MorphismProperty.of_isPullback hk.flip (inferInstance : IsFinite b)
  let : Surjective k := MorphismProperty.of_isPullback hk.flip (inferInstance : Surjective b)
  let d := Sigma.desc fun i => (D.arrows i).hom.left
  let : IsFinite d := D.finite_cover
  let : Surjective d := D.surjective_cover
  refine ⟨k, hk, hkfst, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, hksnd, ← Category.assoc]
  apply congrArg (fun a => a ≫ b)
  apply Sigma.hom_ext
  intro i
  change Sigma.ι (fun i : D.I => (D.M i).X) i ≫
    ((Sigma.desc fun i => (D.arrows i).hom.left) ≫ D.N.f) =
    Sigma.ι (fun i : D.I => (D.M i).X) i ≫ (Sigma.desc fun i => (D.M i).f)
  rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  exact Over.w (D.arrows i).hom

end AlgebraicGeometry.Scheme.OverField.Curve.Normalization
