/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProjectiveFromCurves
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.AffineOpenLocalization
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Affine

/-! # Relative projective constructibility over a Noetherian target

An actual closed embedding into a projective-space pullback is transported
along each original affine spectrum chart. The projective comparison retains
the literal chart pullback projection. All-degree etale exchange and the
existing partitions then descend constructibility to the original target.
The full proper curve-family theorem remains an explicit geometric input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- A relative closed projective embedding gives a closed embedding of each
literal spectrum-chart pullback, with its unchanged structural morphism. -/
theorem exists_closedProjectiveEmbedding_of_affineBaseChange
    {R A : Type u} [CommRing R] [CommRing A] {X S : Scheme.{u}}
    (b : S ⟶ Spec (.of R)) (p : X ⟶ S) (n : ℕ)
    (j : X ⟶ pullback (ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1)))) b)
    [IsClosedImmersion j] (hj : j ≫ pullback.snd _ _ = p)
    (g : Spec (.of A) ⟶ S) :
    ∃ i : pullback g p ⟶ ProjectiveSpace A (ULift.{u} (Fin (n + 1))),
      IsClosedImmersion i ∧
      i ≫ ProjectiveSpace.toSpec A (ULift.{u} (Fin (n + 1))) = pullback.fst g p := by
  let t := ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1)))
  let a : Over.mk p ⟶ Over.mk (pullback.snd t b) := Over.homMk j hj
  have : IsClosedImmersion a.left := show IsClosedImmersion j from inferInstance
  let ag := (Over.pullback g).map a
  have hag : IsClosedImmersion ag.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) g a inferInstance
  let e := ProjectiveSpace.affinePullbackIso (ULift.{u} (Fin (n + 1)))
    (pullback.fst t (g ≫ b)) (pullback.snd t (g ≫ b)) (g ≫ b)
    (IsPullback.of_hasPullback t (g ≫ b))
  have he : e.hom ≫ ProjectiveSpace.toSpec A (ULift.{u} (Fin (n + 1))) =
      pullback.snd t (g ≫ b) :=
    ProjectiveSpace.affinePullbackIso_hom_toSpec _ _ _ _ _
  let i := (pullbackSymmetry g p).hom ≫ ag.left ≫
    (pullbackLeftPullbackSndIso t b g).hom ≫ e.hom
  refine ⟨i, ?_, ?_⟩
  · dsimp [i]
    infer_instance
  · change ((pullbackSymmetry g p).hom ≫ ag.left ≫
      (pullbackLeftPullbackSndIso t b g).hom ≫ e.hom) ≫
        ProjectiveSpace.toSpec A (ULift.{u} (Fin (n + 1))) = _
    simp only [Category.assoc, he]
    have hw : ag.left ≫ pullback.snd (pullback.snd t b) g = pullback.snd p g :=
      Over.w ag
    rw [pullbackLeftPullbackSndIso_hom_snd, hw]
    exact pullbackSymmetry_hom_comp_snd g p

variable
  (hcurve : ∀ {Y T : Scheme.{u}} [IsNoetherian T] (g : Y ⟶ T) [IsProper g],
    (∀ (K : Type u) [Field K] (η : Spec (.of K) ⟶ T),
      topologicalKrullDim (pullback g η : Scheme.{u}) ≤ 1) →
    ∀ (q : ℕ) (F : AbelianSheaf.{u, u + 1} Y), Constructible.IsConstructible F →
      Constructible.IsConstructible ((higherDirectImage g q).obj F))

include hcurve

/-- The original relative projective morphism preserves constructibility
in all degrees, conditional only on the genuine curve-family theorem. -/
theorem higherDirectImage_relativeProjective_isConstructible_of_curves
    {R : Type u} [CommRing R] {X S : Scheme.{u}} [IsNoetherian S]
    (b : S ⟶ Spec (.of R)) (p : X ⟶ S) (n : ℕ)
    (j : X ⟶ pullback (ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1)))) b)
    [IsClosedImmersion j] (hj : j ≫ pullback.snd _ _ = p)
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((higherDirectImage p q).obj F) := by
  have : IsProper p := by rw [← hj]; infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := ⟨⟩
  apply higherDirectImage_isConstructible_of_affineSpecBaseChanges p q F
  intro U
  have : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨i, hi, hbase⟩ :=
    exists_closedProjectiveEmbedding_of_affineBaseChange b p n j hj U.property.fromSpec
  have : IsClosedImmersion i := hi
  have hpull := Constructible.isConstructible_pullback_of_qcqs
    (pullback.snd U.property.fromSpec p) hF
  have h := higherDirectImage_closedProjective_isConstructible_of_curves hcurve
    Γ(S, U.1) n i q _ hpull
  simpa only [hbase] using h

/-- A closed projective embedding over the original affine base gives the
required relative closed embedding for any separated intermediate target.
This is the actual graph map, not an assumed projective-modification packet. -/
theorem higherDirectImage_projectiveSource_isConstructible_of_curves
    {R : Type u} [CommRing R] {X S : Scheme.{u}} [IsNoetherian S]
    (b : S ⟶ Spec (.of R)) [IsSeparated b] (p : X ⟶ S) (n : ℕ)
    (j : X ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))) [IsClosedImmersion j]
    (hj : j ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))) = p ≫ b)
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((higherDirectImage p q).obj F) := by
  let a := pullback.lift j p hj
  have ha : IsClosedImmersion (a ≫ pullback.fst _ _) := by
    simpa only [a, pullback.lift_fst] using (inferInstance : IsClosedImmersion j)
  have : IsClosedImmersion a := IsClosedImmersion.of_comp a (pullback.fst _ _)
  exact higherDirectImage_relativeProjective_isConstructible_of_curves hcurve b p n a
    (pullback.lift_snd j p hj) q F hF

end AlgebraicGeometry.Scheme.EtaleCohomology
