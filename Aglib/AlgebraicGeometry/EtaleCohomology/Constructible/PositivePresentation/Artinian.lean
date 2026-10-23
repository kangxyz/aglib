/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.Ambient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FreeSet
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Artinian

/-! # The original positive-modulus presentation on locally Artinian bases

On a locally Artinian quasi-separated base, the original affine-etale free
positive-modulus generators are finite locally constant. Actual common
partitions and proved finite-colimit closure show that the original
bounded-presentation stages are geometrically constructible. The diagram,
cocone, coefficient universe and index universe are those of the original
producer. Ambient finite presentability is retained from its independent
all-modulus proof.

The locally Artinian hypothesis is explicit. This is not the remaining
general qcqs or general Noetherian constructibility assertion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

variable (X : Scheme.{u}) [IsLocallyArtinian X] [QuasiSeparatedSpace X]
    (n : ℕ)

/-- Every original finite-colimit stage is geometrically constructible on
a locally Artinian quasi-separated base at a positive modulus. -/
theorem locallyArtinian_finiteColimitStage_isConstructible
    (hn : n ≠ 0) (F : BoundedPresentation.Coefficient X n)
    (hF : BoundedPresentation.finiteColimitStages X n F) : IsConstructible F.obj := by
  let P : ObjectProperty (AbelianSheaf.{u, u + 1} X) := fun F => IsConstructible F
  have : P.IsClosedUnderIsomorphisms := {
    of_iso := by
      intro A B e h
      exact (isConstructible_iff_of_iso e).mp h }
  let Q : ObjectProperty (BoundedPresentation.Coefficient X n) :=
    P.inverseImage (BoundedPresentation.inclusion X n)
  have hgen : BoundedPresentation.generators X n ≤ Q := by
    rintro F ⟨U⟩
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
      change IsAffine (Spec U.left.unop)
      infer_instance
    change IsConstructible
      (CategoryTheory.Sheaf.TorsionFinitePresentation.freeZModRepresentable.{u + 1}
        X.smallEtaleTopology n ((Scheme.AffineEtale.Spec X).obj U))
    exact isConstructible_of_isFiniteLocallyConstant
      (locallyArtinian_freeZModRepresentable_isFiniteLocallyConstant
        ((Scheme.AffineEtale.Spec X).obj U) n hn)
  have hclosure : BoundedPresentation.finiteColimitStages X n ≤ Q := by
    apply (BoundedPresentation.generators X n).colimitsCardinalClosure_le
      Cardinal.aleph0.{u + 1} ?_ hgen
    intro J _ hJ
    have : Finite (Arrow J) := by
      simpa only [hasCardinalLT_aleph0_iff] using hJ
    have : Finite J := Finite.of_surjective (fun a : Arrow J => a.left)
      (fun j => ⟨Arrow.mk (𝟙 j), rfl⟩)
    have : P.IsClosedUnderColimitsOfShape J := {
      colimitsOfShape_le := by
        rintro G ⟨p⟩
        exact FiniteColimits.locallyArtinian_isConstructible_of_isColimit
          p.diag p.isColimit p.prop_diag_obj }
    dsimp only [Q]
    infer_instance
  exact hclosure F hF

/-- The actual original filtered presentation has geometric constructible
and ambient finitely presentable stages on a locally Artinian
quasi-separated base, for every nonzero modulus. -/
theorem exists_filtered_presentation_locallyArtinian_constructible
    (hn : n ≠ 0) (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ BoundedPresentation.Coefficient X n)
      (ι : D ⋙ BoundedPresentation.inclusion X n ⟶ (Functor.const I).obj F),
      Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, BoundedPresentation.finiteColimitStages X n (D.obj i) ∧
          IsFinitelyPresentable.{u + 1} (D.obj i).obj ∧ IsConstructible (D.obj i).obj := by
  obtain ⟨I, hI, hfiltered, D, ι, hcolimit, hstage⟩ :=
    exists_filtered_presentation_ambient_finitelyPresentable X n F hF
  let := hI
  have : IsFiltered I := hfiltered
  exact ⟨I, hI, hfiltered, D, ι, hcolimit,
    fun i => ⟨(hstage i).1, (hstage i).2,
      locallyArtinian_finiteColimitStage_isConstructible X n hn (D.obj i) (hstage i).1⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
