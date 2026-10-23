/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.Ambient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.RepresentablePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.General

/-! # Original positive stages from actual finite-etale partitions

Actual finite-etale partitions of the original affine-etale generators,
together with the proved general finite-colimit closure, imply geometric
constructibility of the original bounded-presentation stages. The input
consists of actual locally closed schemes and finite base-changed maps.
The geometric producer of those partitions is a separate theorem.

The original diagram, cocone and coefficient/index universe are retained.
The modulus is nonzero; ambient finite presentability holds independently
at every modulus, including zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

variable (X : Scheme.{u}) (n : ℕ)

/-- Actual finite-etale partitions of all original affine-etale generators
produce constructible original positive-modulus finite-colimit stages. -/
theorem finiteColimitStage_isConstructible_of_finiteEtalePartitions
    (hn : n ≠ 0)
    (hparts : ∀ U : Scheme.AffineEtale X, ∀ V : X.affineOpens,
      ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
        ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom)
    (F : BoundedPresentation.Coefficient X n)
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
    change IsConstructible
      (CategoryTheory.Sheaf.TorsionFinitePresentation.freeZModRepresentable.{u + 1}
        X.smallEtaleTopology n ((Scheme.AffineEtale.Spec X).obj U))
    exact freeZModRepresentable_isConstructible_of_finiteEtalePartitions
      ((Scheme.AffineEtale.Spec X).obj U) n hn (hparts U)
  have hclosure : BoundedPresentation.finiteColimitStages X n ≤ Q := by
    apply (BoundedPresentation.generators X n).colimitsCardinalClosure_le
      Cardinal.aleph0.{u + 1} ?_ hgen
    intro J _ hJ
    have : Finite (Arrow J) := by
      simpa only [hasCardinalLT_aleph0_iff] using hJ
    have : P.IsClosedUnderColimitsOfShape J := {
      colimitsOfShape_le := by
        rintro G ⟨p⟩
        exact FiniteColimits.isConstructible_of_isColimit
          p.diag p.isColimit p.prop_diag_obj }
    dsimp only [Q]
    infer_instance
  exact hclosure F hF

/-- Under actual finite-etale partitions of the original generators, the
actual original filtered presentation has constructible and ambient
finitely presentable stages, for every nonzero modulus. -/
theorem exists_filtered_presentation_constructible_of_finiteEtalePartitions
    (hn : n ≠ 0)
    (hparts : ∀ U : Scheme.AffineEtale X, ∀ V : X.affineOpens,
      ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
        ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
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
      finiteColimitStage_isConstructible_of_finiteEtalePartitions
        X n hn hparts (D.obj i) (hstage i).1⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
