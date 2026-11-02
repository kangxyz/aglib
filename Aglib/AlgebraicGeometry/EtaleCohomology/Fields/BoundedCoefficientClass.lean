/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.Artinian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsCoefficientContinuity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.CategoryTheory.Limits.CoconeValues

/-! # Finite coefficient representatives of original bounded field classes

The existing bounded presentation is used on the actual field spectrum.
Its finite-colimit stages are genuinely finite locally constant: the original
free generators and finite-colimit closure prove this without any general
constructibility or Galois-module equivalence assumption. Pullback and qcqs
coefficient continuity produce a class at one actual stage whose original
coefficient map has exactly the prescribed class as image.

This is coefficient devissage, not two-field effacement. The final naturality
lemma only transports a supplied zero and does not produce a killing cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u e eZ

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

open Constructible

/-- Positive bounded-presentation stages are actually finite locally constant
on a locally Artinian quasi-separated base. The original stages are unchanged. -/
theorem boundedStage_isFiniteLocallyConstant
    (X : Scheme.{u}) [IsLocallyArtinian X] [QuasiSeparatedSpace X]
    (n : ℕ) (hn : 0 < n) (E : BoundedPresentation.Coefficient X n)
    (hE : BoundedPresentation.finiteColimitStages X n E) :
    IsFiniteLocallyConstant E.obj := by
  let P : ObjectProperty (AbelianSheaf.{u, u + 1} X) :=
    fun F => IsFiniteLocallyConstant F
  have : P.IsClosedUnderIsomorphisms := {
    of_iso := by
      intro A B t h
      exact (isFiniteLocallyConstant_iff_of_iso t).mp h }
  let Q : ObjectProperty (BoundedPresentation.Coefficient X n) :=
    P.inverseImage (BoundedPresentation.inclusion X n)
  have hgen : BoundedPresentation.generators X n ≤ Q := by
    rintro F ⟨U⟩
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
      change IsAffine (Spec U.left.unop)
      infer_instance
    change IsFiniteLocallyConstant
      (CategoryTheory.Sheaf.TorsionFinitePresentation.freeZModRepresentable.{u + 1}
        X.smallEtaleTopology n ((Scheme.AffineEtale.Spec X).obj U))
    exact PositivePresentation.locallyArtinian_freeZModRepresentable_isFiniteLocallyConstant
      ((Scheme.AffineEtale.Spec X).obj U) n (Nat.ne_of_gt hn)
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
        exact FiniteColimits.locallyArtinian_isFiniteLocallyConstant_of_isColimit
          p.diag p.isColimit p.prop_diag_obj }
    dsimp only [Q]
    infer_instance
  exact hclosure E hE

/-- A class in an actual pulled-back filtered coefficient colimit has a
representative at one original coefficient stage. -/
theorem exists_coefficientStage_class
    {S Y : Scheme.{u}} (p : Y ⟶ S) [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I AddCommGrpCat.{e}] [UnivLE.{u + 1, e}]
    (D : I ⥤ AbelianSheaf.{u, u + 1} S) (t : Cocone D) (ht : IsColimit t)
    (q : ℕ) (c : Sheaf.H.{e} ((inverseImage p).obj t.pt) q) :
    ∃ (i : I) (d : Sheaf.H.{e} ((inverseImage p).obj (D.obj i)) q),
      Sheaf.H.map ((inverseImage p).map (t.ι.app i)) q d = c := by
  let H : AbelianSheaf.{u, u + 1} Y ⥤ AddCommGrpCat.{e} :=
    Sheaf.functorH Y.smallEtaleTopology q
  let G := D ⋙ inverseImage p
  let : IsIso (colimit.post G H) :=
    Continuity.isIso_qcqsCoefficientColimitComparison G q
  let : PreservesColimit G H := preservesColimit_of_isIso_post H G
  let : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{e}) :=
    preservesFilteredColimitsOfSize_of_univLE.{e, e, u + 1, u + 1} _
  exact CoconeValues.exists_rep (G ⋙ H)
    (isColimitOfPreserves H (isColimitOfPreserves (inverseImage p) ht)) c

/-- Every original bounded field coefficient class on a qcqs source comes
from an actual finite locally constant field coefficient killed by the same n.
The original coefficient arrow and its exact class image are part of the output. -/
theorem exists_finiteLocallyConstant_coefficient_class
    (K : Type u) [Field K]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K)))
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K))
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [UnivLE.{u + 1, e}]
    (q : ℕ) (c : Sheaf.H.{e} ((inverseImage p).obj F) q) :
    ∃ (E : AbelianSheaf.{u, u + 1} (Spec (.of K))) (a : E ⟶ F),
      n • 𝟙 E = 0 ∧ IsFiniteLocallyConstant E ∧
      ∃ d : Sheaf.H.{e} ((inverseImage p).obj E) q,
        Sheaf.H.map ((inverseImage p).map a) q d = c := by
  obtain ⟨I, hI, hfiltered, D, ι, ⟨ht⟩, hstage⟩ :=
    BoundedPresentation.exists_filtered_presentation (Spec (.of K)) n F hF
  let := hI
  let : IsFiltered I := hfiltered
  obtain ⟨i, d, hd⟩ := exists_coefficientStage_class p
    (D ⋙ BoundedPresentation.inclusion (Spec (.of K)) n) (Cocone.mk F ι) ht q c
  exact ⟨(D.obj i).obj, ι.app i, (D.obj i).property,
    boundedStage_isFiniteLocallyConstant (Spec (.of K)) n hn (D.obj i) (hstage i), d, hd⟩

/-- Zero of the actual representative pulls forward to zero of the original
class. This is only naturality, with independent source and target Ext worlds. -/
theorem cohomologyPullback_eq_zero_of_coefficient_class
    {Y Z : Scheme.{u}} (z : Z ⟶ Y)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    {E F : AbelianSheaf.{u, u + 1} Y} (a : E ⟶ F) (q : ℕ)
    (d : Sheaf.H.{e} E q) (c : Sheaf.H.{e} F q)
    (hc : Sheaf.H.map a q d = c)
    (hd : cohomologyPullback.{u, e, eZ} z E q d = 0) :
    cohomologyPullback.{u, e, eZ} z F q c = 0 := by
  rw [← hc, cohomologyPullback_coefficientMap, hd, map_zero]

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
