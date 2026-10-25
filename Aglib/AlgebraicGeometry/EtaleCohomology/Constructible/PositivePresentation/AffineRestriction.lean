/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.GenuineModules
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Ambient finite presentability of original stages on affine opens

On a separated scheme, an original affine-etale test object has an affine
structural morphism. Its actual pullback to any affine open is therefore
affine, hence qcqs. The accepted original free-generator pullback comparison
and finite-colimit preservation prove ambient finite presentability of the
original bounded stages on that affine open.

This is a theorem about the actual finite-colimit stages. It does not use
general preservation of finitely presentable objects by inverse image.
The statement holds at every modulus, including zero. Geometric
constructibility retains its nonzero-modulus and actual partition input.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.TorsionFinitePresentation
open AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

variable (X : Scheme.{u}) [X.IsSeparated] (n : ℕ)

/-- Each original bounded finite-colimit stage remains ambient finitely
presentable on every original affine open of a separated base, at all moduli. -/
theorem finiteColimitStage_affineRestriction_isFinitelyPresentable
    (V : X.affineOpens) (F : BoundedPresentation.Coefficient X n)
    (hF : BoundedPresentation.finiteColimitStages X n F) :
    IsFinitelyPresentable.{u + 1} ((inverseImage V.1.ι).obj F.obj) := by
  let κ : Cardinal.{u + 1} := Cardinal.aleph0
  let P : ObjectProperty (AbelianSheaf.{u, u + 1} V.1.toScheme) :=
    isCardinalPresentable.{u + 1, u + 1, u + 2}
      (AbelianSheaf.{u, u + 1} V.1.toScheme) κ
  let Q : ObjectProperty (BoundedPresentation.Coefficient X n) :=
    P.inverseImage (BoundedPresentation.inclusion X n ⋙ inverseImage V.1.ι)
  have hgen : BoundedPresentation.generators X n ≤ Q := by
    rintro F ⟨U⟩
    let W : X.Etale := (Scheme.AffineEtale.Spec X).obj U
    have : IsAffine W.left := by
      change IsAffine (Spec U.left.unop)
      infer_instance
    have ht : W.hom ≫ terminal.from X = terminal.from W.left := terminal.comp_from _
    have hterminal : IsAffineHom (terminal.from W.left) := inferInstance
    have hcomp : IsAffineHom (W.hom ≫ terminal.from X) := ht.symm ▸ hterminal
    have hsep : IsSeparated (terminal.from X) :=
      (inferInstance : X.IsSeparated).isSeparated_terminal_from
    have : IsAffineHom W.hom := @IsAffineHom.of_comp W.left X (⊤_ Scheme.{u})
      W.hom (terminal.from X) hcomp hsep
    have : IsAffine V.1.toScheme := V.property
    have : IsAffine ((siteBaseChange V.1.ι).obj W).left := by
      change IsAffine (pullback W.hom V.1.ι)
      infer_instance
    change P ((inverseImage V.1.ι).obj
      (freeZModRepresentable.{u + 1} X.smallEtaleTopology n W))
    have hp : P (freeZModRepresentable.{u + 1} V.1.toScheme.smallEtaleTopology n
        ((siteBaseChange V.1.ι).obj W)) :=
      qcqs_freeZModRepresentable_isFinitelyPresentable n ((siteBaseChange V.1.ι).obj W)
    exact P.prop_of_iso (freeZModRepresentableInverseImageIso V.1.ι n W).symm hp
  have hclosure : BoundedPresentation.finiteColimitStages X n ≤ Q := by
    apply (BoundedPresentation.generators X n).colimitsCardinalClosure_le κ ?_ hgen
    intro J _ hJ
    have : P.IsClosedUnderColimitsOfShape J :=
      isClosedUnderColimitsOfShape_isCardinalPresentable.{u + 1, u + 1, u + 1, u + 1, u + 2}
        (AbelianSheaf.{u, u + 1} V.1.toScheme) hJ
    dsimp only [Q]
    infer_instance
  exact hclosure F hF

/-- The original affine-restriction conclusion is retained for the genuine
scalar-converted stage through the native underlying comparison. -/
theorem scalarLiftStage_affineRestriction_isFinitelyPresentable
    (V : X.affineOpens) (F : BoundedPresentation.Coefficient X n)
    (hF : BoundedPresentation.finiteColimitStages X n F) :
    IsFinitelyPresentable.{u + 1}
      ((inverseImage V.1.ι).obj ((zmodUnderlying X n).obj ((scalarLift X n).obj F))) := by
  let P : ObjectProperty (AbelianSheaf.{u, u + 1} V.1.toScheme) :=
    isCardinalPresentable.{u + 1, u + 1, u + 2}
      (AbelianSheaf.{u, u + 1} V.1.toScheme) Cardinal.aleph0.{u + 1}
  have hP : P ((inverseImage V.1.ι).obj F.obj) :=
    finiteColimitStage_affineRestriction_isFinitelyPresentable X n V F hF
  exact P.prop_of_iso
    ((inverseImage V.1.ι).mapIso ((scalarLiftUnderlyingIso X n).app F)).symm hP

/-- The actual positive genuine presentation has ambient finitely
presentable underlying stages on every original affine open, as well as
global ambient finite presentability and geometric constructibility. -/
theorem exists_filtered_genuine_presentation_constructible_affineFP_of_finiteEtalePartitions
    (hn : n ≠ 0)
    (hparts : ∀ U : Scheme.AffineEtale X, ∀ V : X.affineOpens,
      ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
        ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj
          ((Scheme.AffineEtale.Spec X).obj U)).hom)
    (M : ZModSheaf X n) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ ZModSheaf X n) (κ : D ⟶ (Functor.const I).obj M),
      Nonempty (IsColimit (Cocone.mk M κ)) ∧
        Nonempty (IsColimit ((zmodUnderlying X n).mapCocone (Cocone.mk M κ))) ∧
        ∀ i, IsFinitelyPresentable.{u + 1} ((zmodUnderlying X n).obj (D.obj i)) ∧
          IsConstructible ((zmodUnderlying X n).obj (D.obj i)) ∧
          ∀ V : X.affineOpens, IsFinitelyPresentable.{u + 1}
            ((inverseImage V.1.ι).obj ((zmodUnderlying X n).obj (D.obj i))) := by
  obtain ⟨I, hI, hfiltered, D, ι, κ, _, ⟨hκ⟩, _, hstage⟩ :=
    exists_filtered_genuine_presentation X n M
  let := hI
  have : IsFiltered I := hfiltered
  refine ⟨I, hI, hfiltered, D ⋙ scalarLift X n, κ, ⟨hκ⟩,
    ⟨isColimitOfPreserves (zmodUnderlying X n) hκ⟩, ?_⟩
  intro i
  refine ⟨(hstage i).2, ?_, fun V =>
    scalarLiftStage_affineRestriction_isFinitelyPresentable X n V (D.obj i) (hstage i).1⟩
  exact (isConstructible_iff_of_iso ((scalarLiftUnderlyingIso X n).app (D.obj i))).mpr
    (finiteColimitStage_isConstructible_of_finiteEtalePartitions
      X n hn hparts (D.obj i) (hstage i).1)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
