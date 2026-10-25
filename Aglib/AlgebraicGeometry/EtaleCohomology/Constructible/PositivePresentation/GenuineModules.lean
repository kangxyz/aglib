/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FiniteEtalePartitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModRetract
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Full
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # The original bounded presentation as genuine ZMod sheaves

Canonical scalar conversion is an actual equivalence from the original
bounded coefficient category to genuine ZMod sheaves. The native underlying
functor factors through the original bounded coefficient inclusion and
preserves its original colimits. These assertions include modulus zero.

The original filtered diagram and cocone lift through canonical scalar
conversion. The fully faithful preimage of the native scalar comparison
then makes the cocone point the original genuine module sheaf. A diagram
comparison and a cocone comparison retain every original underlying map.
Constructible stages keep the nonzero-modulus condition and the actual
finite-etale-partition input.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

universe u v w

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  TorsionZMod.sheafUnderlying_full Cardinal.fact_isRegular_aleph0

variable (X : Scheme.{u}) (n : ℕ)

/-- The actual canonical scalar conversion of the original bounded coefficients. -/
abbrev scalarLift : BoundedPresentation.Coefficient X n ⥤ ZModSheaf X n :=
  TorsionZMod.sheafFunctor.{u + 1, u, u + 1} X.smallEtaleTopology n

/-- Forgetting scalars after canonical conversion recovers the original
coefficient objects and maps through the native comparison. -/
abbrev scalarLiftUnderlyingIso :
    scalarLift X n ⋙ zmodUnderlying X n ≅ BoundedPresentation.inclusion X n :=
  TorsionZMod.sheafFunctorUnderlyingIso.{u + 1, u, u + 1} X.smallEtaleTopology n

/-- The supplied genuine module structures land in the original bounded
coefficient category by their literal identity-annihilation equation. -/
def genuineCoefficientFunctor : ZModSheaf X n ⥤ BoundedPresentation.Coefficient X n :=
  (TorsionZMod.killedSheaves X.smallEtaleTopology n).lift (zmodUnderlying X n)
    (zmodUnderlying_nsmul_id X n)

/-- The factorization through the original bounded coefficient inclusion
retains the original underlying functor literally. -/
def genuineCoefficientUnderlyingIso :
    genuineCoefficientFunctor X n ⋙ BoundedPresentation.inclusion X n ≅
      zmodUnderlying X n :=
  (TorsionZMod.killedSheaves X.smallEtaleTopology n).liftCompιIso
    (zmodUnderlying X n) (zmodUnderlying_nsmul_id X n)

/-- The actual underlying-coefficient factor is an equivalence, including
modulus zero. Essential surjectivity uses canonical scalar conversion. -/
instance genuineCoefficientFunctor_isEquivalence :
    (genuineCoefficientFunctor X n).IsEquivalence where
  faithful := Functor.Faithful.of_comp_iso (genuineCoefficientUnderlyingIso X n)
  full := Functor.Full.of_comp_faithful_iso (genuineCoefficientUnderlyingIso X n)
  essSurj := {
    mem_essImage F := ⟨(scalarLift X n).obj F, ⟨ObjectProperty.isoMk _
      (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F.obj F.property)⟩⟩ }

/-- The canonical scalar conversion is itself an equivalence. Its original
underlying comparison proves full faithfulness; the supplied genuine
module objects are recovered by full scalar forgetting. -/
instance scalarLift_isEquivalence : (scalarLift X n).IsEquivalence where
  faithful := Functor.Faithful.of_comp_iso (scalarLiftUnderlyingIso X n)
  full := Functor.Full.of_comp_faithful_iso (scalarLiftUnderlyingIso X n)
  essSurj := {
    mem_essImage M := ⟨(genuineCoefficientFunctor X n).obj M,
      ⟨(zmodUnderlying X n).preimageIso
        (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n
          ((zmodUnderlying X n).obj M) (zmodUnderlying_nsmul_id X n M))⟩⟩ }

/-- The actual equivalence uses canonical conversion as its forward functor. -/
def genuineModuleEquivalence :
    BoundedPresentation.Coefficient X n ≌ ZModSheaf X n :=
  (scalarLift X n).asEquivalence

/-- The original genuine-module underlying functor preserves all original
colimits of the coefficient/index size, for every modulus. -/
instance genuineUnderlying_preservesColimits :
    PreservesColimitsOfSize.{u + 1, u + 1} (zmodUnderlying X n) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (genuineCoefficientFunctor X n ⋙ BoundedPresentation.inclusion X n) := inferInstance
  exact preservesColimits_of_natIso (genuineCoefficientUnderlyingIso X n)

/-- Canonical conversion of the original underlying coefficient is
isomorphic to the supplied genuine module sheaf, through the native
underlying comparison. -/
def canonicalModuleIso (M : ZModSheaf X n) :
    (scalarLift X n).obj ((genuineCoefficientFunctor X n).obj M) ≅ M :=
  (zmodUnderlying X n).preimageIso
    (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n
      ((zmodUnderlying X n).obj M) (zmodUnderlying_nsmul_id X n M))

/-- The underlying isomorphism is exactly the native original scalar comparison. -/
theorem canonicalModuleIso_underlying_hom (M : ZModSheaf X n) :
    (zmodUnderlying X n).map (canonicalModuleIso X n M).hom =
      (scalarLiftUnderlyingIso X n).hom.app ((genuineCoefficientFunctor X n).obj M) := by
  exact (zmodUnderlying X n).map_preimage _

section CoconeTransport

variable {I : Type v} [Category.{w} I] (M : ZModSheaf X n)
    (D : I ⥤ BoundedPresentation.Coefficient X n)
    (ι : D ⋙ BoundedPresentation.inclusion X n ⟶
      (Functor.const I).obj ((zmodUnderlying X n).obj M))

/-- The original diagram's actual underlying comparison after canonical
scalar conversion, with no change of its index or arrows. -/
def scalarLiftDiagramUnderlyingIso :
    (D ⋙ scalarLift X n) ⋙ zmodUnderlying X n ≅ D ⋙ BoundedPresentation.inclusion X n :=
  NatIso.ofComponents (fun i => (scalarLiftUnderlyingIso X n).app (D.obj i))
    (fun f => (scalarLiftUnderlyingIso X n).hom.naturality (D.map f))

/-- Lift the literal original cocone into its actual full coefficient category. -/
def originalCoefficientCocone : Cocone D where
  pt := (genuineCoefficientFunctor X n).obj M
  ι := {
    app i := ObjectProperty.homMk (ι.app i)
    naturality := by
      intro i j f
      apply ObjectProperty.hom_ext
      exact ι.naturality f }

/-- Reflection through the original full inclusion retains the supplied
original colimit, without replacing its cocone maps. -/
def originalCoefficientCocone_isColimit
    (hι : IsColimit (Cocone.mk ((zmodUnderlying X n).obj M) ι)) :
    IsColimit (originalCoefficientCocone X n M D ι) := by
  apply isColimitOfReflects (BoundedPresentation.inclusion X n)
  exact hι

/-- Apply canonical scalar conversion to the original cocone and use its
native comparison to make the point the original genuine module sheaf. -/
def genuinePresentationCocone : Cocone (D ⋙ scalarLift X n) :=
  ((scalarLift X n).mapCocone (originalCoefficientCocone X n M D ι)).extend
    (canonicalModuleIso X n M).hom

/-- The actual transported cocone with original genuine point is a colimit. -/
def genuinePresentationCocone_isColimit
    (hι : IsColimit (Cocone.mk ((zmodUnderlying X n).obj M) ι)) :
    IsColimit (genuinePresentationCocone X n M D ι) := by
  have hPres : PreservesColimitsOfShape I (scalarLift X n) :=
    ((genuineModuleEquivalence X n).toAdjunction.leftAdjoint_preservesColimits :
      PreservesColimitsOfSize.{w, v} (scalarLift X n)).preservesColimitsOfShape
  have hD : PreservesColimit D (scalarLift X n) := hPres.preservesColimit
  exact IsColimit.extendIso (canonicalModuleIso X n M).hom
    (hD.preserves (originalCoefficientCocone_isColimit X n M D ι hι)).some

/-- Every original cocone map is recovered through the native scalar comparison. -/
theorem genuinePresentationCocone_underlying_ι (i : I) :
    (zmodUnderlying X n).map ((genuinePresentationCocone X n M D ι).ι.app i) =
      (scalarLiftUnderlyingIso X n).hom.app (D.obj i) ≫ ι.app i := by
  let f : D.obj i ⟶ (genuineCoefficientFunctor X n).obj M :=
    ObjectProperty.homMk (ι.app i)
  change (zmodUnderlying X n).map
      ((scalarLift X n).map f ≫
        (canonicalModuleIso X n M).hom) = _
  rw [Functor.map_comp, canonicalModuleIso_underlying_hom]
  exact (scalarLiftUnderlyingIso X n).hom.naturality f

/-- The underlying transported cocone is actually isomorphic to the original
cocone precomposed with its native diagram comparison. The point map is identity. -/
def genuinePresentationUnderlyingCoconeIso :
    (zmodUnderlying X n).mapCocone (genuinePresentationCocone X n M D ι) ≅
      (Cocone.precompose (scalarLiftDiagramUnderlyingIso X n D).hom).obj
        (Cocone.mk ((zmodUnderlying X n).obj M) ι) :=
  Cocone.ext (Iso.refl _) (by
    intro i
    change (zmodUnderlying X n).map
        ((genuinePresentationCocone X n M D ι).ι.app i) ≫
          𝟙 ((zmodUnderlying X n).obj M) =
      (scalarLiftUnderlyingIso X n).hom.app (D.obj i) ≫ ι.app i
    exact (Category.comp_id _).trans
      (genuinePresentationCocone_underlying_ι X n M D ι i))

end CoconeTransport

/-- Ambient finite presentability of the original stage is retained after
canonical scalar conversion and forgetting its genuine supplied action. -/
theorem scalarLiftStage_isFinitelyPresentable
    (F : BoundedPresentation.Coefficient X n)
    (hF : BoundedPresentation.finiteColimitStages X n F) :
    IsFinitelyPresentable.{u + 1}
      ((zmodUnderlying X n).obj ((scalarLift X n).obj F)) := by
  let P : ObjectProperty (AbelianSheaf.{u, u + 1} X) :=
    isCardinalPresentable.{u + 1, u + 1, u + 2}
      (AbelianSheaf.{u, u + 1} X) Cardinal.aleph0.{u + 1}
  have hP : P ((BoundedPresentation.inclusion X n).obj F) :=
    finiteColimitStage_isFinitelyPresentable X n F hF
  exact P.prop_of_iso ((scalarLiftUnderlyingIso X n).app F).symm hP

/-- Every original genuine module sheaf has the actual original filtered
bounded-coefficient presentation after canonical scalar conversion. Both
colimit cocones and every original underlying leg are retained, for all moduli. -/
theorem exists_filtered_genuine_presentation (M : ZModSheaf X n) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ BoundedPresentation.Coefficient X n)
      (ι : D ⋙ BoundedPresentation.inclusion X n ⟶
        (Functor.const I).obj ((zmodUnderlying X n).obj M))
      (κ : D ⋙ scalarLift X n ⟶ (Functor.const I).obj M),
      Nonempty (IsColimit (Cocone.mk ((zmodUnderlying X n).obj M) ι)) ∧
        Nonempty (IsColimit (Cocone.mk M κ)) ∧
        (∀ i, (zmodUnderlying X n).map (κ.app i) =
          (scalarLiftUnderlyingIso X n).hom.app (D.obj i) ≫ ι.app i) ∧
        ∀ i, BoundedPresentation.finiteColimitStages X n (D.obj i) ∧
          IsFinitelyPresentable.{u + 1}
            ((zmodUnderlying X n).obj ((D ⋙ scalarLift X n).obj i)) := by
  obtain ⟨I, hI, hfiltered, D, ι, ⟨hι⟩, hstage⟩ :=
    BoundedPresentation.exists_filtered_presentation X n
      ((zmodUnderlying X n).obj M) (zmodUnderlying_nsmul_id X n M)
  let := hI
  have : IsFiltered I := hfiltered
  refine ⟨I, hI, hfiltered, D, ι, (genuinePresentationCocone X n M D ι).ι,
    ⟨hι⟩, ⟨genuinePresentationCocone_isColimit X n M D ι hι⟩,
    genuinePresentationCocone_underlying_ι X n M D ι, ?_⟩
  exact fun i => ⟨hstage i, scalarLiftStage_isFinitelyPresentable X n (D.obj i) (hstage i)⟩

/-- At a nonzero modulus, actual finite-etale partitions of the original
generators give a genuine filtered presentation with geometrically
constructible and ambient finitely presentable underlying stages. Both
the genuine and the actual underlying cocones are colimits. -/
theorem exists_filtered_genuine_presentation_constructible_of_finiteEtalePartitions
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
          IsConstructible ((zmodUnderlying X n).obj (D.obj i)) := by
  obtain ⟨I, hI, hfiltered, D, ι, κ, _, ⟨hκ⟩, _, hstage⟩ :=
    exists_filtered_genuine_presentation X n M
  let := hI
  have : IsFiltered I := hfiltered
  refine ⟨I, hI, hfiltered, D ⋙ scalarLift X n, κ, ⟨hκ⟩,
    ⟨isColimitOfPreserves (zmodUnderlying X n) hκ⟩, ?_⟩
  intro i
  exact ⟨(hstage i).2,
    (isConstructible_iff_of_iso ((scalarLiftUnderlyingIso X n).app (D.obj i))).mpr
      (finiteColimitStage_isConstructible_of_finiteEtalePartitions
        X n hn hparts (D.obj i) (hstage i).1)⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
