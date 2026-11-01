/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CartesianExchangeNormalization
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionBaseChangeSource
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.CompositionBCRawSource
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.CompositionBCRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIsoRefinement
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoNaturality

/-! # The original chosen Cartesian exchange on an actual supplied model

The literal normalized model is transported on its actual source. The original
mixed refinement to the supplied model, source-transport naturality and original
raw transition composition compute the given exchange without identifying any
independent derived-model families.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
private theorem iso_trans_whisker_self_hom
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {F : A ⥤ C} {V : A ⥤ B} {G : B ⥤ C}
    (s : F ≅ V ⋙ G) (t : G ≅ G) (ht : t = Iso.refl G) :
    (s ≪≫ Functor.isoWhiskerLeft V t).hom = s.hom := by
  rw [ht, Functor.isoWhiskerLeft_refl, Iso.trans_refl]

universe u wX wS wL wT wX' wM wN wP wR

variable {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
  (b : T ⟶ S) (a : X' ⟶ X) (sq : IsPullback a f' f b)
  [QuasiCompact f] [QuasiCompact f']
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [hL : HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [hT : HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [literalModels : ∀ D : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]
  [presentationModels : ∀ E : Hom.DenseCompactification f',
    HasDerivedCategory.{wP} (ModuleSheaf E.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]
  (C : Hom.DenseCompactification f) (E : Hom.DenseCompactification f')
  (q : E.Xbar ⟶ C.Xbar) (hj : IsPullback a E.j C.j q) (hp : q ≫ C.p = E.p ≫ b)

local notation "D" => Hom.DenseCompactification.baseChangeObj b C
local notation "R" => C.toCompactification.baseChange b
local notation "e" => sq.flip.isoPullback
local notation "he" => sq.flip.isoPullback_hom_fst
local notation "Dt" => Functor.obj (Hom.DenseCompactification.sourceIso f' e he) D
local notation "Rt" => Hom.Compactification.ofSourceIso R f' e he
local notation "n" => Hom.DenseCompactification.baseChangeNormalization b C
local notation "r" =>
  Hom.DenseCompactification.cartesianSourceRefinement C f' a b sq E q hj.w.symm hp

/-- The local derived-category model on `ModuleSheaf C.Xbar Λ`. -/
local instance compositionChosenOldModel : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) :=
  sourceModels C
/-- The local derived-category model on `ModuleSheaf (D).Xbar Λ`. -/
local instance compositionChosenLiteralModel : HasDerivedCategory.{wN} (ModuleSheaf (D).Xbar Λ) :=
  literalModels D
/-- The local derived-category model on `ModuleSheaf E.Xbar Λ`. -/
local instance compositionChosenFinalModel : HasDerivedCategory.{wP} (ModuleSheaf E.Xbar Λ) :=
  presentationModels E
/-- The local derived-category model on `ModuleSheaf (R).Xbar Λ`. -/
local instance compositionChosenRawModel : HasDerivedCategory.{wR} (ModuleSheaf (R).Xbar Λ) :=
  rawModels C
/-- The local derived-category model on `ModuleSheaf (Dt).Xbar Λ`. -/
local instance compositionChosenTransportDenseModel :
    HasDerivedCategory.{wN} (ModuleSheaf (Dt).Xbar Λ) := literalModels D
/-- The local derived-category model on `ModuleSheaf (Rt).Xbar Λ`. -/
local instance compositionChosenTransportRawModel :
    HasDerivedCategory.{wR} (ModuleSheaf (Rt).Xbar Λ) := rawModels C

/-- The actual given Cartesian exchange equals the original compactified commuting map
on every supplied dense target model carrying an actual compatible ambient map. -/
theorem moduleCompactificationCartesianBaseChangeIsoTo_commuting :
    (moduleCompactificationCartesianBaseChangeIsoTo f f' b a sq Λ C D E).hom =
      moduleRawCommutingSquareMap C.toCompactification E.toCompactification a q b hj hp.symm Λ := by
  have sqn : IsPullback (Dt).j (𝟙 X') n (Rt).j := by
    let hn : Mono (show (Dt).Xbar ⟶ (Rt).Xbar from n) :=
      inferInstanceAs (Mono (Hom.DenseCompactification.baseChangeNormalization b C))
    apply IsPullback.flip
    apply @IsPullback.of_horiz_isIso_mono Scheme _ X' X' (Dt).Xbar (Rt).Xbar
      (𝟙 X') (Dt).j (Rt).j n inferInstance hn
    refine ⟨?_⟩
    change 𝟙 X' ≫ ((e).hom ≫ (R).j) = ((e).hom ≫ (D).j) ≫ n
    exact (Category.id_comp _).trans
      ((congrArg (fun k => (e).hom ≫ k)
        (Hom.DenseCompactification.baseChange_j_normalization b C).symm).trans
          (Category.assoc _ _ _).symm)
  let sqr := Hom.DenseCompactification.isPullback_open r
  have sqt : IsPullback E.j (𝟙 X') ((r).hom ≫ n) (Rt).j := by
    have hh := sqr.paste_vert sqn
    rw [Category.comp_id] at hh
    exact hh
  have hpt : ((r).hom ≫ n) ≫ (Rt).p = E.p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => (r).hom ≫ k)
        (Hom.DenseCompactification.baseChangeNormalization_fst b C)).trans (r).base_fac)
  have hqt : ((r).hom ≫ n) ≫ pullback.snd b C.p = q :=
    (Category.assoc _ _ _).trans
      (Hom.DenseCompactification.cartesianSourceRefinement_projection C f' a b sq E q hj.w.symm hp)
  let d := moduleCompactificationDensificationMap R Λ
  let dt := @moduleRawCompactificationTransition X' T f'
    (Dt).toCompactification Rt n sqn
    (Hom.DenseCompactification.baseChangeNormalization_fst b C) Λ _
    hX' hT (literalModels D) (rawModels C)
  let tr := @moduleRawCompactificationTransition X' T f'
    E.toCompactification (Dt).toCompactification (r).hom sqr (r).base_fac Λ _
    hX' hT (presentationModels E) (literalModels D)
  let t := @moduleRawCompactificationTransition X' T f'
    E.toCompactification Rt ((r).hom ≫ n) sqt hpt Λ _
    hX' hT (presentationModels E) (rawModels C)
  let βraw := moduleRawCompactificationBaseChangeIso C.toCompactification b Λ
  let βdense := moduleCompactificationBaseChangeIsoTo f b Λ C D
  let ψraw := moduleRawCompactificationSourceIso e Λ f' he R
  let ψdense := moduleRawCompactificationSourceIso e Λ f' he (D).toCompactification
  let ψfinal := moduleCompactificationSourceIsoTo (pullback.fst b f) f' e he Λ D E
  let c := moduleCartesianBaseChangeSourceIso f f' b a sq Λ
  let sqRaw := Hom.Compactification.isPullback_cartesianBaseChange_open
    C.toCompactification f' a b sq
  let sqProper := (IsPullback.of_hasPullback b C.p).flip
  let βr := @moduleRawSquareMap X S X' T f f'
    C.toCompactification Rt a (pullback.snd b C.p) b sqRaw sqProper Λ _
    hX hS (sourceModels C) hX' hT (rawModels C)
  have hb : βdense.hom = βraw.hom ≫
      Functor.whiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ) d := by
    exact (iso_trans_whisker_self_hom
      (moduleNormalizedCompactificationBaseChangeIso C b Λ)
      (moduleCompactificationComparison (pullback.fst b f) Λ D D)
      (moduleCompactificationComparison_self (pullback.fst b f) Λ D)).trans
        (moduleNormalizedCompactificationBaseChangeIso_hom C b Λ)
  have hs : ψfinal.hom = ψdense.hom ≫
      Functor.whiskerLeft (moduleDerivedInverseImageTorsion (e).hom Λ) tr := by
    exact congrArg Iso.hom
      (moduleCompactificationSourceIsoTo_refinement (pullback.fst b f) f' e he Λ D r)
  have hn : d ≫ ψdense.hom = ψraw.hom ≫
      Functor.whiskerLeft (moduleDerivedInverseImageTorsion (e).hom Λ) dt :=
    moduleRawCompactificationSourceIso_refinement_naturality e f' he
      (D).toCompactification R n (Hom.Compactification.isPullback_densify R) sqn
      (Hom.DenseCompactification.baseChangeNormalization_fst b C) Λ
  have ht : dt ≫ tr = t :=
    (@moduleRawCompactificationTransition_comp X' T f'
      E.toCompactification (Dt).toCompactification (r).hom sqr (r).base_fac Λ _
      hX' hT (presentationModels E) (literalModels D) Rt n sqn
      (Hom.DenseCompactification.baseChangeNormalization_fst b C) sqt hpt (rawModels C)).symm
  have hr : (cartesianSourceExchange βraw ψraw c).hom = βr :=
    moduleRawCartesianPresentation f f' b a sq C.toCompactification Λ
  have hq : moduleRawCommutingSquareMap C.toCompactification E.toCompactification
      a q b hj hp.symm Λ = βr ≫ Functor.whiskerLeft (moduleDerivedInverseImageTorsion a Λ) t :=
    @moduleRawCommutingSquareMap_refinement X S X' T f f'
      C.toCompactification Rt a (pullback.snd b C.p) b sqRaw sqProper.w.symm Λ _
      hX hS hX' hT (sourceModels C) (rawModels C) E.toCompactification
      ((r).hom ≫ n) sqt hpt q hqt hj hp.symm (presentationModels E)
  exact cartesianExchangeNormalization βraw βdense ψraw ψdense ψfinal c d dt tr t
    βr (moduleRawCommutingSquareMap C.toCompactification E.toCompactification a q b hj hp.symm Λ)
    hb hs hn ht hr hq

end AlgebraicGeometry.Scheme.EtaleCohomology
