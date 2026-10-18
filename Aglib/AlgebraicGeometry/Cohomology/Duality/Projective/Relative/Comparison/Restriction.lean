/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.OpenCoefficients
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.OpenSingle
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.OpenShift
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext

/-!
# Original source and target restriction maps for relative Serre comparison

The source uses the native exact-single restriction of Ext. The target uses
the original derived open base change and single-coefficient counit. Affine
open direct images make these actual maps bijective by the original pointwise
adjunction, without a trace or duality hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace AlgebraicGeometry.Scheme.Cohomology

variable {W X U Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ U) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)

/-- The original exact open restriction of an Ext class, with the actual differential
coefficient comparison and native exact-single maps. -/
def relativeProjectiveExtRestriction (n : ℕ) (N : Y.Modules) (M : X.Modules) (r : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) r) :
    Ext.{u + 1} (M.restrict i)
      ((relativeTopDifferentialCoefficientsFunctor q n).obj (N.restrict j)) r :=
  (Ext.homPlusAddEquiv r).symm
    (((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).inv.app M ≫
      x.homPlus.map (Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlus ≫
      (shiftFunctor (DerivedCategory.Plus W.Modules) (r : ℤ)).map
        (((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).hom.app
            ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
          (DerivedCategory.Plus.singleFunctor W.Modules 0).map
            ((relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).hom.app N)))

/-- The restricted Ext class retains the displayed original shifted derived representative. -/
theorem relativeProjectiveExtRestriction_homPlus
    (n : ℕ) (N : Y.Modules) (M : X.Modules) (r : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) r) :
    (relativeProjectiveExtRestriction p i q j H n N M r x).homPlus =
      ((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).inv.app M ≫
        x.homPlus.map (Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlus ≫
        (shiftFunctor (DerivedCategory.Plus W.Modules) (r : ℤ)).map
          (((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).hom.app
              ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
            (DerivedCategory.Plus.singleFunctor W.Modules 0).map
              ((relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).hom.app N)) :=
  (Ext.homPlusAddEquiv r).apply_symm_apply _

/-- Native derived open base change followed by the original exact-single comparison. -/
def relativeProjectiveSourceRestrictionIso (M : X.Modules) :
    (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus.obj
        ((Scheme.Modules.derivedPushforwardPlus p).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ≅
      (Scheme.Modules.derivedPushforwardPlus q).obj
        ((DerivedCategory.Plus.singleFunctor W.Modules 0).obj (M.restrict i)) :=
  (Scheme.Modules.derivedOpenBaseChangeIso i q p j H).app
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≪≫
    (Scheme.Modules.derivedPushforwardPlus q).mapIso
      (((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).app M)

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem shiftedHom_map_precomp {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
    {X' X Y : C} (d : X' ⟶ X) {r : ℤ} (a : ShiftedHom X Y r) :
    (show ShiftedHom X' Y r from d ≫ a).map F = F.map d ≫ a.map F := by
  rw [← ShiftedHom.mk₀_comp (0 : ℤ) rfl d, ShiftedHom.map_comp,
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp]

variable {W X U Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ U) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)

/-- Original derived open restriction, native source base change, and the original
coefficient counit on the target of the Serre comparison. -/
def relativeOpenTargetRestriction (L : U.Modules) (M : X.Modules) (n r : ℤ)
    (a : ShiftedHom ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))
      ((DerivedCategory.Plus.singleFunctor Y.Modules n).obj
        ((Scheme.Modules.pushforward j).obj L)) r) :
    ShiftedHom ((Scheme.Modules.derivedPushforwardPlus q).obj
        ((DerivedCategory.Plus.singleFunctor W.Modules 0).obj (M.restrict i)))
      ((DerivedCategory.Plus.singleFunctor U.Modules n).obj L) r :=
  (relativeProjectiveSourceRestrictionIso p i q j H M).inv ≫
    a.map (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus ≫
    (((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusSingleIso n).hom.app
        ((Scheme.Modules.pushforward j).obj L) ≫
      (DerivedCategory.Plus.singleFunctor U.Modules n).map
        ((Scheme.Modules.restrictAdjunction j).counit.app L))⟦r⟧'

/-- For an affine open and quasicoherent coefficient, the actual target restriction map
is bijective. The source can be any module, and both displayed degrees are arbitrary integers. -/
theorem relativeOpenTargetRestriction_bijective [IsAffineHom j]
    (L : U.Modules) [L.IsQuasicoherent] (M : X.Modules) (n r : ℤ) :
    Function.Bijective (relativeOpenTargetRestriction p i q j H L M n r) := by
  let P := Scheme.Modules.pushforward p
  let J := (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus
  let I := injectiveResolution M
  let K := P.mapCochainComplexPlus.obj I.cochainComplexPlus
  let D := I.rightDerivedFunctorPlusIso P
  let C := relativeProjectiveSourceRestrictionIso p i q j H M
  let S := J.mapIso D ≪≫ C
  let E₁ := Iso.homCongr D.symm
    (Iso.refl (((DerivedCategory.Plus.singleFunctor Y.Modules n).obj
      ((Scheme.Modules.pushforward j).obj L))⟦r⟧))
  let E₂ := Iso.homCongr S
    (Iso.refl (((DerivedCategory.Plus.singleFunctor U.Modules n).obj L)⟦r⟧))
  have heq : relativeOpenTargetRestriction p i q j H L M n r =
      E₂ ∘ (openSingleDerivedHomRestriction j L K n r ∘ E₁) := by
    funext a
    simp only [Function.comp_apply, E₁, E₂, Iso.homCongr_apply,
      Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [openSingleDerivedHomRestriction, shiftedHom_map_precomp]
    change C.inv ≫ a.map J ≫ _ = _
    simp only [S, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
    rw [← J.map_comp_assoc, D.inv_hom_id]
    erw [J.map_id, Category.id_comp]
  rw [heq]
  exact E₂.bijective.comp
    ((affineOpenSingleDerivedHomRestriction_bijective j L K n r).comp E₁.bijective)

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem shiftedHom_map_postcomp {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
    {X Y Z : C} {r : ℤ} (a : ShiftedHom X Y r) (d : Y ⟶ Z) :
    (show ShiftedHom X Z r from a ≫ d⟦r⟧').map F = a.map F ≫ (F.map d)⟦r⟧' := by
  rw [← ShiftedHom.comp_mk₀ a (0 : ℤ) rfl d, ShiftedHom.map_comp,
    ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀]

variable {X Y U : Scheme.{u}} (p : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j] (n : ℕ)

/-- The original coefficient comparison becomes the original coefficient restriction and
base counit under the actual source restriction adjunction. -/
theorem relativeTopDifferentialOpenPushforwardMap_restrict_counit (L : U.Modules) :
    (Scheme.Modules.restrictFunctor (pullback.snd j p)).map
        (relativeTopDifferentialOpenPushforwardMap p j n L) ≫
      (Scheme.Modules.restrictAdjunction (pullback.snd j p)).counit.app
        ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L) =
    (relativeTopDifferentialCoefficientsRestrictionIso p (pullback.snd j p)
        (pullback.fst j p) j (IsPullback.of_hasPullback j p).flip.w n).hom.app
          ((Scheme.Modules.pushforward j).obj L) ≫
      (relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).map
        ((Scheme.Modules.restrictAdjunction j).counit.app L) := by
  erw [← Adjunction.homEquiv_counit]
  rw [relativeTopDifferentialOpenPushforwardMap_eq_restrictHomEquiv]
  exact Equiv.symm_apply_apply _ _

/-- Actual Ext restriction followed by the original base coefficient counit. -/
def relativeOpenSourceRestriction (L : U.Modules) (M : X.Modules) (r : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj
      ((Scheme.Modules.pushforward j).obj L)) r) :
    Ext.{u + 1} (M.restrict (pullback.snd j p))
      ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L) r :=
  (relativeProjectiveExtRestriction p (pullback.snd j p) (pullback.fst j p) j
    (IsPullback.of_hasPullback j p).flip n ((Scheme.Modules.pushforward j).obj L) M r x).comp
      (Ext.mk₀ ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).map
        ((Scheme.Modules.restrictAdjunction j).counit.app L))) (Nat.add_zero r)

/-- The original source map is the native affine-open adjunction map after the actual
ordinary coefficient comparison; this equation retains the original two counits. -/
theorem relativeOpenSourceRestriction_homPlus (L : U.Modules) (M : X.Modules) (r : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj
      ((Scheme.Modules.pushforward j).obj L)) r) :
    (relativeOpenSourceRestriction p j n L M r x).homPlus =
      ((Scheme.Modules.restrictFunctor (pullback.snd j p)).rightDerivedFunctorPlusSingleIso
        0).inv.app M ≫
        openSingleDerivedHomRestriction (pullback.snd j p)
          ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L)
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) 0 (r : ℤ)
          (x.homPlus ≫
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
              (relativeTopDifferentialOpenPushforwardMap p j n L))⟦(r : ℤ)⟧') := by
  let i := pullback.snd j p
  let q := pullback.fst j p
  let A := Scheme.Modules.restrictFunctor i
  let B := relativeTopDifferentialCoefficientsFunctor q n
  let V := (relativeTopDifferentialCoefficientsFunctor p n).obj
    ((Scheme.Modules.pushforward j).obj L)
  let c := (relativeTopDifferentialCoefficientsRestrictionIso p i q j
    (IsPullback.of_hasPullback j p).flip.w n).hom.app ((Scheme.Modules.pushforward j).obj L)
  let d := B.map ((Scheme.Modules.restrictAdjunction j).counit.app L)
  let β := relativeTopDifferentialOpenPushforwardMap p j n L
  let S := DerivedCategory.Plus.singleFunctor (pullback j p).Modules 0
  have hm : A.map β ≫ (Scheme.Modules.restrictAdjunction i).counit.app (B.obj L) = c ≫ d :=
    relativeTopDifferentialOpenPushforwardMap_restrict_counit p j n L
  have hn := (A.rightDerivedFunctorPlusSingleIso 0).hom.naturality β
  change A.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map β) ≫
      (A.rightDerivedFunctorPlusSingleIso 0).hom.app _ =
    (A.rightDerivedFunctorPlusSingleIso 0).hom.app V ≫ S.map (A.map β) at hn
  have hc : A.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map β) ≫
      (A.rightDerivedFunctorPlusSingleIso 0).hom.app
        ((Scheme.Modules.pushforward i).obj (B.obj L)) ≫
      S.map ((Scheme.Modules.restrictAdjunction i).counit.app (B.obj L)) =
    (A.rightDerivedFunctorPlusSingleIso 0).hom.app V ≫ S.map (c ≫ d) := by
    rw [← Category.assoc, hn, Category.assoc, ← S.map_comp, hm]
  have hcs := congrArg
    ((shiftFunctor (DerivedCategory.Plus (pullback j p).Modules) (r : ℤ)).map) hc
  simp only [Functor.map_comp] at hcs
  rw [relativeOpenSourceRestriction, Ext.homPlus_comp, Ext.homPlus_mk₀]
  erw [ShiftedHom.comp_mk₀, relativeProjectiveExtRestriction_homPlus,
    openSingleDerivedHomRestriction, shiftedHom_map_postcomp]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun z => (A.rightDerivedFunctorPlusSingleIso 0).inv.app M ≫
    x.homPlus.map A.rightDerivedFunctorPlus ≫ z) hcs.symm

/-- For an affine open, the actual source restriction/counit map is bijective whenever
the original differential-coefficient comparison is invertible. Projective geometry
supplies the displayed locally-free and quasicoherence properties. -/
theorem relativeOpenSourceRestriction_bijective [IsAffineHom j]
    [IsFiniteLocallyFree X (moduleExteriorPower X (relativeDifferentialSheaf p) n)]
    (L : U.Modules) [L.IsQuasicoherent]
    [((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L).IsQuasicoherent]
    (M : X.Modules) (r : ℕ) :
    Function.Bijective (relativeOpenSourceRestriction p j n L M r) := by
  let i := pullback.snd j p
  let : IsAffineHom i := MorphismProperty.pullback_snd j p inferInstance
  let q := pullback.fst j p
  let V := (relativeTopDifferentialCoefficientsFunctor p n).obj
    ((Scheme.Modules.pushforward j).obj L)
  let L' := (relativeTopDifferentialCoefficientsFunctor q n).obj L
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let β := relativeTopDifferentialOpenPushforwardIso p j n L
  let sM := ((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).app M
  let E₁ := (Ext.homPlusAddEquiv (X := M) (Y := V) r).toEquiv
  let E₂ := Iso.homCongr
    (Iso.refl ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))
    ((shiftFunctor (DerivedCategory.Plus X.Modules) (r : ℤ)).mapIso
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).mapIso β))
  let E₃ := Iso.homCongr sM
    (Iso.refl (((DerivedCategory.Plus.singleFunctor (pullback j p).Modules 0).obj
      L')⟦(r : ℤ)⟧))
  have heq : (fun x => (relativeOpenSourceRestriction p j n L M r x).homPlus) =
      E₃ ∘ (openSingleDerivedHomRestriction i L' K 0 (r : ℤ) ∘ (E₂ ∘ E₁)) := by
    funext x
    rw [relativeOpenSourceRestriction_homPlus]
    simp only [E₁, E₂, E₃, Function.comp_apply, Iso.homCongr_apply,
      Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id,
      Functor.mapIso_hom]
    rfl
  have hb : Function.Bijective
      (fun x => (relativeOpenSourceRestriction p j n L M r x).homPlus) := by
    rw [heq]
    exact E₃.bijective.comp
      ((affineOpenSingleDerivedHomRestriction_bijective i L' K 0 (r : ℤ)).comp
        (E₂.bijective.comp E₁.bijective))
  exact (Equiv.comp_bijective (relativeOpenSourceRestriction p j n L M r)
    (Ext.homPlusAddEquiv (X := M.restrict i) (Y := L') r).toEquiv).mp hb

end AlgebraicGeometry.Scheme.Cohomology
