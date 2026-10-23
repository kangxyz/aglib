/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.StageOverlapEquality
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.ChartRepresentativeTests
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.UnitRepresentativeEquality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.EtaleMatching
/-! # Native unit matching on base-changed charts -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- The actual base change of an etale chart as a native small-site object. -/
def baseChangeEtaleChart {S T : Scheme.{u}} (τ : T ⟶ S)
    (W : Over S) [Etale W.hom] : T.Etale :=
  Scheme.Etale.mk (pullback.fst τ W.hom)

/-- The structural triangle of an original base-changed representative. -/
theorem baseChangeChart_triangle {X S T : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (W : Over S) (U : X.Etale)
    (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r) :
    (pullback.snd τ W.hom ≫ a) ≫ U.hom = pullback.fst τ W.hom ≫ (τ ≫ r) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ pullback.snd τ W.hom ≫ z) ha).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z ↦ z ≫ r) pullback.condition.symm).trans
          (Category.assoc _ _ _))))

/-- The original unit test determined by a base-changed chart representative. -/
def baseChangeChartTest {X S T : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (W : Over S) [Etale W.hom] (U : X.Etale)
    (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r) :
    baseChangeEtaleChart τ W ⟶ (siteBaseChange (τ ≫ r)).obj U :=
  relativeChartTest (τ ≫ r) (baseChangeEtaleChart τ W) U
    (pullback.snd τ W.hom ≫ a) (baseChangeChart_triangle τ r W U a ha)

private theorem baseChangeChartTest_arrow {X S T : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (W : Over S) [Etale W.hom]
    (U : X.Etale) (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r) :
    unitRepresentativeArrow (τ ≫ r) (baseChangeChartTest τ r W U a ha) =
      Over.homMk (pullback.snd τ W.hom ≫ a)
        (baseChangeChart_triangle τ r W U a ha) :=
  unitRepresentativeArrow_relativeChartTest (τ ≫ r) (baseChangeEtaleChart τ W) U
    (pullback.snd τ W.hom ≫ a) (baseChangeChart_triangle τ r W U a ha)

/-- The original relative scheme underlying an overlap of base-changed charts. -/
def baseChangeOverlapSource {X S T : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (W V : Over S) [Etale W.hom] [Etale V.hom] : Over X :=
  Over.mk ((etaleOverlapChart (baseChangeEtaleChart τ W) (baseChangeEtaleChart τ V)).hom ≫
    (τ ≫ r))

/-- The geometric comparison from an overlap of base changes to the base
change of the original overlap, with its actual relative structural map. -/
def baseChangeOverlapArrow {X S T : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (W V : Over S) [Etale W.hom] [Etale V.hom] :
    Over.mk ((etaleOverlapChart (baseChangeEtaleChart τ W) (baseChangeEtaleChart τ V)).hom ≫
        (τ ≫ r)) ⟶
      relativeBaseChangeObject τ r (pullback.fst W.hom V.hom ≫ W.hom) :=
  Over.homMk (overlapBaseChangePair τ W.hom V.hom) (by
    let o := pullback.fst W.hom V.hom ≫ W.hom
    change overlapBaseChangePair τ W.hom V.hom ≫ (pullback.snd τ o ≫ o ≫ r) =
      (pullback.fst (pullback.fst τ W.hom) (pullback.fst τ V.hom) ≫
        pullback.fst τ W.hom) ≫ (τ ≫ r)
    exact (congrArg (fun z ↦ overlapBaseChangePair τ W.hom V.hom ≫ z)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z ↦ z ≫ r) pullback.condition.symm).trans
          (Category.assoc _ _ _)))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z ↦ z ≫ (τ ≫ r)) (pullback.lift_fst _ _ _))))

/-- The left triangle compares actual original test arrows, before applying
any section or inverse-image functor. -/
theorem baseChangeOverlapArrow_left_test {X S T : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (W V : Over S) [Etale W.hom] [Etale V.hom]
    (U : X.Etale) (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r) :
    baseChangeOverlapArrow τ r W V ≫
      (relativeBaseChangeOverlapLeft τ r W.hom V.hom ≫
        relativeBaseChangeRepresentative τ r W.hom U a ha) =
      unitRepresentativeArrow (τ ≫ r)
        (etaleOverlapFst (baseChangeEtaleChart τ W) (baseChangeEtaleChart τ V) ≫
          baseChangeChartTest τ r W U a ha) := by
  have ht : (baseChangeChartTest τ r W U a ha).left ≫ pullback.fst U.hom (τ ≫ r) =
      pullback.snd τ W.hom ≫ a :=
    congrArg (fun z ↦ z.left) (baseChangeChartTest_arrow τ r W U a ha)
  apply Over.OverMorphism.ext
  change overlapBaseChangePair τ W.hom V.hom ≫
      (overlapBaseChangeLeft τ W.hom V.hom ≫ (pullback.snd τ W.hom ≫ a)) =
    (pullback.fst (pullback.fst τ W.hom) (pullback.fst τ V.hom) ≫
      (baseChangeChartTest τ r W U a ha).left) ≫ pullback.fst U.hom (τ ≫ r)
  have hleft : overlapBaseChangePair τ W.hom V.hom ≫
      (overlapBaseChangeLeft τ W.hom V.hom ≫ (pullback.snd τ W.hom ≫ a)) =
      pullback.fst (pullback.fst τ W.hom) (pullback.fst τ V.hom) ≫
        (pullback.snd τ W.hom ≫ a) := by
    simp only [overlapBaseChangeLeft, pullback.lift_snd_assoc]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ a) (overlapBaseChangePair_left τ W.hom V.hom)).trans
        (Category.assoc _ _ _))
  exact hleft.trans ((Category.assoc _ _ _).trans
    (congrArg (fun z ↦ pullback.fst (pullback.fst τ W.hom)
      (pullback.fst τ V.hom) ≫ z) ht)).symm

/-- The right original-test triangle is likewise purely geometric. -/
theorem baseChangeOverlapArrow_right_test {X S T : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (W V : Over S) [Etale W.hom] [Etale V.hom]
    (U : X.Etale) (a : V.left ⟶ U.left) (ha : a ≫ U.hom = V.hom ≫ r) :
    baseChangeOverlapArrow τ r W V ≫
      (relativeBaseChangeOverlapRight τ r W.hom V.hom ≫
        relativeBaseChangeRepresentative τ r V.hom U a ha) =
      unitRepresentativeArrow (τ ≫ r)
        (etaleOverlapSnd (baseChangeEtaleChart τ W) (baseChangeEtaleChart τ V) ≫
          baseChangeChartTest τ r V U a ha) := by
  have ht : (baseChangeChartTest τ r V U a ha).left ≫ pullback.fst U.hom (τ ≫ r) =
      pullback.snd τ V.hom ≫ a :=
    congrArg (fun z ↦ z.left) (baseChangeChartTest_arrow τ r V U a ha)
  apply Over.OverMorphism.ext
  change overlapBaseChangePair τ W.hom V.hom ≫
      (overlapBaseChangeRight τ W.hom V.hom ≫ (pullback.snd τ V.hom ≫ a)) =
    (pullback.snd (pullback.fst τ W.hom) (pullback.fst τ V.hom) ≫
      (baseChangeChartTest τ r V U a ha).left) ≫ pullback.fst U.hom (τ ≫ r)
  have hright : overlapBaseChangePair τ W.hom V.hom ≫
      (overlapBaseChangeRight τ W.hom V.hom ≫ (pullback.snd τ V.hom ≫ a)) =
      pullback.snd (pullback.fst τ W.hom) (pullback.fst τ V.hom) ≫
        (pullback.snd τ V.hom ≫ a) := by
    simp only [overlapBaseChangeRight, pullback.lift_snd_assoc]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ a) (overlapBaseChangePair_right τ W.hom V.hom)).trans
        (Category.assoc _ _ _))
  exact hright.trans ((Category.assoc _ _ _).trans
    (congrArg (fun z ↦ pullback.snd (pullback.fst τ W.hom)
      (pullback.fst τ V.hom) ≫ z) ht)).symm

private theorem restrict_matching_representatives {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y Z : Over X} (U V : X.Etale)
    (A : Y ⟶ Z) (L : Z ⟶ (Etale.forget X).obj U)
    (R : Z ⟶ (Etale.forget X).obj V)
    (a : Y ⟶ (Etale.forget X).obj U) (b : Y ⟶ (Etale.forget X).obj V)
    (ha : A ≫ L = a) (hb : A ≫ R = b)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (h : etaleRepresentativeSection F Z U L s = etaleRepresentativeSection F Z V R t) :
    etaleRepresentativeSection F Y U a s = etaleRepresentativeSection F Y V b t := by
  have heq := (etaleRepresentativeSection_restrict F A U L s).symm.trans
    ((congrArg ((pullbackSectionsFunctor F).map A.op) h).trans
      (etaleRepresentativeSection_restrict F A V R t))
  exact (congrArg (fun q ↦ etaleRepresentativeSection F Y U q s) ha).symm.trans
    (heq.trans (congrArg (fun q ↦ etaleRepresentativeSection F Y V q t) hb))

private theorem baseChange_overlap_representatives
    {X S T : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} (W : J → Over S)
    [∀ j, Etale (W j).hom] (U : J → X.Etale)
    (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (h : BaseChangeOverlapMatching τ r F W U a ha t) (j k : J) :
    etaleRepresentativeSection F (Over.mk ((etaleOverlapChart
      (baseChangeEtaleChart τ (W j)) (baseChangeEtaleChart τ (W k))).hom ≫ (τ ≫ r))) (U j)
      (unitRepresentativeArrow (τ ≫ r)
        (etaleOverlapFst (baseChangeEtaleChart τ (W j)) (baseChangeEtaleChart τ (W k)) ≫
          baseChangeChartTest τ r (W j) (U j) (a j) (ha j))) (t j) =
    etaleRepresentativeSection F (Over.mk ((etaleOverlapChart
      (baseChangeEtaleChart τ (W j)) (baseChangeEtaleChart τ (W k))).hom ≫ (τ ≫ r))) (U k)
      (unitRepresentativeArrow (τ ≫ r)
        (etaleOverlapSnd (baseChangeEtaleChart τ (W j)) (baseChangeEtaleChart τ (W k)) ≫
          baseChangeChartTest τ r (W k) (U k) (a k) (ha k))) (t k) := by
  exact restrict_matching_representatives F (U j) (U k)
    (baseChangeOverlapArrow τ r (W j) (W k))
    (relativeBaseChangeOverlapLeft τ r (W j).hom (W k).hom ≫
      relativeBaseChangeRepresentative τ r (W j).hom (U j) (a j) (ha j))
    (relativeBaseChangeOverlapRight τ r (W j).hom (W k).hom ≫
      relativeBaseChangeRepresentative τ r (W k).hom (U k) (a k) (ha k))
    (unitRepresentativeArrow (τ ≫ r)
      (etaleOverlapFst (baseChangeEtaleChart τ (W j)) (baseChangeEtaleChart τ (W k)) ≫
        baseChangeChartTest τ r (W j) (U j) (a j) (ha j)))
    (unitRepresentativeArrow (τ ≫ r)
      (etaleOverlapSnd (baseChangeEtaleChart τ (W j)) (baseChangeEtaleChart τ (W k)) ≫
        baseChangeChartTest τ r (W k) (U k) (a k) (ha k)))
    (baseChangeOverlapArrow_left_test τ r (W j) (W k) (U j) (a j) (ha j))
    (baseChangeOverlapArrow_right_test τ r (W j) (W k) (U k) (a k) (ha k))
    (t j) (t k) (h j k)


private theorem baseChange_unitSections_overlap
    {X S T : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} (W : J → Over S)
    [∀ j, Etale (W j).hom] (U : J → X.Etale)
    (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (h : BaseChangeOverlapMatching τ r F W U a ha t) (j k : J) :
    ((inverseImage (τ ≫ r)).obj F).obj.map
      (etaleOverlapFst (baseChangeEtaleChart τ (W j)) (baseChangeEtaleChart τ (W k))).op
        (unitSectionMap (τ ≫ r) F (baseChangeChartTest τ r (W j) (U j) (a j) (ha j)) (t j)) =
    ((inverseImage (τ ≫ r)).obj F).obj.map
      (etaleOverlapSnd (baseChangeEtaleChart τ (W j)) (baseChangeEtaleChart τ (W k))).op
        (unitSectionMap (τ ≫ r) F (baseChangeChartTest τ r (W k) (U k) (a k) (ha k)) (t k)) := by
  let V (j : J) := baseChangeEtaleChart τ (W j)
  let b (j : J) := baseChangeChartTest τ r (W j) (U j) (a j) (ha j)
  let p' := etaleOverlapFst (V j) (V k)
  let q' := etaleOverlapSnd (V j) (V k)
  have hu := (unitSectionMap_eq_iff_representative_eq (τ ≫ r) F
    (etaleOverlapChart (V j) (V k)) (U j) (U k) (p' ≫ b j) (q' ≫ b k)
      (t j) (t k)).mpr (baseChange_overlap_representatives τ r F W U a ha t h j k)
  have hup := (ConcreteCategory.comp_apply (unitSectionMap (τ ≫ r) F (b j))
    (((inverseImage (τ ≫ r)).obj F).obj.map p'.op) (t j)).symm.trans
      (ConcreteCategory.congr_hom (unitSectionMap_precomp (τ ≫ r) F (b j) p') (t j))
  have huq := (ConcreteCategory.comp_apply (unitSectionMap (τ ≫ r) F (b k))
    (((inverseImage (τ ≫ r)).obj F).obj.map q'.op) (t k)).symm.trans
      (ConcreteCategory.congr_hom (unitSectionMap_precomp (τ ≫ r) F (b k) q') (t k))
  exact hup.trans (hu.trans huq.symm)

/-- Actual overlap matching yields matching in the original inverse-image
sheaf, along the original base-changed charts and original unit tests. -/
theorem baseChange_unitSections_compatible
    {X S T : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} (W : J → Over S)
    [∀ j, Etale (W j).hom] (U : J → X.Etale)
    (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (h : BaseChangeOverlapMatching τ r F W U a ha t) :
    Presieve.Arrows.Compatible
      (((inverseImage (τ ≫ r)).obj F).obj ⋙ CategoryTheory.forget Ab.{u + 1})
      (fun j ↦ (etaleTerminalIsTerminal T).from (baseChangeEtaleChart τ (W j)))
      (fun j ↦ unitSectionMap (τ ≫ r) F (baseChangeChartTest τ r (W j) (U j) (a j) (ha j))
        (t j)) := by
  apply nativeSections_compatible_of_scheme_pullbacks ((inverseImage (τ ≫ r)).obj F).obj
    (fun j ↦ baseChangeEtaleChart τ (W j))
  exact baseChange_unitSections_overlap τ r F W U a ha t h

end AlgebraicGeometry.Scheme.EtaleAffineBasis
