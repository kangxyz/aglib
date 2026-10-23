/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.NativeStageAmalgamation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.NativeEtaleSectionRestriction
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeEquation

/-! # The original projection image of a native stage amalgamation -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u v

open EtaleAffineBasis
attribute [local instance] hasSheafifyLarge

private theorem square_values {C : Type*} [Category* C]
    (P : Cᵒᵖ ⥤ Ab.{u + 1}) {Y Z B D : C}
    (A : Y ⟶ Z) (L : Z ⟶ B) (R : Y ⟶ D) (Q : D ⟶ B)
    (hA : A ≫ L = R ≫ Q) (v : P.obj (op B)) (s : P.obj (op D))
    (x : P.obj (op Z)) (y : P.obj (op Y))
    (hv : P.map L.op v = x) (hs : P.map R.op s = y) (hxy : P.map A.op x = y) :
    P.map R.op (P.map Q.op v) = P.map R.op s := by
  have heq := congrArg (P.map A.op) hv
  have hleft := ConcreteCategory.congr_hom (P.map_comp L.op A.op) v
  have hright := ConcreteCategory.congr_hom (P.map_comp Q.op R.op) v
  have hmap := congrArg P.map (congrArg Quiver.Hom.op hA)
  exact hright.symm.trans ((ConcreteCategory.congr_hom hmap v).symm.trans
    (hleft.trans (heq.trans (hxy.trans hs.symm))))

/-- A single original local square transports its prescribed representative.
The coefficient is fixed before any pullback-chart geometry is substituted. -/
theorem native_local_image_of_representatives {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y Z B C : Over X} (U : X.Etale)
    (A : Y ⟶ Z) (L : Z ⟶ B) (R : Y ⟶ C) (Q : C ⟶ B)
    (a : Z ⟶ (Etale.forget X).obj U) (b : Y ⟶ (Etale.forget X).obj U)
    (hA : A ≫ L = R ≫ Q) (ha : A ≫ a = b)
    (v : (pullbackSectionsFunctor F).obj (op B))
    (s : (pullbackSectionsFunctor F).obj (op C)) (t : F.obj.obj (op U))
    (hv : (pullbackSectionsFunctor F).map L.op v =
      etaleRepresentativeSection F Z U a t)
    (hs : (pullbackSectionsFunctor F).map R.op s =
      etaleRepresentativeSection F Y U b t) :
    (pullbackSectionsFunctor F).map R.op ((pullbackSectionsFunctor F).map Q.op v) =
      (pullbackSectionsFunctor F).map R.op s := by
  have hxy : (pullbackSectionsFunctor F).map A.op
      (etaleRepresentativeSection F Z U a t) = etaleRepresentativeSection F Y U b t :=
    (etaleRepresentativeSection_restrict F A U a t).trans
      (congrArg (fun z : Y ⟶ (Etale.forget X).obj U ↦
        etaleRepresentativeSection F Y U z t) ha)
  exact square_values (pullbackSectionsFunctor F) A L R Q hA v s _ _ hv hs hxy

/-- A raw relative pullback chart maps to the actual source object by its
original first projection. Only its geometric structural triangle is normalized. -/
def nativeRelativeBaseChangeSource {X S : Scheme.{u}} (C : Over X)
    (σ : C.left ⟶ S) (r : S ⟶ X) (hC : σ ≫ r = C.hom) (W : Over S) :
    relativeBaseChangeObject σ r W.hom ⟶ C :=
  Over.homMk (pullback.fst σ W.hom) (by
    change pullback.fst σ W.hom ≫ C.hom = pullback.snd σ W.hom ≫ W.hom ≫ r
    rw [← hC, ← Category.assoc, pullback.condition, Category.assoc])

instance nativeRelativeBaseChangeSource_etale {X S : Scheme.{u}} (C : Over X)
    (σ : C.left ⟶ S) (r : S ⟶ X) (hC : σ ≫ r = C.hom)
    (W : Over S) [Etale W.hom] : Etale (nativeRelativeBaseChangeSource C σ r hC W).left :=
  inferInstanceAs (Etale (pullback.fst σ W.hom))

/-- The literal native relative-projection charts cover the original source.
This geometric proof does not compare two site families under a coefficient
functor: it proves the required native cover directly by surjectivity. -/
theorem nativeRelativeBaseChangeSource_covering {X S : Scheme.{u}} (C : Over X)
    (σ : C.left ⟶ S) (r : S ⟶ X) (hC : σ ≫ r = C.hom)
    {J : Type v} (W : J → Over S) [∀ j, Etale (W j).hom]
    (hcover : ∀ x : S, ∃ j, ∃ y : (W j).left, (W j).hom y = x) :
    Sieve.ofArrows
        (fun j ↦ Scheme.Etale.mk (nativeRelativeBaseChangeSource C σ r hC (W j)).left)
        (fun j ↦ (etaleTerminalIsTerminal C.left).from
          (Scheme.Etale.mk (nativeRelativeBaseChangeSource C σ r hC (W j)).left)) ∈
      C.left.smallEtaleTopology (etaleTerminal C.left) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j, y, hy⟩ := hcover (σ x)
  have hx : x ∈ Set.range (pullback.fst σ (W j).hom) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hx
  apply Set.mem_iUnion.mpr
  refine ⟨j, z, ?_⟩
  have hw := MorphismProperty.Over.w ((etaleTerminalIsTerminal C.left).from
    (Scheme.Etale.mk (nativeRelativeBaseChangeSource C σ r hC (W j)).left))
  have hleft : ((etaleTerminalIsTerminal C.left).from
      (Scheme.Etale.mk (nativeRelativeBaseChangeSource C σ r hC (W j)).left)).left =
      (nativeRelativeBaseChangeSource C σ r hC (W j)).left :=
    (Category.comp_id _).symm.trans hw
  exact (congrArg (fun q ↦ q z) hleft).trans hz

/-- Evaluate the accepted whole restriction identity at one section, before
introducing any indexed pullback charts or a covering family. -/
theorem nativeEtaleSectionEvaluation_restriction_apply {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y C : Over X} (R : Y ⟶ C) [Etale R.left]
    (s : (pullbackSectionsFunctor F).obj (op C)) :
    (nativeEtaleSectionEvaluationIso F R).hom ((pullbackSectionsFunctor F).map R.op s) =
      ((inverseImage C.hom).obj F).obj.map
        ((etaleTerminalIsTerminal C.left).from (Scheme.Etale.mk R.left)).op s :=
  (ConcreteCategory.comp_apply ((pullbackSectionsFunctor F).map R.op)
    (nativeEtaleSectionEvaluationIso F R).hom s).symm.trans
      (ConcreteCategory.congr_hom (nativeEtaleSectionEvaluation_restriction F R) s)

/-- Original sections are separated by the actual relative base-change cover.
This boundary involves only the source object and its cover, before any stage
object, stage section, or projection to that stage is introduced. -/
theorem native_baseChange_sections_ext {X S : Scheme.{u}} (C : Over X)
    (σ : C.left ⟶ S) (r : S ⟶ X) (hC : σ ≫ r = C.hom)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} (W : J → Over S)
    [∀ j, Etale (W j).hom]
    (hcover : ∀ x : S, ∃ j, ∃ y : (W j).left, (W j).hom y = x)
    (s t : (pullbackSectionsFunctor F).obj (op C))
    (h : ∀ j, (pullbackSectionsFunctor F).map
        (nativeRelativeBaseChangeSource C σ r hC (W j)).op s =
      (pullbackSectionsFunctor F).map
        (nativeRelativeBaseChangeSource C σ r hC (W j)).op t) : s = t := by
  have htype : Presieve.IsSheaf C.left.smallEtaleTopology
      (((inverseImage C.hom).obj F).obj ⋙ CategoryTheory.forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose C.left.smallEtaleTopology (CategoryTheory.forget Ab.{u + 1})).obj
        ((inverseImage C.hom).obj F)).property
  apply (htype.isSheafFor
    (Presieve.ofArrows
      (fun j ↦ Scheme.Etale.mk (nativeRelativeBaseChangeSource C σ r hC (W j)).left)
      (fun j ↦ (etaleTerminalIsTerminal C.left).from
        (Scheme.Etale.mk (nativeRelativeBaseChangeSource C σ r hC (W j)).left)))
    (nativeRelativeBaseChangeSource_covering C σ r hC W hcover)).isSeparatedFor.ext
  rintro V f ⟨j⟩
  exact (nativeEtaleSectionEvaluation_restriction_apply F
    (nativeRelativeBaseChangeSource C σ r hC (W j)) s).symm.trans
      ((congrArg (nativeEtaleSectionEvaluationIso F
        (nativeRelativeBaseChangeSource C σ r hC (W j))).hom (h j)).trans
          (nativeEtaleSectionEvaluation_restriction_apply F
            (nativeRelativeBaseChangeSource C σ r hC (W j)) t))

/-- The original first projection of a native stage chart. -/
def nativeStageChartSource {X S : Scheme.{u}} (B : Over X)
    (τ : B.left ⟶ S) (W : Over S) [Etale W.hom] :
    Over.mk ((baseChangeEtaleChart τ W).hom ≫ B.hom) ⟶ B :=
  Over.homMk (baseChangeEtaleChart τ W).hom

/-- The actual pullback-chart transition, from a raw source chart to a native
stage chart, over the original coefficient base. -/
def nativeRelativeChartTransition {X S : Scheme.{u}} (B C : Over X)
    (Q : C ⟶ B) (τ : B.left ⟶ S) (σ : C.left ⟶ S) (hq : Q.left ≫ τ = σ)
    (r : S ⟶ X) (hC : σ ≫ r = C.hom) (W : Over S) [Etale W.hom] :
    relativeBaseChangeObject σ r W.hom ⟶
      Over.mk ((baseChangeEtaleChart τ W).hom ≫ B.hom) :=
  Over.homMk
    (pullback.lift (pullback.fst σ W.hom ≫ Q.left) (pullback.snd σ W.hom)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ pullback.fst σ W.hom ≫ z) hq).trans pullback.condition)))
    (by
      change (pullback.lift _ _ _) ≫ (pullback.fst τ W.hom ≫ B.hom) =
        pullback.snd σ W.hom ≫ W.hom ≫ r
      exact (pullback.lift_fst_assoc _ _ _ B.hom).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ pullback.fst σ W.hom ≫ z) (Over.w Q)).trans
            (Over.w (nativeRelativeBaseChangeSource C σ r hC W)))))

/-- The transition preserves the literal original projection arrows. -/
theorem nativeRelativeChartTransition_source {X S : Scheme.{u}} (B C : Over X)
    (Q : C ⟶ B) (τ : B.left ⟶ S) (σ : C.left ⟶ S) (hq : Q.left ≫ τ = σ)
    (r : S ⟶ X) (hC : σ ≫ r = C.hom) (W : Over S) [Etale W.hom] :
    nativeRelativeChartTransition B C Q τ σ hq r hC W ≫ nativeStageChartSource B τ W =
      nativeRelativeBaseChangeSource C σ r hC W ≫ Q := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- The transition preserves the original representative arrow, after the
local chart test was normalized before gluing. -/
theorem nativeRelativeChartTransition_representative {X S : Scheme.{u}}
    (B C : Over X) (Q : C ⟶ B)
    (τ : B.left ⟶ S) (σ : C.left ⟶ S) (hq : Q.left ≫ τ = σ)
    (r : S ⟶ X) (hB : τ ≫ r = B.hom) (hC : σ ≫ r = C.hom)
    (W : Over S) [Etale W.hom] (U : X.Etale)
    (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r) :
    nativeRelativeChartTransition B C Q τ σ hq r hC W ≫
        unitRepresentativeArrow B.hom (nativeBaseChangeChartTest B τ r hB W U a ha) =
      relativeBaseChangeRepresentative σ r W.hom U a ha := by
  have ht := unitRepresentativeArrow_relativeChartTest B.hom (baseChangeEtaleChart τ W)
    U (pullback.snd τ W.hom ≫ a)
    ((baseChangeChart_triangle τ r W U a ha).trans
      (congrArg (fun z ↦ (baseChangeEtaleChart τ W).hom ≫ z) hB))
  refine (congrArg (fun z ↦ nativeRelativeChartTransition B C Q τ σ hq r hC W ≫ z)
    ht).trans ?_
  apply Over.OverMorphism.ext
  exact pullback.lift_snd_assoc _ _ _ _

/-- The original projection has the prescribed image on one actual chart.
This is proved before introducing a family of charts or cover separation. -/
theorem native_baseChange_chart_image_equation {X S : Scheme.{u}}
    (B C : Over X) (Q : C ⟶ B)
    (τ : B.left ⟶ S) (σ : C.left ⟶ S) (hq : Q.left ≫ τ = σ)
    (r : S ⟶ X) (hB : τ ≫ r = B.hom) (hC : σ ≫ r = C.hom)
    (F : AbelianSheaf.{u, u + 1} X) (W : Over S) [Etale W.hom]
    (U : X.Etale) (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r)
    (t : F.obj.obj (op U)) (s : (pullbackSectionsFunctor F).obj (op C))
    (v : (pullbackSectionsFunctor F).obj (op B))
    (hv : (pullbackSectionsFunctor F).map
        (Over.homMk (baseChangeEtaleChart τ W).hom
          (U := Over.mk ((baseChangeEtaleChart τ W).hom ≫ B.hom)) (V := B)).op v =
      etaleRepresentativeSection F (Over.mk ((baseChangeEtaleChart τ W).hom ≫ B.hom)) U
        (unitRepresentativeArrow B.hom (nativeBaseChangeChartTest B τ r hB W U a ha)) t)
    (hs : (pullbackSectionsFunctor F).map (nativeRelativeBaseChangeSource C σ r hC W).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject σ r W.hom) U
        (relativeBaseChangeRepresentative σ r W.hom U a ha) t) :
    (pullbackSectionsFunctor F).map (nativeRelativeBaseChangeSource C σ r hC W).op
        ((pullbackSectionsFunctor F).map Q.op v) =
      (pullbackSectionsFunctor F).map (nativeRelativeBaseChangeSource C σ r hC W).op s := by
  exact native_local_image_of_representatives F U
    (nativeRelativeChartTransition B C Q τ σ hq r hC W)
    (Over.homMk (baseChangeEtaleChart τ W).hom
      (U := Over.mk ((baseChangeEtaleChart τ W).hom ≫ B.hom)) (V := B))
    (nativeRelativeBaseChangeSource C σ r hC W) Q
    (unitRepresentativeArrow B.hom (nativeBaseChangeChartTest B τ r hB W U a ha))
    (relativeBaseChangeRepresentative σ r W.hom U a ha)
    (nativeRelativeChartTransition_source B C Q τ σ hq r hC W)
    (nativeRelativeChartTransition_representative B C Q τ σ hq r hB hC W U a ha)
    v s t hv hs

/-- Local representatives determine the image under the original relative
projection of a section glued in the original stage sheaf. -/
theorem native_baseChange_amalgamation_image {X S : Scheme.{u}}
    (B C : Over X) (Q : C ⟶ B)
    (τ : B.left ⟶ S) (σ : C.left ⟶ S) (hq : Q.left ≫ τ = σ)
    (r : S ⟶ X) (hB : τ ≫ r = B.hom) (hC : σ ≫ r = C.hom)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} (W : J → Over S)
    [∀ j, Etale (W j).hom]
    (hcover : ∀ x : S, ∃ j, ∃ y : (W j).left, (W j).hom y = x)
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (s : (pullbackSectionsFunctor F).obj (op C))
    (v : (pullbackSectionsFunctor F).obj (op B))
    (hv : IsNativeUnitAmalgamation B F (fun j ↦ baseChangeEtaleChart τ (W j)) U
      (fun j ↦ nativeBaseChangeChartTest B τ r hB (W j) (U j) (a j) (ha j)) t v)
    (hs : ∀ j, (pullbackSectionsFunctor F).map
        (nativeRelativeBaseChangeSource C σ r hC (W j)).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject σ r (W j).hom) (U j)
        (relativeBaseChangeRepresentative σ r (W j).hom (U j) (a j) (ha j)) (t j)) :
    (pullbackSectionsFunctor F).map Q.op v = s := by
  apply native_baseChange_sections_ext C σ r hC F W hcover
  intro j
  exact native_baseChange_chart_image_equation B C Q τ σ hq r hB hC F
    (W j) (U j) (a j) (ha j) (t j) s v (hv j) (hs j)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
