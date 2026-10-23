/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RelativeSectionsSeparation
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RelativeChartTransition
/-! # Original limit image of the stage amalgamation -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private theorem functor_square_values {C : Type*} [Category* C]
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

private theorem native_section_image_transport {X : Scheme.{u}}
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
  exact functor_square_values (pullbackSectionsFunctor F) A L R Q hA v s
    (etaleRepresentativeSection F Z U a t) (etaleRepresentativeSection F Y U b t)
    hv hs hxy

private theorem actual_chart_image_equation {S T L X : Scheme.{u}}
    (τ : T ⟶ S) (σ : L ⟶ S) (q : L ⟶ T) (hq : q ≫ τ = σ)
    (r : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (W : Over S) (U : X.Etale) (a : W.left ⟶ U.left)
    (ha : a ≫ U.hom = W.hom ≫ r) (t : F.obj.obj (op U))
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk (σ ≫ r))))
    (v : (pullbackSectionsFunctor F).obj (op (Over.mk (τ ≫ r))))
    (hs : (pullbackSectionsFunctor F).map (relativeBaseChangeSource σ r W.hom).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject σ r W.hom) U
        (relativeBaseChangeRepresentative σ r W.hom U a ha) t)
    (hv : (pullbackSectionsFunctor F).map (relativeBaseChangeSource τ r W.hom).op v =
      etaleRepresentativeSection F (relativeBaseChangeObject τ r W.hom) U
        (relativeBaseChangeRepresentative τ r W.hom U a ha) t) :
    (pullbackSectionsFunctor F).map (relativeBaseChangeSource σ r W.hom).op
      ((pullbackSectionsFunctor F).map
        (Over.homMk q ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ r) hq))
          (U := Over.mk (σ ≫ r)) (V := Over.mk (τ ≫ r))).op v) =
      (pullbackSectionsFunctor F).map (relativeBaseChangeSource σ r W.hom).op s := by
  exact native_section_image_transport F U (relativeChartTransition τ σ q hq r W)
    (relativeBaseChangeSource τ r W.hom) (relativeBaseChangeSource σ r W.hom)
    (Over.homMk q ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ r) hq))
      (U := Over.mk (σ ≫ r)) (V := Over.mk (τ ≫ r)))
    (relativeBaseChangeRepresentative τ r W.hom U a ha)
    (relativeBaseChangeRepresentative σ r W.hom U a ha)
    (relativeChartTransition_source τ σ q hq r W)
    (relativeChartTransition_representative τ σ q hq r W U a ha) v s t hv hs

/-- The descended local equations force the original limit image of the
amalgamated section to be the initial section. -/
theorem baseChange_amalgamation_image {S T L X : Scheme.{u}}
    (τ : T ⟶ S) (σ : L ⟶ S) (q : L ⟶ T) (hq : q ≫ τ = σ)
    (r : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → Over S) [∀ j, Etale (W j).hom]
    (hcover : ∀ x : S, ∃ j, ∃ y : (W j).left, (W j).hom y = x)
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk (σ ≫ r))))
    (v : (pullbackSectionsFunctor F).obj (op (Over.mk (τ ≫ r))))
    (hs : ∀ j, (pullbackSectionsFunctor F).map
        (relativeBaseChangeSource σ r (W j).hom).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject σ r (W j).hom) (U j)
        (relativeBaseChangeRepresentative σ r (W j).hom (U j) (a j) (ha j)) (t j))
    (hv : ∀ j, (pullbackSectionsFunctor F).map
        (relativeBaseChangeSource τ r (W j).hom).op v =
      etaleRepresentativeSection F (relativeBaseChangeObject τ r (W j).hom) (U j)
        (relativeBaseChangeRepresentative τ r (W j).hom (U j) (a j) (ha j)) (t j)) :
    (pullbackSectionsFunctor F).map
      (Over.homMk q ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z ↦ z ≫ r) hq))
        (U := Over.mk (σ ≫ r)) (V := Over.mk (τ ≫ r))).op v = s := by
  apply relativeBaseChange_sections_ext σ r F W hcover
  intro j
  exact actual_chart_image_equation τ σ q hq r F (W j) (U j) (a j) (ha j) (t j)
    s v (hs j) (hv j)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
