/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackScalarTransport
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.BaseChangeRepresentativeSections
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.MappedAffineCoverModels
/-! # Original section representatives along descended cover refinements -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private theorem functor_square_representative_value {C : Type*} [Category* C]
    (P : Cᵒᵖ ⥤ Ab.{u + 1}) {B B' Y Z : C}
    (G : Y ⟶ B) (A : Z ⟶ Y) (G' : Z ⟶ B') (E : B' ⟶ B)
    (hG : G' ≫ E = A ≫ G) (s : P.obj (op B))
    (x : P.obj (op Y)) (y : P.obj (op Z))
    (h : P.map G.op s = x) (hx : P.map A.op x = y) :
    P.map G'.op (P.map E.op s) = y := by
  have h₁ := ConcreteCategory.congr_hom (P.map_comp E.op G'.op) s
  have h₂ := ConcreteCategory.congr_hom (P.map_comp G.op A.op) s
  have hm := congrArg P.map (congrArg Quiver.Hom.op hG)
  exact h₁.symm.trans ((ConcreteCategory.congr_hom hm s).trans
    (h₂.trans ((congrArg (P.map A.op) h).trans hx)))

private theorem native_section_square {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {B B' Y Z : Over X} (U : X.Etale)
    (G : Y ⟶ B) (A : Z ⟶ Y) (G' : Z ⟶ B') (E : B' ⟶ B)
    (a : Y ⟶ (Etale.forget X).obj U) (a' : Z ⟶ (Etale.forget X).obj U)
    (hG : G' ≫ E = A ≫ G) (ha : A ≫ a = a')
    (s : (pullbackSectionsFunctor F).obj (op B)) (t : F.obj.obj (op U))
    (h : pullbackSectionsMap F G s = etaleRepresentativeSection F Y U a t) :
    (pullbackSectionsFunctor F).map G'.op ((pullbackSectionsFunctor F).map E.op s) =
      etaleRepresentativeSection F Z U a' t := by
  have h' := (ConcreteCategory.congr_hom (pullbackSectionsFunctor_map F G) s).trans h
  have hx : (pullbackSectionsFunctor F).map A.op
      (etaleRepresentativeSection F Y U a t) = etaleRepresentativeSection F Z U a' t :=
    (etaleRepresentativeSection_restrict F A U a t).trans
      (congrArg (fun q : Z ⟶ (Etale.forget X).obj U ↦
        etaleRepresentativeSection F Z U q t) ha)
  exact functor_square_representative_value (pullbackSectionsFunctor F) G A G' E hG s
    (etaleRepresentativeSection F Y U a t) (etaleRepresentativeSection F Z U a' t) h' hx

/-- The native identity-underlying relative map for an actual structural equation. -/
def relativeSourceEquality {S X : Scheme.{u}} {f g : S ⟶ X} (h : g = f) :
    Over.mk g ⟶ Over.mk f :=
  Over.homMk (𝟙 S) ((Category.id_comp f).trans h.symm)

/-- The refinement map of a descended chart, viewed over the original coefficient base. -/
def mappedCoverRefinement {S T X : Scheme.{u}} (σ : S ⟶ T) (r : T ⟶ X)
    (f : S ⟶ X) (hf : σ ≫ r = f) (Y : Over S) (W : Over T)
    (d : pullback σ W.hom ⟶ Y.left)
    (hd : d ≫ Y.hom = pullback.fst σ W.hom) :
    relativeBaseChangeObject σ r W.hom ⟶ Over.mk (Y.hom ≫ f) :=
  Over.homMk d (by
    change d ≫ (Y.hom ≫ f) = pullback.snd σ W.hom ≫ W.hom ≫ r
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ f) hd).trans
        ((congrArg (fun z ↦ pullback.fst σ W.hom ≫ z) hf.symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z ↦ z ≫ r) pullback.condition).trans
              (Category.assoc _ _ _))))))

/-- Original finite representative equations pull along the actual descended
cover refinements to the literal source equations needed for stage gluing. -/
theorem mappedCover_section_representatives {S T X : Scheme.{u}}
    (σ : S ⟶ T) (r : T ⟶ X) (f : S ⟶ X) (hf : σ ≫ r = f)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v}
    (Y : J → Over S) (W : J → Over T) (U : J → X.Etale)
    (a : ∀ j, Over.mk ((Y j).hom ≫ f) ⟶ (Etale.forget X).obj (U j))
    (b : ∀ j, (W j).left ⟶ (U j).left)
    (hb : ∀ j, b j ≫ (U j).hom = (W j).hom ≫ r)
    (d : ∀ j, pullback σ (W j).hom ⟶ (Y j).left)
    (hd : ∀ j, d j ≫ (Y j).hom = pullback.fst σ (W j).hom)
    (hda : ∀ j, d j ≫ (a j).left = pullback.snd σ (W j).hom ≫ b j)
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk f)))
    (t : ∀ j, F.obj.obj (op (U j)))
    (hs : ∀ j, pullbackSectionsMap F
      (Over.homMk (Y j).hom (U := Over.mk ((Y j).hom ≫ f)) (V := Over.mk f)) s =
      etaleRepresentativeSection F (Over.mk ((Y j).hom ≫ f)) (U j) (a j) (t j)) :
    ∀ j, (pullbackSectionsFunctor F).map (relativeBaseChangeSource σ r (W j).hom).op
        ((pullbackSectionsFunctor F).map (relativeSourceEquality hf).op s) =
      etaleRepresentativeSection F (relativeBaseChangeObject σ r (W j).hom) (U j)
        (relativeBaseChangeRepresentative σ r (W j).hom (U j) (b j) (hb j)) (t j) := by
  intro j
  apply native_section_square F (U j)
    (Over.homMk (Y j).hom (U := Over.mk ((Y j).hom ≫ f)) (V := Over.mk f))
    (mappedCoverRefinement σ r f hf (Y j) (W j) (d j) (hd j))
    (relativeBaseChangeSource σ r (W j).hom) (relativeSourceEquality hf)
    (a j) (relativeBaseChangeRepresentative σ r (W j).hom (U j) (b j) (hb j))
  · apply Over.OverMorphism.ext
    exact (Category.comp_id _).trans (hd j).symm
  · apply Over.OverMorphism.ext
    exact hda j
  · exact hs j
end AlgebraicGeometry.Scheme.EtaleAffineBasis
