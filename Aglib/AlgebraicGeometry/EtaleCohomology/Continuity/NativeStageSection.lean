/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.NativeStageImage

/-! # An original stage section with its original projection image

Gluing, local source normalization, and the projection image are assembled at
independent relative objects. The resulting section belongs to the literal
original stage object before any inverse-system stage is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u v

open EtaleAffineBasis
attribute [local instance] hasSheafifyLarge

/-- Functoriality for a complete local source comparison, before coefficients
or representative values are specialized. -/
private theorem presheaf_triple_map_eq {C : Type*} [Category C]
    (P : Cᵒᵖ ⥤ Ab.{u + 1}) {Y A B V : C}
    (g : Y ⟶ A) (E : A ⟶ B) (e : B ⟶ V) (R : Y ⟶ V)
    (hR : g ≫ E ≫ e = R) :
    P.map e.op ≫ P.map E.op ≫ P.map g.op = P.map R.op := by
  calc
    P.map e.op ≫ P.map E.op ≫ P.map g.op = P.map (g ≫ E ≫ e).op := by
      simp only [op_comp, Functor.map_comp, Category.assoc]
    _ = P.map R.op := congrArg P.map (congrArg Quiver.Hom.op hR)

/-- Reassociate only the local source restriction before applying indexed
geometry. All objects and arrows are the actual original relative objects. -/
private theorem native_representative_equation_of_composite {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y A B C : Over X} (U : X.Etale)
    (g : Y ⟶ A) (E : A ⟶ B) (e : B ⟶ C) (R : Y ⟶ C)
    (hR : g ≫ E ≫ e = R) (a : Y ⟶ (Etale.forget X).obj U)
    (s : (pullbackSectionsFunctor F).obj (op C)) (t : F.obj.obj (op U))
    (h : (pullbackSectionsFunctor F).map g.op
        ((pullbackSectionsFunctor F).map E.op ((pullbackSectionsFunctor F).map e.op s)) =
      etaleRepresentativeSection F Y U a t) :
    (pullbackSectionsFunctor F).map R.op s = etaleRepresentativeSection F Y U a t := by
  exact (ConcreteCategory.congr_hom
    (presheaf_triple_map_eq (pullbackSectionsFunctor F) g E e R hR) s).symm.trans h

/-- The two source normalizations preserve the original pullback projection. -/
private theorem native_source_comparison_triangle {X S : Scheme.{u}} (C : Over X)
    (σ : C.left ⟶ S) (r : S ⟶ X) (hC : σ ≫ r = C.hom)
    (f : C.left ⟶ X) (hf : σ ≫ r = f) (e : Over.mk f ≅ C)
    (he : e.hom.left = 𝟙 C.left) (W : Over S) :
    EtaleAffineBasis.relativeBaseChangeSource σ r W.hom ≫
        EtaleAffineBasis.relativeSourceEquality hf ≫ e.hom =
      nativeRelativeBaseChangeSource C σ r hC W := by
  apply Over.OverMorphism.ext
  change pullback.fst σ W.hom ≫ 𝟙 C.left ≫ e.hom.left = pullback.fst σ W.hom
  exact (congrArg (fun z ↦ pullback.fst σ W.hom ≫ 𝟙 C.left ≫ z) he).trans
    ((congrArg (fun z ↦ pullback.fst σ W.hom ≫ z) (Category.id_comp (𝟙 C.left))).trans
      (Category.comp_id _))

/-- Normalize one named representative equation at the original source object
before any diagram, chosen representative data, or common stage is substituted. -/
private theorem native_source_representative_equation {X S : Scheme.{u}} (C : Over X)
    (σ : C.left ⟶ S) (r : S ⟶ X) (hC : σ ≫ r = C.hom)
    (f : C.left ⟶ X) (hf : σ ≫ r = f) (e : Over.mk f ≅ C)
    (he : e.hom.left = 𝟙 C.left) (F : AbelianSheaf.{u, u + 1} X)
    (W : Over S) (U : X.Etale) (a : W.left ⟶ U.left)
    (ha : a ≫ U.hom = W.hom ≫ r)
    (s : (pullbackSectionsFunctor F).obj (op C)) (t : F.obj.obj (op U))
    (h : IsBaseChangeSectionRepresentative σ r f hf F W U a ha
      ((pullbackSectionsFunctor F).map e.hom.op s) t) :
    (pullbackSectionsFunctor F).map (nativeRelativeBaseChangeSource C σ r hC W).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject σ r W.hom) U
        (relativeBaseChangeRepresentative σ r W.hom U a ha) t := by
  exact native_representative_equation_of_composite F U
    (relativeBaseChangeSource σ r W.hom) (relativeSourceEquality hf) e.hom
    (nativeRelativeBaseChangeSource C σ r hC W)
    (native_source_comparison_triangle C σ r hC f hf e he W)
    (relativeBaseChangeRepresentative σ r W.hom U a ha) s t h.eq

/-- Actual matching representatives glue to a section of the original stage
object whose image under the original relative projection is the given section. -/
theorem exists_native_stage_section_with_image {X S : Scheme.{u}}
    (B C : Over X) (Q : C ⟶ B)
    (τ : B.left ⟶ S) (σ : C.left ⟶ S) (hq : Q.left ≫ τ = σ)
    (r : S ⟶ X) (hB : τ ≫ r = B.hom) (hC : σ ≫ r = C.hom)
    (f : C.left ⟶ X) (hf : σ ≫ r = f) (e : Over.mk f ≅ C)
    (he : e.hom.left = 𝟙 C.left) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → Over S) [∀ j, Etale (W j).hom]
    (hcover : ∀ x : S, ∃ j, ∃ y : (W j).left, (W j).hom y = x)
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (s : (pullbackSectionsFunctor F).obj (op C))
    (hmatch : BaseChangeOverlapMatching τ r F W U a ha t)
    (hrep : ∀ j, IsBaseChangeSectionRepresentative σ r f hf
      F (W j) (U j) (a j) (ha j) ((pullbackSectionsFunctor F).map e.hom.op s) (t j)) :
    ∃ v : (pullbackSectionsFunctor F).obj (op B),
      (pullbackSectionsFunctor F).map Q.op v = s := by
  obtain ⟨v, hv⟩ := exists_native_baseChange_unitSections_amalgamation B τ r hB F
    W hcover U a ha t hmatch
  exact ⟨v, native_baseChange_amalgamation_image B C Q τ σ hq r hB hC F W hcover U a ha t
    s v hv (fun j ↦ native_source_representative_equation C σ r hC f hf e he F
      (W j) (U j) (a j) (ha j) s (t j) (hrep j))⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
