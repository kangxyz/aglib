/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.NativeStageSection

/-! # An independent source isomorphism for an original stage section

The local representative data retain their literal source scheme. Only the
source is compared by an actual relative isomorphism; the output section and
projection remain at the original relative stage object and original arrow.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u v

open EtaleAffineBasis
attribute [local instance] hasSheafifyLarge

private theorem section_image_cancel_source_iso {C : Type*} [Category C]
    (P : Cᵒᵖ ⥤ Ab.{u + 1}) {A B V : C} (e : A ≅ B) (q : B ⟶ V)
    (s : P.obj (op B)) (t : P.obj (op V))
    (h : P.map (e.hom ≫ q).op t = P.map e.hom.op s) : P.map q.op t = s := by
  have hm : P.map (e.hom ≫ q).op = P.map q.op ≫ P.map e.hom.op :=
    P.map_comp q.op e.hom.op
  apply (ConcreteCategory.bijective_of_isIso (P.map e.hom.op)).injective
  exact (ConcreteCategory.congr_hom hm t).symm.trans h

/-- Actual matching and representatives at an independent literal source give
an original stage section and its image under the original relative arrow. -/
theorem exists_native_stage_section_of_source_iso {X S L : Scheme.{u}}
    (B C : Over X) (Q : C ⟶ B) (f : L ⟶ X) (e : Over.mk f ≅ C)
    (τ : B.left ⟶ S) (σ : L ⟶ S) (hq : (e.hom ≫ Q).left ≫ τ = σ)
    (r : S ⟶ X) (hB : τ ≫ r = B.hom) (hf : σ ≫ r = f)
    (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → Over S) [∀ j, Etale (W j).hom]
    (hcover : ∀ x : S, ∃ j, ∃ y : (W j).left, (W j).hom y = x)
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (s : (pullbackSectionsFunctor F).obj (op C))
    (hmatch : BaseChangeOverlapMatching τ r F W U a ha t)
    (hrep : ∀ j, IsBaseChangeSectionRepresentative σ r f hf F (W j) (U j) (a j) (ha j)
      ((pullbackSectionsFunctor F).map e.hom.op s) (t j)) :
    ∃ v : (pullbackSectionsFunctor F).obj (op B),
      (pullbackSectionsFunctor F).map Q.op v = s := by
  have hid := ConcreteCategory.congr_hom
    ((pullbackSectionsFunctor F).map_id (op (Over.mk f)))
    ((pullbackSectionsFunctor F).map e.hom.op s)
  have hrep' (j : J) : IsBaseChangeSectionRepresentative σ r f hf F (W j) (U j)
      (a j) (ha j)
      ((pullbackSectionsFunctor F).map (Iso.refl (Over.mk f)).hom.op
        ((pullbackSectionsFunctor F).map e.hom.op s)) (t j) :=
    (congrArg (fun z : (pullbackSectionsFunctor F).obj (op (Over.mk f)) ↦
      IsBaseChangeSectionRepresentative σ r f hf F (W j) (U j) (a j) (ha j) z (t j))
      hid).mpr (hrep j)
  obtain ⟨v, hv⟩ := exists_native_stage_section_with_image B (Over.mk f) (e.hom ≫ Q)
    τ σ hq r hB hf f hf (Iso.refl _) rfl F W hcover U a ha t
    ((pullbackSectionsFunctor F).map e.hom.op s) hmatch hrep'
  exact ⟨v, section_image_cancel_source_iso (pullbackSectionsFunctor F) e Q s v hv⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
