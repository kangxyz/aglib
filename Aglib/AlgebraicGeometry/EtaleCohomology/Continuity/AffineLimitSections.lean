/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineSectionData
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.NativeStageMatching
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.NativeStageSource
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.StageSectionsInjectivity
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.SectionReindex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramNativeCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTailLimit
public import Aglib.CategoryTheory.Limits.Preserves.PresheafSections

/-! # Actual section cocones on affine inverse limits

The affine section descent and eventual-equality theorems prove that the
original relative section cocone is a filtered colimit. The original compatible
coefficient-system cocone follows by the existing native tail assembly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

open EtaleAffineBasis
attribute [local instance] hasSheafifyLarge

/-- Normalize only the structural arrow of the source of an actual relative map. -/
private def relativeMapSourceIso {C : Type*} [Category C] {X : C}
    {A B : Over X} (a : A ⟶ B) : Over.mk (a.left ≫ B.hom) ≅ A :=
  Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (Over.w a).symm)

/-- A filtered original presheaf cocone is colimiting when its legs are jointly
surjective and equality of two stage elements is witnessed by a later stage. -/
def isColimitPresheafMapConeOfSections
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Ab.{u + 1}) (D : I ⥤ C) (c : Cone D)
    (hsurj : ∀ s : P.obj (op c.pt),
      ∃ (i : I) (v : P.obj (op (D.obj i))), P.map (c.π.app i).op v = s)
    (hinj : ∀ (i : I) (s t : P.obj (op (D.obj i))),
      P.map (c.π.app i).op s = P.map (c.π.app i).op t →
      ∃ (k : I) (q : k ⟶ i), P.map (D.map q).op s = P.map (D.map q).op t) :
    IsColimit (P.mapCocone c.op) :=
  CategoryTheory.Limits.isColimitPresheafMapConeOfSections P D c hsurj hinj

section Relative

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {X : Scheme.{u}}
  (D : I ⥤ Over X) (c : Cone D)
  (hc : IsLimit ((Over.forget X).mapCone c))
  [∀ i, IsAffine (D.obj i).left] (F : AbelianSheaf.{u, u + 1} X)

include hc

/-- Normalize local chart data first, glue in the original stage sheaf, and
identify the original cone image before constructing the stage existential. -/
private theorem affinePullbackSections_image_of_data (i : I)
    (e : Over.mk (Y := ((Over.forget X).mapCone c).pt)
      (((Over.forget X).mapCone c).π.app i ≫ (D.obj i).hom) ≅ c.pt)
    (he : e.hom.left = 𝟙 c.pt.left)
    (s : (pullbackSectionsFunctor F).obj (op c.pt))
    (A : EtaleAffineBasis.AffineSectionData (D ⋙ Over.forget X)
      ((Over.forget X).mapCone c) i (D.obj i).hom F
      ((pullbackSectionsFunctor F).map e.hom.op s)) :
    ∃ (j : I) (v : (pullbackSectionsFunctor F).obj (op (D.obj j))),
      (pullbackSectionsFunctor F).map (c.π.app j).op v = s := by
  rcases A with ⟨stage, q, J, hJ, W, hW, hEtale, hcover, U, a, t, ha, hrep⟩
  have hD : ∀ j, IsAffine ((D ⋙ Over.forget X).obj j) :=
    fun j ↦ inferInstanceAs (IsAffine (D.obj j).left)
  have (j : J) : Etale (W j).hom := hEtale j
  let r : (D ⋙ Over.forget X).obj stage ⟶ X :=
    (D ⋙ Over.forget X).map q ≫ (D.obj i).hom
  have hr : r = (D.obj stage).hom := Over.w (D.map q)
  have hf : ((Over.forget X).mapCone c).π.app stage ≫ r =
      ((Over.forget X).mapCone c).π.app i ≫ (D.obj i).hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ (D.obj i).hom) (((Over.forget X).mapCone c).w q))
  obtain ⟨k, hk⟩ := @exists_stage_overlap_matching_of_representative_equations.{u, u}
    I inferInstance inferInstance (D ⋙ Over.forget X) ((Over.forget X).mapCone c)
    hc hD stage X r F J hJ W hW
    U a ha t
    (((Over.forget X).mapCone c).π.app i ≫ (D.obj i).hom) hf
    ((pullbackSectionsFunctor F).map e.hom.op s) hrep
  have hB : (D ⋙ Over.forget X).map k.hom ≫ r = (D.obj k.left).hom :=
    (congrArg (fun z ↦ (D.map k.hom).left ≫ z) hr).trans (Over.w (D.map k.hom))
  have hq : (e.hom ≫ c.π.app k.left).left ≫ (D ⋙ Over.forget X).map k.hom =
      ((Over.forget X).mapCone c).π.app stage := by
    change (e.hom.left ≫ (c.π.app k.left).left) ≫ (D ⋙ Over.forget X).map k.hom = _
    exact (congrArg
      (fun z : c.pt.left ⟶ c.pt.left ↦
        (z ≫ (c.π.app k.left).left) ≫ (D ⋙ Over.forget X).map k.hom) he).trans
      ((congrArg
        (fun z : c.pt.left ⟶ (D.obj k.left).left ↦
          z ≫ (D ⋙ Over.forget X).map k.hom)
        (Category.id_comp (c.π.app k.left).left)).trans
          (((Over.forget X).mapCone c).w k.hom))
  obtain ⟨v, hv⟩ := exists_native_stage_section_of_source_iso
    (S := (D ⋙ Over.forget X).obj stage) (L := ((Over.forget X).mapCone c).pt)
    (D.obj k.left) c.pt (c.π.app k.left)
    (((Over.forget X).mapCone c).π.app i ≫ (D.obj i).hom) e
    ((D ⋙ Over.forget X).map k.hom) (((Over.forget X).mapCone c).π.app stage) hq
    r hB hf F W hcover U a ha t s hk hrep
  exact ⟨k.left, v, hv⟩

/-- Genuine finite representatives and their actual later-stage image supply
an original cocone image, without normalizing a composite stage arrow. -/
theorem affinePullbackSections_jointly_surjective
    (s : (pullbackSectionsFunctor F).obj (op c.pt)) :
    ∃ (i : I) (v : (pullbackSectionsFunctor F).obj (op (D.obj i))),
      (pullbackSectionsFunctor F).map (c.π.app i).op v = s := by
  classical
  have (j : I) : IsAffine ((D ⋙ Over.forget X).obj j) :=
    inferInstanceAs (IsAffine (D.obj j).left)
  have : Nonempty I := IsCofiltered.nonempty
  let i : I := Classical.arbitrary I
  let e : Over.mk (Y := ((Over.forget X).mapCone c).pt)
      (((Over.forget X).mapCone c).π.app i ≫ (D.obj i).hom) ≅ c.pt :=
    relativeMapSourceIso (c.π.app i)
  exact affinePullbackSections_image_of_data D c hc F i e rfl s
    (EtaleAffineBasis.affineSectionData (D ⋙ Over.forget X)
      ((Over.forget X).mapCone c) hc i (D.obj i).hom F
      ((pullbackSectionsFunctor F).map e.hom.op s))

/-- Equality of original limit images of two affine-stage sections is witnessed
by an actual later stage transition. -/
theorem affinePullbackSections_eventually_equal (i : I)
    (s t : (pullbackSectionsFunctor F).obj (op (D.obj i)))
    (h : (pullbackSectionsFunctor F).map (c.π.app i).op s =
      (pullbackSectionsFunctor F).map (c.π.app i).op t) :
    ∃ (k : I) (q : k ⟶ i),
      (pullbackSectionsFunctor F).map (D.map q).op s =
        (pullbackSectionsFunctor F).map (D.map q).op t := by
  let P := pullbackSectionsFunctor F
  let D₀ : I ⥤ Scheme.{u} := D ⋙ Over.forget X
  let c₀ : Cone D₀ := (Over.forget X).mapCone c
  have (i : I) : IsAffine (D₀.obj i) := inferInstanceAs (IsAffine (D.obj i).left)
  let e : Over.mk (Y := c.pt.left) ((c.π.app i).left ≫ (D.obj i).hom) ≅ c.pt :=
    relativeMapSourceIso (c.π.app i)
  let a : Over.mk (Y := c.pt.left) ((c.π.app i).left ≫ (D.obj i).hom) ⟶ D.obj i :=
    Over.homMk (c.π.app i).left
  have ha : e.hom ≫ c.π.app i = a := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  have h' : P.map a.op s = P.map a.op t :=
    presheaf_eq_of_triangle P e.hom (c.π.app i) a ha s t h
  obtain ⟨k, hk⟩ := EtaleAffineBasis.exists_stage_sections_eventually_equal
    D₀ c₀ hc i (D.obj i).hom F s t h'
  let d : Over.mk (Y := (D.obj k.left).left)
      ((D.map k.hom).left ≫ (D.obj i).hom) ≅ D.obj k.left :=
    relativeMapSourceIso (D.map k.hom)
  let b : Over.mk (Y := (D.obj k.left).left)
      ((D.map k.hom).left ≫ (D.obj i).hom) ⟶ D.obj i :=
    Over.homMk (D.map k.hom).left
  have hb : d.inv ≫ b = D.map k.hom := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  refine ⟨k.left, k.hom, ?_⟩
  exact presheaf_eq_of_triangle P d.inv b (D.map k.hom) hb s t hk

/-- Genuine affine section descent and eventual equality make the original
relative section cocone a colimit, without an assumed continuity certificate. -/
def affinePullbackSectionsCoconeIsColimit :
    IsColimit (pullbackSectionsCocone D c F) :=
  isColimitPresheafMapConeOfSections (pullbackSectionsFunctor F) D c
    (affinePullbackSections_jointly_surjective D c hc F)
    (affinePullbackSections_eventually_equal D c hc F)

end Relative

section Compatible

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [∀ i, IsAffine (X.obj i).unop] (F : DiagramCoefficientSystem X)

/-- Actual affine fixed-coefficient tail continuity gives the original section
cocone for every compatible coefficient system. -/
def isColimitCompatibleSectionsOfAffineStages :
    IsColimit (compatibleSectionsCocone X F c) := by
  have (i : Iᵒᵖ) : IsAffine (X.leftOp.obj i) :=
    inferInstanceAs (IsAffine (X.obj i.unop).unop)
  have : IsAffine c.pt.unop :=
    Scheme.isAffine_of_isLimit (coneLeftOpOfCocone c)
      (isLimitConeLeftOpOfCocone X hc)
  have : CompactSpace c.pt.unop := inferInstance
  have : QuasiSeparatedSpace c.pt.unop := inferInstance
  apply isColimitCompatibleSectionsOfNativeTails X F c
  intro i
  let D := (relativeSchemeTail X i).leftOp
  have (j : (Under i)ᵒᵖ) : IsAffine (D.obj j).left :=
    inferInstanceAs (IsAffine (X.obj j.unop.right).unop)
  exact affinePullbackSectionsCoconeIsColimit D (relativeSchemeTailCone X c i)
    (isLimitRelativeSchemeTailUnderlying X c hc i) (F.obj i)

end Compatible

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
