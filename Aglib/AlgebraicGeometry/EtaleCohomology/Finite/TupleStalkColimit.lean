/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.TupleStageEquality

/-! # The actual finite-source stage colimit is its component stalk product -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

variable (A B : Type u) [CommRing A] [CommRing B]
  [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
  [Algebra B A] [Module.Finite B A] {X : Scheme.{u}}
  {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ X.Etale) (c : Cone (D ⋙ Scheme.Etale.forget X))
  (e : Spec (.of A) ≅ c.pt.left) (F : AbelianSheaf.{u, u + 1} X)

/-- The original section diagram, without replacing its coefficient sheaf. -/
abbrev finiteSourceSectionsDiagram : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1} := D.op ⋙ F.obj

/-- The concrete product of the original component stalk groups. -/
abbrev finiteSourceStalkTuple : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (∀ m : MaximalSpectrum A,
    ((finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).presheafFiber.obj
      F.obj : AddCommGrpCat.{u + 1}))

/-- Original stage germs, assembled componentwise. -/
def finiteSourceStageGerms (i : I) : F.obj.obj (op (D.obj i)) ⟶
    finiteSourceStalkTuple A B D c e F :=
  AddCommGrpCat.ofHom
    { toFun := fun a m =>
        (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber
          (D.obj i) (finiteLimitStagePoint A B D c e i m) F.obj a
      map_zero' := by ext m; exact map_zero _
      map_add' := by intro a b; ext m; exact map_add _ _ _ }

/-- The tuple cocone uses only the original component germs. -/
def finiteSourceStalkTupleCocone : Cocone (finiteSourceSectionsDiagram D F) where
  pt := finiteSourceStalkTuple A B D c e F
  ι :=
    { app := fun i => finiteSourceStageGerms A B D c e F i.unop
      naturality := by
        intro i j d
        apply ConcreteCategory.hom_ext
        intro a
        apply funext
        intro m
        let η := finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m
        have hp : η.fiber.map (D.map d.unop)
            (finiteLimitStagePoint A B D c e j.unop m) =
            finiteLimitStagePoint A B D c e i.unop m := by
          apply Over.OverMorphism.ext
          have hw := congrArg (fun r : c.pt ⟶
            (D ⋙ Scheme.Etale.forget X).obj i.unop => r.left) (c.w d.unop)
          change (finiteSourceResiduePoint A m ≫ e.hom ≫
            (c.π.app j.unop).left) ≫ (D.map d.unop).left =
              finiteSourceResiduePoint A m ≫ e.hom ≫ (c.π.app i.unop).left
          exact (Category.assoc (finiteSourceResiduePoint A m)
            (e.hom ≫ (c.π.app j.unop).left) (D.map d.unop).left).trans
            ((congrArg (fun r : Spec (.of A) ⟶ (D.obj i.unop).left =>
              finiteSourceResiduePoint A m ≫ r)
              (Category.assoc e.hom (c.π.app j.unop).left (D.map d.unop).left)).trans
              (congrArg (fun r : c.pt.left ⟶ (D.obj i.unop).left =>
                finiteSourceResiduePoint A m ≫ e.hom ≫ r) hw))
        have hw := ConcreteCategory.congr_hom
          (η.toPresheafFiber_w (D.map d.unop)
            (finiteLimitStagePoint A B D c e j.unop m) F.obj) a
        exact hw.trans (congrArg (fun t => η.toPresheafFiber (D.obj i.unop) t F.obj a) hp) }

/-- The canonical map from the original stage colimit to original stalk tuples. -/
def finiteSourceColimitToStalkTuple : colimit (finiteSourceSectionsDiagram D F) ⟶
    finiteSourceStalkTuple A B D c e F :=
  colimit.desc _ (finiteSourceStalkTupleCocone A B D c e F)

omit [IsCofiltered I] in
@[reassoc (attr := simp)]
lemma ι_finiteSourceColimitToStalkTuple (i : Iᵒᵖ) :
    colimit.ι (finiteSourceSectionsDiagram D F) i ≫
      finiteSourceColimitToStalkTuple A B D c e F =
        finiteSourceStageGerms A B D c e F i.unop :=
  colimit.ι_desc _ _

/-- The canonical tuple map is bijective, with both existence and equality
proved using actual finite-presentation descent. -/
theorem finiteSourceColimitToStalkTuple_bijective
    (hc : IsLimit ((Over.forget X).mapCone c))
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).left] :
    Function.Bijective (finiteSourceColimitToStalkTuple A B D c e F) := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  constructor
  · intro x y hxy
    obtain ⟨i, a, b, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1})
        (colimit.isColimit (finiteSourceSectionsDiagram D F))) x y
    have hg : finiteSourceStageGerms A B D c e F i.unop a =
        finiteSourceStageGerms A B D c e F i.unop b := by
      exact (ConcreteCategory.congr_hom
        (ι_finiteSourceColimitToStalkTuple A B D c e F i) a).symm.trans
        (hxy.trans (ConcreteCategory.congr_hom
          (ι_finiteSourceColimitToStalkTuple A B D c e F i) b))
    obtain ⟨k, d, hd⟩ := exists_stage_refinement_of_component_germ_eq A B D c e hc F
      i.unop a b (fun m => congrFun hg m)
    exact Concrete.colimit_rep_eq_of_exists (finiteSourceSectionsDiagram D F) a b
      ⟨op k, d.op, d.op, hd⟩
  · intro z
    obtain ⟨i, a, ha⟩ := exists_stage_section_of_component_germs A B D c e hc F z
    refine ⟨colimit.ι (finiteSourceSectionsDiagram D F) (op i) a, ?_⟩
    have h := ConcreteCategory.congr_hom
      (ι_finiteSourceColimitToStalkTuple A B D c e F (op i)) a
    exact h.trans (funext ha)

/-- This isomorphism has the literal original component germ coordinates. -/
def finiteSourceStalkTupleIso
    (hc : IsLimit ((Over.forget X).mapCone c))
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).left] :
    colimit (finiteSourceSectionsDiagram D F) ≅ finiteSourceStalkTuple A B D c e F := by
  let := (ConcreteCategory.isIso_iff_bijective
    (finiteSourceColimitToStalkTuple A B D c e F)).mpr
      (finiteSourceColimitToStalkTuple_bijective A B D c e F hc)
  exact asIso (finiteSourceColimitToStalkTuple A B D c e F)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
