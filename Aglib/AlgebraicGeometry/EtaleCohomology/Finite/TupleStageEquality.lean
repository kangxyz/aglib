/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.TupleStageLift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.RelativeFactorization

/-! # Equality of original finite component germs descends to a stage -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

variable (A B : Type u) [CommRing A] [CommRing B]
  [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
  [Algebra B A] [Module.Finite B A] {X : Scheme.{u}}
  {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ X.Etale) (c : Cone (D ⋙ Scheme.Etale.forget X))
  (e : Spec (.of A) ≅ c.pt.left)

/-- Equality of all original component germs gives an actual refinement on
which the prescribed original sections agree, not merely a new representative. -/
theorem exists_stage_refinement_of_component_germ_eq
    (hc : IsLimit ((Over.forget X).mapCone c))
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (F : AbelianSheaf.{u, u + 1} X) (i : I)
    (a b : F.obj.obj (op (D.obj i)))
    (hab : ∀ m, (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber
      (D.obj i) (finiteLimitStagePoint A B D c e i m) F.obj a =
      (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber
        (D.obj i) (finiteLimitStagePoint A B D c e i m) F.obj b) :
    ∃ (k : I) (d : k ⟶ i), F.obj.map (D.map d).op a = F.obj.map (D.map d).op b := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  choose U f t ht heq using fun m =>
    ((finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber_eq_iff'
      (D.obj i) (finiteLimitStagePoint A B D c e i m) a b).mp (hab m)
  have hf (m : MaximalSpectrum A) : Etale (f m).left := inferInstance
  let V (m : MaximalSpectrum A) : (D.obj i).left.Etale := Scheme.Etale.mk (f m).left
  have ht' (m : MaximalSpectrum A) : (t m).left ≫ (V m).hom =
      localComponentResidueMap A m ≫
        (localComponentInclusion A m ≫ (e.hom ≫ (c.π.app i).left)) := by
    exact (congrArg (fun k :
      Over.mk (finiteSourceResiduePoint A m ≫ (e.hom ≫ c.pt.hom)) ⟶
        Over.mk (D.obj i).hom => k.left) (ht m)).trans
      (Category.assoc (localComponentResidueMap A m) (localComponentInclusion A m)
        (e.hom ≫ (c.π.app i).left))
  obtain ⟨s, hs, _⟩ := exists_finite_pointed_neighborhood_lift A B
    (e.hom ≫ (c.π.app i).left) V (fun m => (t m).left) ht'
  let θ : coproductEtale U ⟶ D.obj i :=
    MorphismProperty.Over.homMk (Sigma.desc (fun m => (f m).left)) (by
      apply Sigma.hom_ext
      intro m
      exact (Category.assoc (Sigma.ι (fun m => (U m).left) m)
        (Sigma.desc (fun m => (f m).left)) (D.obj i).hom).symm.trans
        ((congrArg (fun q : (U m).left ⟶ (D.obj i).left => q ≫ (D.obj i).hom)
          (Sigma.ι_comp_desc (fun m => (f m).left) m)).trans
          ((f m).w.trans (Sigma.ι_comp_desc (fun m => (U m).hom) m).symm)))
  have hsθ : s ≫ θ.left = e.hom ≫ (c.π.app i).left := hs
  have hsX : s ≫ (coproductEtale U).hom = e.hom ≫ c.pt.hom := by
    exact (congrArg (fun q : (coproductEtale U).left ⟶ X => s ≫ q) θ.w.symm).trans
      ((Category.assoc s θ.left (D.obj i).hom).symm.trans
        ((congrArg (fun q : Spec (.of A) ⟶ (D.obj i).left => q ≫ (D.obj i).hom)
          hsθ).trans
          ((Category.assoc e.hom (c.π.app i).left (D.obj i).hom).trans
            (congrArg (fun q : c.pt.left ⟶ X => e.hom ≫ q) (c.π.app i).w))))
  let s' : c.pt ⟶ Over.mk (coproductEtale U).hom := Over.homMk (e.inv ≫ s) (by
    exact (Category.assoc e.inv s (coproductEtale U).hom).trans
      ((congrArg (fun q : Spec (.of A) ⟶ X => e.inv ≫ q) hsX).trans
        (e.inv_hom_id_assoc c.pt.hom)))
  have htriangle : s' ≫ (Scheme.Etale.forget X).map θ = c.π.app i ≫ 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact (Category.assoc e.inv s θ.left).trans
      ((congrArg (fun q => e.inv ≫ q) hsθ).trans
        ((e.inv_hom_id_assoc (c.π.app i).left).trans (Category.comp_id _).symm))
  have hcompact (j : I) : CompactSpace ((D ⋙ Scheme.Etale.forget X).obj j).left :=
    inferInstanceAs (CompactSpace (D.obj j).left)
  have hqs (j : I) : QuasiSeparatedSpace ((D ⋙ Scheme.Etale.forget X).obj j).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j).left)
  have haffine {j k : I} (v : j ⟶ k) :
      IsAffineHom ((D ⋙ Scheme.Etale.forget X).map v).left :=
    inferInstanceAs (IsAffineHom (D.map v).left)
  have : Etale (coproductEtale U).hom := (coproductEtale U).prop
  have : LocallyOfFinitePresentation (coproductEtale U).hom := inferInstance
  have : LocallyOfFinitePresentation ((Scheme.Etale.forget X).obj
      (coproductEtale U)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (coproductEtale U).hom)
  have : Etale (D.obj i).hom := (D.obj i).prop
  have : LocallyOfFinitePresentation ((D ⋙ Scheme.Etale.forget X).obj i).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (D.obj i).hom)
  obtain ⟨k, d, r, hfac, _⟩ := Continuity.exists_relative_factorization
    (D ⋙ Scheme.Etale.forget X) c hc i (𝟙 _) ((Scheme.Etale.forget X).map θ) s' htriangle
  let r' : D.obj k ⟶ coproductEtale U := MorphismProperty.Over.homMk r.left r.w
  have hfac' : r' ≫ θ = D.map d := by
    apply MorphismProperty.Over.Hom.ext
    exact (congrArg (fun q : (D ⋙ Scheme.Etale.forget X).obj k ⟶
      (D ⋙ Scheme.Etale.forget X).obj i => q.left) hfac).trans (Category.comp_id _)
  have heq' : F.obj.map θ.op a = F.obj.map θ.op b := by
    apply Concrete.isLimit_ext _ (coproductSectionsFanIsLimit U F)
    intro ⟨m⟩
    change F.obj.map (coproductEtaleInclusion U m).op (F.obj.map θ.op a) =
      F.obj.map (coproductEtaleInclusion U m).op (F.obj.map θ.op b)
    have hι : coproductEtaleInclusion U m ≫ θ = f m := by
      apply MorphismProperty.Over.Hom.ext
      exact Sigma.ι_comp_desc _ m
    simpa only [← Functor.map_comp_apply, ← op_comp, hι] using heq m
  refine ⟨k, d, ?_⟩
  have hh := congrArg (fun z => F.obj.map r'.op z) heq'
  simpa only [← Functor.map_comp_apply, ← op_comp, hfac'] using hh

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
