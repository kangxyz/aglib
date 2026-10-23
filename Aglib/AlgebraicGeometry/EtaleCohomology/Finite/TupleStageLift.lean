/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.FiniteNeighborhoodLift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimitSections

/-! # Original finite component tuples descend to actual étale stages -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

variable (A B : Type u) [CommRing A] [CommRing B]
  [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
  [Algebra B A] [Module.Finite B A] {X : Scheme.{u}}

/-- The literal native residue-field map of a maximal-localization component. -/
def finiteSourceResiduePoint (m : MaximalSpectrum A) :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal))) ⟶ Spec (.of A) :=
  localComponentResidueMap A m ≫ localComponentInclusion A m

/-- Original ambient points supplied by the individual component residue fields. -/
def finiteSourceComponentPoint (q : Spec (.of A) ⟶ X) (m : MaximalSpectrum A) :
    X.smallEtaleTopology.Point := by
  let := HenselianLocalRing.henselian_localizationAtPrime B A m.asIdeal
  let := HenselianLocalRing.residueField_isSepClosed_localizationAtPrime B A m.asIdeal
  exact pointSmallEtale (finiteSourceResiduePoint A m ≫ q)

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ X.Etale) (c : Cone (D ⋙ Scheme.Etale.forget X))
  (e : Spec (.of A) ≅ c.pt.left)

/-- The actual original stage point induced by a component of the limiting source. -/
def finiteLimitStagePoint (i : I) (m : MaximalSpectrum A) :
    (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).fiber.obj (D.obj i) :=
  Over.homMk (finiteSourceResiduePoint A m ≫ e.hom ≫ (c.π.app i).left) (by
    change (finiteSourceResiduePoint A m ≫ e.hom ≫ (c.π.app i).left) ≫
      (D.obj i).hom = finiteSourceResiduePoint A m ≫ (e.hom ≫ c.pt.hom)
    exact (Category.assoc (finiteSourceResiduePoint A m)
      (e.hom ≫ (c.π.app i).left) (D.obj i).hom).trans
      (congrArg (fun k : Spec (.of A) ⟶ X => finiteSourceResiduePoint A m ≫ k)
        ((Category.assoc e.hom (c.π.app i).left (D.obj i).hom).trans
          (congrArg (fun k : c.pt.left ⟶ X => e.hom ≫ k) (c.π.app i).w))))

/-- A tuple of original component stalk elements is represented by one section
at one actual stage. The only continuity input is the represented-Hom theorem. -/
theorem exists_stage_section_of_component_germs
    (hc : IsLimit ((Over.forget X).mapCone c))
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (F : AbelianSheaf.{u, u + 1} X)
    (z : ∀ m, ((finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).presheafFiber.obj
      F.obj : AddCommGrpCat.{u + 1})) :
    ∃ (i : I) (a : F.obj.obj (op (D.obj i))),
      ∀ m, (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber
        (D.obj i) (finiteLimitStagePoint A B D c e i m) F.obj a = z m := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  choose U t a ha using fun m =>
    (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber_jointly_surjective (z m)
  have ht (m : MaximalSpectrum A) : (t m).left ≫ (U m).hom =
      LocalRing.residueSpecMap (Localization.AtPrime m.asIdeal) ≫
        (localComponentInclusion A m ≫ (e.hom ≫ c.pt.hom)) := by
    exact (t m).w.trans (Category.assoc
      (LocalRing.residueSpecMap (Localization.AtPrime m.asIdeal))
      (localComponentInclusion A m) (e.hom ≫ c.pt.hom))
  obtain ⟨s, hs, hres⟩ := exists_finite_pointed_neighborhood_lift A B
    (e.hom ≫ c.pt.hom) U (fun m => (t m).left) ht
  let s' : c.pt ⟶ Over.mk (coproductEtale U).hom := Over.homMk (e.inv ≫ s) (by
    exact (Category.assoc e.inv s (coproductEtale U).hom).trans
      ((congrArg (fun k : Spec (.of A) ⟶ X => e.inv ≫ k) hs).trans
        (e.inv_hom_id_assoc c.pt.hom)))
  have hcompact (j : I) : CompactSpace ((D ⋙ Scheme.Etale.forget X).obj j).left :=
    inferInstanceAs (CompactSpace (D.obj j).left)
  have hqs (j : I) : QuasiSeparatedSpace ((D ⋙ Scheme.Etale.forget X).obj j).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j).left)
  have haffine {j k : I} (v : j ⟶ k) :
      IsAffineHom ((D ⋙ Scheme.Etale.forget X).map v).left :=
    inferInstanceAs (IsAffineHom (D.map v).left)
  have : Etale (coproductEtale U).hom := (coproductEtale U).prop
  have : LocallyOfFinitePresentation (coproductEtale U).hom := inferInstance
  have : LocallyOfFinitePresentation (Over.mk (coproductEtale U).hom).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (coproductEtale U).hom)
  let hcol := Continuity.representedSectionsCoconeIsColimit
    (D ⋙ Scheme.Etale.forget X) c hc (Over.mk (coproductEtale U).hom)
  obtain ⟨i, r, hr⟩ := Types.jointly_surjective_of_isColimit hcol s'
  let r' : D.obj i.unop ⟶ coproductEtale U := MorphismProperty.Over.homMk r.left r.w
  obtain ⟨b, hb⟩ := exists_coproduct_section U F a
  refine ⟨i.unop, F.obj.map r'.op b, ?_⟩
  intro m
  have hp : (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).fiber.map r'
      (finiteLimitStagePoint A B D c e i.unop m) =
      (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).fiber.map
        (coproductEtaleInclusion U m) (t m) := by
    apply Over.OverMorphism.ext
    have hr' : (c.π.app i.unop).left ≫ r.left = e.inv ≫ s :=
      congrArg (fun k : c.pt ⟶ Over.mk (coproductEtale U).hom => k.left) hr
    change (finiteSourceResiduePoint A m ≫ e.hom ≫ (c.π.app i.unop).left) ≫
      r.left = (t m).left ≫ Sigma.ι (fun i => (U i).left) m
    have hj : (e.hom ≫ (c.π.app i.unop).left) ≫ r.left = s :=
      (Category.assoc e.hom (c.π.app i.unop).left r.left).trans
        ((congrArg (fun k : c.pt.left ⟶ (coproductEtale U).left => e.hom ≫ k) hr').trans
          (e.hom_inv_id_assoc s))
    exact (Category.assoc (finiteSourceResiduePoint A m)
      (e.hom ≫ (c.π.app i.unop).left) r.left).trans
      ((congrArg (fun k : Spec (.of A) ⟶ (coproductEtale U).left =>
        finiteSourceResiduePoint A m ≫ k) hj).trans (hres m))
  have h₁ := (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber_w
    r' (finiteLimitStagePoint A B D c e i.unop m) F.obj
  have h₂ := (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber_w
    (coproductEtaleInclusion U m) (t m) F.obj
  have hg := congrArg (fun v =>
    (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber
      (coproductEtale U) v F.obj) hp
  let η := finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m
  exact (ConcreteCategory.congr_hom h₁ b).trans
    ((congrArg (fun k => k b) hg).trans
      ((ConcreteCategory.congr_hom h₂ b).symm.trans
        ((congrArg (fun x => η.toPresheafFiber (U m) (t m) F.obj x)
          (hb m)).trans (ha m))))

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
