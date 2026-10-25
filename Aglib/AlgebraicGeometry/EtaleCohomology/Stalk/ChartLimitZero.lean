/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartLimitContinuity
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Eventual vanishing of original classes on pointed etale neighborhoods

The existing original-cohomology limit cocone is used without replacing its
apex or its legs. Forgetting its filtered colimit to types detects equality
with zero at an actual later neighborhood.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u e uI vI
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

/-- Original transfer along a triangle carries the original restricted class
into the original restricted class, with no coefficient-model change. -/
theorem cohomologyTransfer_pullbackTriangle
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X) (a : Y ⟶ Z)
    (h : a ≫ g = f) (F : AbelianSheaf.{u, u + 1} X)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]
    (q : ℕ) (δ : Sheaf.H.{e} F q) :
    cohomologyTransfer a ((pullbackTriangleIso f g a h).inv.app F) q
        (cohomologyPullback g F q δ) = cohomologyPullback f F q δ := by
  subst f
  simp only [pullbackTriangleIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.comp_id]
  change Sheaf.H.map ((inverseImageComp g a).inv.app F) q
      (cohomologyPullback a ((inverseImage g).obj F) q
        (cohomologyPullback g F q δ)) = _
  rw [← cohomologyPullback_comp, ← Sheaf.H.map_comp_apply]
  simp only [Iso.hom_inv_id_app, Sheaf.H.map_id_apply]

section FixedSystem

variable {I : Type uI} [Category.{vI} I] [IsFiltered I] [IsConnected I]
  (Y : I ⥤ Scheme.{u}ᵒᵖ) (b : Cone Y) (c : Cocone Y) (l : b.pt ⟶ c.pt)
  (hl : ∀ i, b.π.app i ≫ c.ι.app i = l)
  (F : AbelianSheaf.{u, u + 1} b.pt.unop)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} b.pt.unop)]
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (Y.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [HasColimit (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F))]
  [PreservesColimitsOfShape I (CategoryTheory.forget AddCommGrpCat.{e})]

/-- An original class zero at the actual fixed-coefficient colimit is zero
at one genuine stage. The witness is a later stage of the original diagram. -/
theorem exists_pullback_eq_zero_of_colimit (q : ℕ)
    (hc : IsColimit (pullbackLimitCohomologyCocone Y b c l hl F q))
    (δ : Sheaf.H.{e} F q)
    (hδ : cohomologyPullback (X := b.pt.unop) (S := c.pt.unop) l.unop F q δ = 0) :
    ∃ i, cohomologyPullback (X := b.pt.unop) (S := (Y.obj i).unop)
      (b.π.app i).unop F q δ = 0 := by
  let i : I := Classical.choice (inferInstance : Nonempty I)
  let x := cohomologyPullback (X := b.pt.unop) (S := (Y.obj i).unop)
      (b.π.app i).unop F q δ
  let D := diagramCohomologyFunctor Y (pullbackCoefficientSystem Y b F) q
  let C := pullbackLimitCohomologyCocone Y b c l hl F q
  have hx : C.ι.app i x = C.ι.app i 0 := by
    rw [map_zero]
    change (pullbackLimitCohomologyCocone Y b c l hl F q).ι.app i
      (cohomologyPullback (X := b.pt.unop) (S := (Y.obj i).unop)
        (b.π.app i).unop F q δ) = 0
    rw [pullbackLimitCohomologyCocone_leg]
    exact (cohomologyTransfer_pullbackTriangle
      (X := b.pt.unop) (Y := c.pt.unop) (Z := (Y.obj i).unop)
      l.unop (b.π.app i).unop
      (c.ι.app i).unop (congrArg Quiver.Hom.unop (hl i)) F q δ).trans hδ
  obtain ⟨j, a, ha⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{e}) hc) x 0).mp hx
  have ha' : D.map a x = 0 := by
    change D.map a x = D.map a 0 at ha
    simpa only [map_zero] using ha
  refine ⟨j, ?_⟩
  have ht : D.map a x = cohomologyPullback (X := b.pt.unop) (S := (Y.obj j).unop)
        (b.π.app j).unop F q δ := by
    change diagramCohomologyMap Y (pullbackCoefficientSystem Y b F) q a
      (cohomologyPullback (X := b.pt.unop) (S := (Y.obj i).unop)
        (b.π.app i).unop F q δ) = _
    rw [diagramCohomologyMap_pullbackCoefficientSystem]
    exact cohomologyTransfer_pullbackTriangle
      (X := b.pt.unop) (Y := (Y.obj j).unop) (Z := (Y.obj i).unop)
      (b.π.app j).unop (b.π.app i).unop
      (Y.map a).unop (congrArg Quiver.Hom.unop (b.w a)) F q δ
  exact ht.symm.trans ha'

end FixedSystem

attribute [local instance] hasExtStandard

/-- Original vanishing on the actual neighborhood limit spreads to an actual
pointed etale stage, for any degree and any fixed sheaf on a qcqs morphism. -/
theorem exists_chart_cohomologyPullback_eq_zero
    (R k : Type u) [CommRing R] [Field k] [Algebra R k]
    {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (δ : Sheaf.H.{u + 2} F q)
    (hδ : cohomologyPullback
      (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R k) ≫ j) f) F q δ = 0) :
    ∃ U : GeometricEtaleNeighborhood R k,
      cohomologyPullback (pullback.snd (Spec.algebraMap R U.algebra ≫ j) f) F q δ = 0 := by
  let : IsConnected (GeometricEtaleNeighborhood R k) :=
    IsFiltered.isConnected (GeometricEtaleNeighborhood R k)
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 2}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 2, u + 2}
      (CategoryTheory.forget AddCommGrpCat.{u + 2})
  exact exists_pullback_eq_zero_of_colimit
    (chartCoefficientDiagram R k j f) (chartCoefficientBaseCone R k j f)
    (chartCoefficientLimitCocone R k j f)
    (chartGeometricBaseChangedCone R k j f).pt.hom.op
    (fun i => relativeCoefficient_cone_composite (chartGeometricBaseChangedDiagram R k j f)
      (chartGeometricBaseChangedCone R k j f)
      ((opOpEquivalence (GeometricEtaleNeighborhood R k)).inverse.obj i)) F q
    (chartLimitCohomologyCoconeIsColimit R k j f F q) δ hδ

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
