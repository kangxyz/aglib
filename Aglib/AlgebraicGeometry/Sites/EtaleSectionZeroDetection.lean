/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSectionZeroGerm
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Detection of the original etale section zero locus

A zero geometric germ has an actual zero neighbourhood in the original
small-etale site. The original inverse-image unit preserves and reflects this
condition at its original pulled-back point. No new sheaf or stalk model is
introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Etale

universe u

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- A zero native geometric germ is witnessed by an actual etale restriction
of the unchanged section, at the unchanged point of the test scheme. -/
theorem mem_sectionZeroLocus_of_geometricGerm_eq_zero
    (s : Spec (.of Ω) ⟶ X) (F : X.Etaleᵒᵖ ⥤ Ab.{u + 1}) {U : X.Etale}
    (a : F.obj (op U)) (p : (pointSmallEtale s).fiber.obj U)
    (h : (pointSmallEtale s).toPresheafFiber U p F a = 0) :
    p.left (default : Spec (.of Ω)) ∈ sectionZeroLocus F a := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  have hz : (pointSmallEtale s).toPresheafFiber U p F a =
      (pointSmallEtale s).toPresheafFiber U p F 0 := by
    simpa only [map_zero] using h
  obtain ⟨V, f, q, hq, ha⟩ :=
    ((pointSmallEtale s).toPresheafFiber_eq_iff' U p a 0).mp hz
  refine ⟨V, f, q.left (default : Spec (.of Ω)), ?_, ?_⟩
  · have he : q.left ≫ f.left = p.left :=
      congrArg (fun r : (pointSmallEtale s).fiber.obj U => r.left) hq
    exact congrArg (fun k : Spec (.of Ω) ⟶ U.left => k (default : Spec (.of Ω))) he
  · simpa only [map_zero] using ha

/-- Membership in the original open zero locus is exactly vanishing of the
native geometric germ, for any chosen lift of the point. -/
theorem mem_sectionZeroLocus_iff_geometricGerm_eq_zero
    (s : Spec (.of Ω) ⟶ X) (F : X.Etaleᵒᵖ ⥤ Ab.{u + 1}) {U : X.Etale}
    (a : F.obj (op U)) (p : (pointSmallEtale s).fiber.obj U) :
    p.left (default : Spec (.of Ω)) ∈ sectionZeroLocus F a ↔
      (pointSmallEtale s).toPresheafFiber U p F a = 0 :=
  ⟨geometricGerm_eq_zero_of_mem_sectionZeroLocus.{u, u + 1} s F a p,
    mem_sectionZeroLocus_of_geometricGerm_eq_zero s F a p⟩

open EtaleCohomology EtaleCohomology.CoefficientStalkBaseChange

attribute [local instance] hasSheafifyLarge

/-- The original inverse-image unit preserves and reflects the zero locus at
its actual pulled-back test point. This is the original stalk-unit equation,
not an arbitrary identification of stalk values. -/
theorem inverseImageUnit_mem_sectionZeroLocus_iff {S : Scheme.{u}}
    (f : S ⟶ X) (s : Spec (.of Ω) ⟶ S)
    (F : AbelianSheaf.{u, u + 1} X) (U : X.Etale)
    (a : F.obj.obj (op U)) (p : (pointSmallEtale (s ≫ f)).fiber.obj U) :
    (pulledBackPoint f s U p).left (default : Spec (.of Ω)) ∈
        sectionZeroLocus ((inverseImage f).obj F).obj
          (((inverseImageAdjunction f).unit.app F).hom.app (op U) a) ↔
      p.left (default : Spec (.of Ω)) ∈ sectionZeroLocus F.obj a := by
  refine (mem_sectionZeroLocus_iff_geometricGerm_eq_zero s
    ((inverseImage f).obj F).obj
    (((inverseImageAdjunction f).unit.app F).hom.app (op U) a)
    (pulledBackPoint f s U p)).trans ?_
  refine Iff.trans ?_
    (mem_sectionZeroLocus_iff_geometricGerm_eq_zero (s ≫ f) F.obj a p).symm
  let e := (StalkInverseImage.stalkUnitNatIso f s).app F
  have he : e.hom ((pointSmallEtale (s ≫ f)).toPresheafFiber U p F.obj a) =
      (pointSmallEtale s).toPresheafFiber ((siteBaseChange f).obj U)
        (pulledBackPoint f s U p) ((inverseImage f).obj F).obj
          (((inverseImageAdjunction f).unit.app F).hom.app (op U) a) :=
    ConcreteCategory.congr_hom
      (StalkInverseImage.germ_stalkUnitNatIso f s F U p) a
  constructor
  · intro h
    exact (ConcreteCategory.bijective_of_isIso e.hom).injective
      ((he.trans h).trans (map_zero e.hom.hom).symm)
  · intro h
    exact he.symm.trans (by rw [h, map_zero])

end AlgebraicGeometry.Scheme.Etale
