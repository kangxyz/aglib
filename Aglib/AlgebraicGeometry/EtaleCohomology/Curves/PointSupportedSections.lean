/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PointSupportedFactor
public import Aglib.AlgebraicGeometry.Sites.EtaleSectionZeroGerm
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage.Projection
public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Actual sections factor through their geometric support subobjects -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Set
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) {U : X.Etale}

/-- The image on the base of the actual etale-local support of a section. -/
def sectionSupportImage (a : F.obj.obj (op U)) : Set X :=
  U.hom '' (Etale.sectionZeroLocus F.obj a)ᶜ

private theorem outside_unit_section_zero (a : F.obj.obj (op U)) (x : X)
    (hx : x ∉ sectionSupportImage F a) :
    ((pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction.unit.app
      F).hom.app (op U) a = 0 := by
  let Φ := pointSmallEtale (FibrewiseClosed.geometricPoint x)
  apply Concrete.limit_ext
    (Discrete.functor (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj F))
  rintro ⟨p⟩
  change Pi.π (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj F) p
      ((Φ.skyscraperSheafAdjunction.unit.app F).hom.app (op U) a) =
    Pi.π (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj F) p 0
  rw [map_zero]
  let o : Spec (.of (FibrewiseClosed.pointField x)) := default
  have hp : U.hom (p.left o) = x := by
    have h := congrArg (fun k : Spec (.of (FibrewiseClosed.pointField x)) ⟶ X => k default) p.w
    exact h.trans (FibrewiseClosed.geometricPoint_apply x default)
  have hzero : p.left o ∈ Etale.sectionZeroLocus F.obj a := by
    by_contra hn
    exact hx ⟨p.left o, hn, hp⟩
  have hg := Etale.geometricGerm_eq_zero_of_mem_sectionZeroLocus.{u, u + 1}
    (FibrewiseClosed.geometricPoint x) F.obj a p hzero
  exact (ConcreteCategory.congr_hom (StalkInverseImage.pointSkyscraperUnit_π Φ F U p) a).trans hg

/-- Every original section lifts to the actual subobject supported on the image of its
etale-local support. In particular, finite local support gives a finite support stage. -/
theorem exists_pointSupported_section (a : F.obj.obj (op U)) :
    ∃ b : (pointSupportedSubobject F (sectionSupportImage F a) :
        AbelianSheaf.{u, u + 1} X).obj.obj (op U),
      (pointSupportedSubobject F (sectionSupportImage F a)).arrow.hom.app (op U) b = a := by
  let t := (sectionsAddEquiv.{u + 1, u, u + 1} X.smallEtaleTopology U F).symm a
  have htval : sectionsEquiv.{u + 1, u, u + 1} X.smallEtaleTopology U F t = a := by
    exact (sectionsAddEquiv.{u + 1, u, u + 1} X.smallEtaleTopology U F).apply_symm_apply a
  have ht : (pointSupportedSubobject F (sectionSupportImage F a)).Factors t := by
    apply (pointSupportedSubobject_factors_iff _ t).mpr
    intro x hx
    apply (sectionsAddEquiv.{u + 1, u, u + 1} X.smallEtaleTopology U _).injective
    rw [map_zero]
    change sectionsEquiv.{u + 1, u, u + 1} X.smallEtaleTopology U _ (t ≫ _) = 0
    rw [sectionsEquiv_naturality.{u + 1, u, u + 1}, htval]
    exact outside_unit_section_zero F a x hx
  let b := sectionsAddEquiv.{u + 1, u, u + 1} X.smallEtaleTopology U _
    ((pointSupportedSubobject F (sectionSupportImage F a)).factorThru t ht)
  refine ⟨b, ?_⟩
  have h := sectionsEquiv_naturality.{u + 1, u, u + 1} X.smallEtaleTopology U
    ((pointSupportedSubobject F (sectionSupportImage F a)).factorThru t ht)
    (pointSupportedSubobject F (sectionSupportImage F a)).arrow
  rw [Subobject.factorThru_arrow] at h
  exact h.symm.trans htval

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
