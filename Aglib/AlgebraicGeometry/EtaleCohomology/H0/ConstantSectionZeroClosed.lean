/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.SectionZeroOpen
public import Aglib.AlgebraicGeometry.Sites.EtaleLocalPreimage
public import Aglib.CategoryTheory.Sites.Point.Constant

/-! # Closed zero loci for arbitrary constant coefficients

Local surjectivity of the original constant sheafification unit supplies an
actual constant representative near every point. The original constant germ
is invertible, so a nonzero representative remains nonzero throughout that
chart. No finiteness or torsion hypothesis on the coefficient is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- The original zero locus of a section of an arbitrary constant abelian
sheaf is closed on each actual small-etale test scheme. -/
theorem isClosed_sectionZeroLocus_constant {X : Scheme.{u}}
    (A : AddCommGrpCat.{u + 1}) {U : X.Etale}
    (a : ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A).obj.obj
      (op U)) :
    IsClosed (Scheme.Etale.sectionZeroLocus
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A).obj a) := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  let q := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)
  let : Presheaf.IsLocallySurjective X.smallEtaleTopology q :=
    Presheaf.isLocallySurjective_toSheafify' X.smallEtaleTopology _
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨V, f, y, b, hy, hb⟩ := Scheme.Etale.exists_localPreimage_at_point q a x
  have hbzero : b ≠ 0 := by
    intro h
    apply hx
    refine ⟨V, f, y, hy, ?_⟩
    exact hb.symm.trans (h ▸ map_zero (q.app (op V)).hom)
  apply Filter.mem_of_superset (f.left.isOpenMap.isOpen_range.mem_nhds ⟨y, hy⟩)
  rintro z ⟨w, rfl⟩ hz
  let η := FibrewiseClosed.geometricPoint w
  let s := η ≫ V.hom
  let p : (pointSmallEtale s).fiber.obj V := Over.homMk η rfl
  let pU := (pointSmallEtale s).fiber.map f p
  have hpU : pU.left (default : Spec (.of (FibrewiseClosed.pointField w))) = f.left w := by
    change f.left (η default) = f.left w
    rw [FibrewiseClosed.geometricPoint_apply]
  have ha := Scheme.Etale.geometricGerm_eq_zero_of_mem_sectionZeroLocus.{u, u + 1}
    s F.obj a pU (by rw [hpU]; exact hz)
  have hw := ConcreteCategory.congr_hom
    ((pointSmallEtale s).toPresheafFiber_w f p F.obj) a
  have hq : ((q.app (op V)) ≫ (pointSmallEtale s).toPresheafFiber V p F.obj) b = 0 := by
    change (pointSmallEtale s).toPresheafFiber V p F.obj (q.app (op V) b) = 0
    rw [hb]
    exact hw.trans ha
  have : IsIso ((q.app (op V)) ≫ (pointSmallEtale s).toPresheafFiber V p F.obj) :=
    (pointSmallEtale s).constantSheafGerm_isIso V p A
  exact hbzero ((ConcreteCategory.bijective_of_isIso
    ((q.app (op V)) ≫ (pointSmallEtale s).toPresheafFiber V p F.obj)).injective
      (hq.trans (map_zero _).symm))

/-- The original global zero open of a constant coefficient is also closed. -/
theorem isClosed_sectionZeroOpen_constant (X : Scheme.{u})
    (A : AddCommGrpCat.{u + 1})
    (a : (globalSections X).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) :
    IsClosed (sectionZeroOpen
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) a : Set X) :=
  isClosed_sectionZeroLocus_constant A a

end AlgebraicGeometry.Scheme.EtaleCohomology
