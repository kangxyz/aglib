/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Restriction squares of adjunctions

A square of the right adjoints gives an isomorphism between the composite left
adjoints. The restriction mate is defined using the original adjunctions, and
the unit and counit equations identify it with that isomorphism. No invertibility
of a partial mate is inferred from invertibility of the right-adjoint square.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Adjunction

open CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
  {i : A ⥤ C} {I : C ⥤ A} {j : B ⥤ D} {J : D ⥤ B}
  (a : L ⊣ R) (b : L' ⊣ R') (c : i ⊣ I) (d : j ⊣ J)
  (e : J ⋙ R ≅ R' ⋙ I)

/-- The first composite adjunction in a restriction square. -/
def squareLeftAdjunction : L ⋙ j ⊣ J ⋙ R := a.comp d

/-- The second composite adjunction, transported along the given right-adjoint square. -/
def squareRightAdjunction : i ⋙ L' ⊣ J ⋙ R :=
  (c.comp b).ofNatIsoRight e.symm

/-- The isomorphism of composite left adjoints determined by the right-adjoint square. -/
def squareLeftIso : L ⋙ j ≅ i ⋙ L' :=
  (squareLeftAdjunction a d).leftAdjointUniq (squareRightAdjunction b c e)

/-- The restriction mate of the right-adjoint square, using the original units and counits. -/
def squareRestrictionMap (N : B) : i.obj (R.obj N) ⟶ R'.obj (j.obj N) :=
  (c.homEquiv _ _).symm (R.map (d.unit.app N) ≫ e.hom.app (j.obj N))

theorem squareLeftIso_hom_adjoint (M : A) (N : D)
    (h : L'.obj (i.obj M) ⟶ N) :
    (squareLeftAdjunction a d).homEquiv M N ((squareLeftIso a b c d e).hom.app M ≫ h) =
      (squareRightAdjunction b c e).homEquiv M N h := by
  rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, ← Category.assoc]
  unfold squareLeftIso
  rw [unit_leftAdjointUniq_hom_app]

/-- Restricting an adjoint arrow agrees with adjoining its restriction mate. -/
theorem squareAdjoint_eq {M : A} {N : B} (f : M ⟶ R.obj N) :
    j.map ((a.homEquiv M N).symm f) =
      (squareLeftIso a b c d e).hom.app M ≫
        (b.homEquiv _ _).symm (i.map f ≫ squareRestrictionMap c d e N) := by
  apply ((squareLeftAdjunction a d).homEquiv _ _).injective
  rw [squareLeftIso_hom_adjoint]
  simp only [squareLeftAdjunction, squareRightAdjunction,
    homEquiv_ofNatIsoRight_apply, comp_homEquiv]
  let g := (a.homEquiv M N).symm f
  change a.homEquiv _ _ (d.homEquiv _ _ (j.map g)) =
    c.homEquiv _ _
      (b.homEquiv _ _ ((b.homEquiv _ _).symm
        (i.map f ≫ squareRestrictionMap c d e N))) ≫ e.inv.app _
  rw [Equiv.apply_symm_apply, homEquiv_unit d, unit_naturality,
    homEquiv_naturality_right, Equiv.apply_symm_apply, homEquiv_naturality_left]
  unfold squareRestrictionMap
  rw [Equiv.apply_symm_apply]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact congrArg (fun h ↦ f ≫ h) (Category.comp_id (R.map (d.unit.app N))).symm

/-- The original-unit equation for the composite left-adjoint isomorphism. -/
theorem squareUnit (M : A) :
    b.unit.app (i.obj M) ≫ R'.map ((squareLeftIso a b c d e).inv.app M) =
      i.map (a.unit.app M) ≫ squareRestrictionMap c d e (L.obj M) := by
  let f := i.map (a.unit.app M) ≫ squareRestrictionMap c d e (L.obj M)
  have h := squareAdjoint_eq a b c d e (a.unit.app M)
  dsimp only [Functor.id_obj] at h
  rw [a.homEquiv_symm_unit, Functor.map_id] at h
  have he : (b.homEquiv _ _).symm f = (squareLeftIso a b c d e).inv.app M := by
    apply (cancel_epi ((squareLeftIso a b c d e).hom.app M)).mp
    exact h.symm.trans (Iso.hom_inv_id_app (squareLeftIso a b c d e) M).symm
  have hh := congrArg (b.homEquiv _ _) he
  rw [Equiv.apply_symm_apply, homEquiv_unit] at hh
  exact hh.symm

/-- The original-counit equation for the same square and its restriction mate. -/
theorem squareCounit (N : B) :
    L'.map (squareRestrictionMap c d e N) ≫ b.counit.app (j.obj N) =
      (squareLeftIso a b c d e).inv.app (R.obj N) ≫ j.map (a.counit.app N) := by
  have h := squareAdjoint_eq a b c d e (𝟙 (R.obj N))
  simp only [homEquiv_counit, Functor.map_id, Category.id_comp] at h
  rw [h]
  simp

end CategoryTheory.Adjunction
