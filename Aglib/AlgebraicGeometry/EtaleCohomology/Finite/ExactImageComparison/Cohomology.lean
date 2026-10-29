/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-! # Original sheaf cohomology under exact direct image

The comparison uses the native exact-adjunction Ext equivalence and the original
inverse-image constant-sheaf isomorphism. Its forward map is precisely original
cohomology pullback followed by the original adjunction counit. No arbitrary
base-change pullback is asserted invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Abelian.Ext

universe v w

/-- Original isomorphism transport on additive Ext, without a choice of scalar module. -/
def precompIsoAddEquiv {C : Type*} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {A B : C} (e : A ≅ B) (F : C) (q : ℕ) : Ext.{w} B F q ≃+ Ext.{w} A F q :=
  { (mk₀ e.hom).precomp F (zero_add q) with
    invFun := fun x => (mk₀ e.inv).comp x (zero_add q)
    left_inv := fun x => by
      change (mk₀ e.inv).comp ((mk₀ e.hom).comp x (zero_add q)) (zero_add q) = x
      simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀,
        e.inv_hom_id, mk₀_id_comp]
    right_inv := fun x => by
      change (mk₀ e.hom).comp ((mk₀ e.inv).comp x (zero_add q)) (zero_add q) = x
      simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀,
        e.hom_inv_id, mk₀_id_comp] }

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]
  (f : X ⟶ S) [PreservesFiniteColimits (directImage f)]

/-- Original cohomology of an exact direct image agrees with cohomology on the source,
with independent Ext universes on the two schemes. -/
def cohomologyDirectImageAddEquiv (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.H.{wS} ((directImage f).obj F) q ≃+ Sheaf.H.{wX} F q :=
  (inverseImageAdjunction f).extEquiv.symm.trans
    (Ext.precompIsoAddEquiv
      (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).symm)
      F q)

/-- The actual comparison is original pullback followed by the original counit map. -/
theorem cohomologyDirectImageAddEquiv_apply
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (a : Sheaf.H.{wS} ((directImage f).obj F) q) :
    cohomologyDirectImageAddEquiv f F q a =
      Sheaf.H.map ((inverseImageAdjunction f).counit.app F) q
        (cohomologyPullback f ((directImage f).obj F) q a) := by
  simp only [cohomologyDirectImageAddEquiv, AddEquiv.trans_apply,
    Ext.precompIsoAddEquiv, Adjunction.extEquiv_symm_apply,
    Sheaf.H.map_apply, cohomologyPullback_apply]
  exact (Ext.comp_assoc (a₁ := 0) (a₂ := q) (a₃ := 0) (a := q) _ _ _
    (zero_add q) (add_zero q) (by omega)).symm

/-- The exact-image comparison sends the original unit map to the original pullback. -/
theorem cohomologyDirectImageAddEquiv_unit
    (F : AbelianSheaf.{u, u + 1} S) (q : ℕ) (x : Sheaf.H.{wS} F q) :
    cohomologyDirectImageAddEquiv f ((inverseImage f).obj F) q
        (Sheaf.H.map ((inverseImageAdjunction f).unit.app F) q x) =
      cohomologyPullback f F q x := by
  rw [cohomologyDirectImageAddEquiv_apply, cohomologyPullback_coefficientMap,
    ← Sheaf.H.map_comp_apply, (inverseImageAdjunction f).left_triangle_components F]
  change ((Sheaf.functorH.{wX, u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) q).map (𝟙 ((inverseImage f).obj F)))
      (cohomologyPullback f F q x) = cohomologyPullback f F q x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Coefficient naturality retains the original maps on both cohomology groups. -/
theorem cohomologyDirectImageAddEquiv_naturality
    {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{wS} ((directImage f).obj F) q) :
    cohomologyDirectImageAddEquiv f G q (Sheaf.H.map ((directImage f).map a) q x) =
      Sheaf.H.map a q (cohomologyDirectImageAddEquiv f F q x) := by
  simp only [cohomologyDirectImageAddEquiv, AddEquiv.trans_apply,
    Ext.precompIsoAddEquiv, Sheaf.H.map_apply,
    Adjunction.extEquiv_symm_naturality_right₀]
  exact (Ext.comp_assoc (a₁ := 0) (a₂ := q) (a₃ := 0) (a := q) _ _ _
    (zero_add q) (add_zero q) (by omega)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
