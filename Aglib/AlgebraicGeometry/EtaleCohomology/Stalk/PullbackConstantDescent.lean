/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCohomologyDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # Original constant-coefficient class and zero descent

The whole triangle-transfer normalization formerly in
`Fields.SeparableExtension.FiniteConstants.ConstantMaps` is retained here.
Original constant classes and relations descend along actual qcqs scheme limits,
before any finite-subalgebra diagram is specialized.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u e

attribute [local instance] hasSheafifyLarge

variable (A : Type u) [AddCommGroup A]

/-- Normalizing the complete fixed-system transfer gives the literal original
constant restriction, in every degree. -/
theorem constantRestriction_triangleTransfer {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ X) (a : T ⟶ S) (h : a ≫ f = g)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} T)] (q : ℕ)
    (c : Sheaf.H.{e} ((inverseImage f).obj (coefficient A X)) q) :
    Sheaf.H.map ((inverseImageConstantIso g).app (value A)).hom q
      (Continuity.cohomologyTransfer a
        ((pullbackTriangleIso g f a h).inv.app (coefficient A X)) q c) =
      Curves.constantRestriction A a q
        (Sheaf.H.map ((inverseImageConstantIso f).app (value A)).hom q c) := by
  rw [Continuity.cohomologyTransfer_eq_extCoefficientTransfer]
  subst g
  let P := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let M := value A
  have hmap := Functor.constantExtRestriction_triangleTransfer
    (constantAdjunction X) (inverseImageAdjunction f) (inverseImageAdjunction a)
    (constantAdjunction S) (inverseImageAdjunction (a ≫ f)) (constantAdjunction T)
    (directImageGlobalSectionsIso f) (directImageCompIso f a)
    (directImageGlobalSectionsIso (a ≫ f)) (directImageGlobalSectionsIso a)
    (directImageGlobalSectionsIso_comp f a) P M q
  have hvalue := congrArg (fun k => k c) hmap
  change Sheaf.H.map ((inverseImageConstantCanonicalIso (a ≫ f)).app M).hom q
      ((inverseImage a).extCoefficientTransfer
        (((inverseImageConstantCanonicalIso a).app P).inv)
        ((inverseImageComp f a).inv.app (coefficient A X)) q c) =
    (inverseImage a).constantExtRestriction (inverseImageConstantCanonicalIso a) P M q
      (Sheaf.H.map ((inverseImageConstantCanonicalIso f).app M).hom q c) at hvalue
  simp only [inverseImageConstantCanonicalIso_eq] at hvalue
  simp only [pullbackTriangleIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.comp_id, Curves.constantRestriction] at hvalue ⊢
  exact hvalue

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

open Opposite Continuity ConstantFinite

universe u e

attribute [local instance] hasSheafifyLarge

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (b : Cone X) (c : Cocone X) (hc : IsColimit c)
  (l : b.pt ⟶ c.pt) (hl : ∀ i, b.π.app i ≫ c.ι.app i = l)
  [∀ i, CompactSpace (X.obj i).unop]
  [∀ i, QuasiSeparatedSpace (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [HasColimitsOfShape I AddCommGrpCat.{e}] [UnivLE.{u, e}]

local instance : IsConnected I := IsFiltered.isConnected I

include hc hl in
/-- Every original constant class descends along an actual structural limit leg. -/
theorem exists_stage_constantCohomologyClass (A : Type u) [AddCommGroup A] (q : ℕ)
    (a : Sheaf.H.{e} (coefficient A c.pt.unop) q) :
    ∃ (i : I) (aᵢ : Sheaf.H.{e} (coefficient A (X.obj i).unop) q),
      Curves.constantRestriction (X := (X.obj i).unop) (S := c.pt.unop)
        A (c.ι.app i).unop q aᵢ = a := by
  let : ∀ i : I, HasExt.{e} (AbelianSheaf.{u, u + 1}
      (unop (((Functor.const I).obj c.pt).obj i))) :=
    fun _ => inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop))
  let E := (inverseImageConstantIso l.unop).app (value A)
  obtain ⟨a', ha'⟩ := (cohomologyMapIso_bijective E q).surjective a
  obtain ⟨i, aᵢ, haᵢ⟩ := exists_stage_cohomologyClass X b c hc l hl
    (coefficient A b.pt.unop) q a'
  let f := (b.π.app i).unop
  let v := (c.ι.app i).unop
  let h : v ≫ f = l.unop := congrArg Quiver.Hom.unop (hl i)
  refine ⟨i, Sheaf.H.map ((inverseImageConstantIso f).app (value A)).hom q aᵢ, ?_⟩
  have hmap := (constantRestriction_triangleTransfer A f l.unop v h q aᵢ).symm
  have hclass := congrArg (Sheaf.H.map E.hom q) haᵢ
  exact (hmap.trans hclass).trans ha'

variable [HasExt.{e} (AbelianSheaf.{u, u + 1} b.pt.unop)]

include hc hl in
/-- A constant source class vanishing at the limit vanishes at an actual stage. -/
theorem exists_stage_constantCohomologyZero (A : Type u) [AddCommGroup A] (q : ℕ)
    (a : Sheaf.H.{e} (coefficient A b.pt.unop) q)
    (ha : Curves.constantRestriction A l.unop q a = 0) :
    ∃ i : I, Curves.constantRestriction (X := b.pt.unop) (S := (X.obj i).unop)
      A (b.π.app i).unop q a = 0 := by
  let : ∀ i : I, HasExt.{e} (AbelianSheaf.{u, u + 1}
      (unop (((Functor.const I).obj b.pt).obj i))) :=
    fun _ => inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} b.pt.unop))
  let : ∀ i : I, HasExt.{e} (AbelianSheaf.{u, u + 1}
      (unop (((Functor.const I).obj c.pt).obj i))) :=
    fun _ => inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop))
  let E := (inverseImageConstantIso l.unop).app (value A)
  have hraw : cohomologyPullback.{u, e, e} l.unop (coefficient A b.pt.unop) q a = 0 := by
    apply (cohomologyMapIso_bijective E q).injective
    change Curves.constantRestriction A l.unop q a = Sheaf.H.map E.hom q 0
    rw [map_zero]
    exact ha
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{e}) :=
    preservesFilteredColimitsOfSize_of_univLE.{e, e, u, u} _
  obtain ⟨i, hi⟩ := exists_pullback_eq_zero_of_colimit X b c l hl
    (coefficient A b.pt.unop) q
    (isColimitPullbackCohomologyCocone X b c hc l hl (coefficient A b.pt.unop) q) a hraw
  refine ⟨i, ?_⟩
  change Sheaf.H.map ((inverseImageConstantIso (b.π.app i).unop).app (value A)).hom q
    (cohomologyPullback.{u, e, e} (b.π.app i).unop (coefficient A b.pt.unop) q a) = 0
  exact (congrArg (Sheaf.H.map
    ((inverseImageConstantIso (b.π.app i).unop).app (value A)).hom q) hi).trans (map_zero _)

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
