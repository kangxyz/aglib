/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Injective.MappedResolution
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Original Ext comparison for an acyclic coefficient under an adjunction

Only the left adjoint is exact. The comparison is its original Ext map followed
by the actual counit. A mapped injective resolution supplies its cycle formula;
no exactness of the right adjoint on other coefficients is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex

universe u v u' v' w w'

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (adj : F ⊣ G) (A : C) (B : D) (n : ℕ)

/-- The original exact-left-adjoint Ext map followed by the original counit. -/
def extCounitMap : Ext A (G.obj B) n →+ Ext (F.obj A) B n where
  toFun x := (x.mapExactFunctor F).comp (Ext.mk₀ (adj.counit.app B)) (Nat.add_zero n)
  map_zero' := by simp
  map_add' x y := by simp

omit [G.Additive] in
/-- Degree zero is precisely the native Hom adjunction, with no new normalization. -/
theorem extCounitMap_mk₀ (f : A ⟶ G.obj B) :
    adj.extCounitMap A B 0 (Ext.mk₀ f) = Ext.mk₀ ((adj.homEquiv A B).symm f) := by
  simp only [extCounitMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, adj.homEquiv_counit]

variable {A B n}

omit [G.Additive] in
/-- Naturality retains arbitrary coefficient arrows, including non-linear additive maps. -/
theorem extCounitMap_naturality {B' : D} (f : B ⟶ B') (x : Ext A (G.obj B) n) :
    adj.extCounitMap A B' n (x.comp (Ext.mk₀ (G.map f)) (Nat.add_zero n)) =
      (adj.extCounitMap A B n x).comp (Ext.mk₀ f) (Nat.add_zero n) := by
  simp only [extCounitMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc _ _ _ _ (Nat.add_zero 0) (by omega),
    Ext.comp_assoc _ _ _ _ (Nat.add_zero 0) (by omega),
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  congr 1
  exact congrArg Ext.mk₀ (adj.counit.naturality f)

section Resolution

variable [PreservesFiniteLimits G] [G.PreservesInjectiveObjects]
  (I : InjectiveResolution B)
  (hI : ∀ n : ℕ, ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1))

omit [HasExt C] [HasExt D] in
/-- The counit on every term of the actual mapped resolution. -/
def mappedResolutionCounit :
    (F.mapHomologicalComplex (.up ℕ)).obj (I.mapOfExactAt G hI).cocomplex ⟶
      I.cocomplex where
  f n := adj.counit.app (I.cocomplex.X n)
  comm' i j _ := by
    simpa only [InjectiveResolution.mapOfExactAt, Functor.mapHomologicalComplex_obj_d,
      Functor.comp_map, Functor.id_map] using (adj.counit.naturality (I.cocomplex.d i j)).symm

omit [HasExt C] [HasExt D] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The termwise counit preserves the original augmentation. -/
theorem mappedResolutionCounit_augmentation :
    F.map ((I.mapOfExactAt G hI).ι.f 0) ≫
        (adj.mappedResolutionCounit I hI).f 0 = adj.counit.app B ≫ I.ι.f 0 := by
  simpa only [InjectiveResolution.mapOfExactAt,
    InjectiveResolution.mapAugmentation_f_zero, mappedResolutionCounit,
    CochainComplex.single₀_obj_zero, Functor.comp_map, Functor.id_map,
    Functor.comp_obj, Functor.id_obj] using
      adj.counit.naturality (I.ι.f 0)

/-- On original resolution cocycles, the canonical Ext map is exactly the Hom adjunction. -/
theorem extCounitMap_extMk (f : A ⟶ G.obj (I.cocomplex.X n))
    (hf : f ≫ G.map (I.cocomplex.d n (n + 1)) = 0) :
    adj.extCounitMap A B n ((I.mapOfExactAt G hI).extMk f (n + 1) rfl hf) =
      I.extMk ((adj.homEquiv A (I.cocomplex.X n)).symm f) (n + 1) rfl (by
        rw [← adj.homEquiv_naturality_right_symm, hf, adj.homAddEquiv_symm_zero]) := by
  exact InjectiveResolution.ExactFunctor.extMk_mapExactFunctor_comp_mk₀
    F (I.mapOfExactAt G hI) I (adj.counit.app B)
    (adj.mappedResolutionCounit I hI) (adj.mappedResolutionCounit_augmentation I hI) f hf

include I hI in
/-- Every original target Ext class comes from the actual counit comparison. -/
theorem extCounitMap_surjective (n : ℕ) :
    Function.Surjective (adj.extCounitMap A B n) := by
  intro x
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  have hg : adj.homEquiv A (I.cocomplex.X n) f ≫
      G.map (I.cocomplex.d n (n + 1)) = 0 := by
    rw [← adj.homEquiv_naturality_right, hf, adj.homAddEquiv_zero]
  refine ⟨(I.mapOfExactAt G hI).extMk (adj.homEquiv _ _ f) (n + 1) rfl hg, ?_⟩
  rw [adj.extCounitMap_extMk I hI]
  simp only [Equiv.symm_apply_apply]

include I hI in
/-- A positive original class vanishes if its counit image vanishes: the actual
Hom adjunction transports a boundary back to a boundary. -/
theorem extCounitMap_eq_zero_succ (n : ℕ) (x : Ext A (G.obj B) (n + 1))
    (hx : adj.extCounitMap A B (n + 1) x = 0) : x = 0 := by
  obtain ⟨f, hf, rfl⟩ := (I.mapOfExactAt G hI).extMk_surjective x (n + 2) rfl
  rw [adj.extCounitMap_extMk I hI] at hx
  obtain ⟨g, hg⟩ := (I.extMk_eq_zero_iff _ _ _ _ n rfl).mp hx
  apply ((I.mapOfExactAt G hI).extMk_eq_zero_iff _ _ _ _ n rfl).mpr
  refine ⟨adj.homEquiv A (I.cocomplex.X n) g, ?_⟩
  change adj.homEquiv A (I.cocomplex.X n) g ≫
    G.map (I.cocomplex.d n (n + 1)) = f
  rw [← adj.homEquiv_naturality_right, hg, Equiv.apply_symm_apply]

include I hI in
/-- The original comparison is bijective in every degree for this coefficient.
The right adjoint need not be exact on other coefficients. -/
theorem extCounitMap_bijective_of_exactAt (n : ℕ) :
    Function.Bijective (adj.extCounitMap A B n) := by
  refine ⟨?_, adj.extCounitMap_surjective I hI n⟩
  cases n with
  | zero =>
    intro x y h
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective A (G.obj B)).2 x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective A (G.obj B)).2 y
    rw [adj.extCounitMap_mk₀, adj.extCounitMap_mk₀] at h
    have hfg := (adj.homEquiv A B).symm.injective
      ((Ext.mk₀_bijective (F.obj A) B).1 h)
    exact congrArg Ext.mk₀ hfg
  | succ n =>
    intro x y h
    apply sub_eq_zero.mp
    apply adj.extCounitMap_eq_zero_succ I hI n
    rw [map_sub, h, sub_self]


end Resolution

end CategoryTheory.Adjunction
