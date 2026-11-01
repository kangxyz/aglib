/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingBiproduct

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v u' v' w w'

section IndependentWorlds

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (A : D)

/-- Degree-zero components use the original projection followed by inclusion,
with the correct covariance and no chosen basis or alternative Ext carrier. -/
example {I : Type*} [Fintype I] {F : I → C} {b : Bicone F} (hb : b.IsBilimit)
    (G : C) (f : A ⟶ L.obj b.pt) (g : b.pt ⟶ G) :
    L.extPairing A (Ext.mk₀ f) (Ext.mk₀ g) (zero_add 0) =
      ∑ i, Ext.mk₀ (f ≫ L.map (b.π i) ≫ L.map (b.ι i ≫ g)) := by
  rw [Functor.extPairing_biproduct L A hb G (zero_add 0)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Functor.extPairing, Ext.mk₀_comp_mk₀, Ext.mapExactFunctor_mk₀,
    Category.assoc]

/-- The actual degree-zero transpose needed by the consumer is bijective
from component perfectness, at independent source and target Ext universes. -/
example (n : ℕ) {I : Type*} [Finite I] {F : I → C} {b : Bicone F}
    (hb : b.IsBilimit) (G : C)
    [Module (ZMod n) (Ext.{w'} A (L.obj b.pt) 2)]
    [∀ i, Module (ZMod n) (Ext.{w'} A (L.obj (F i)) 2)]
    [Module (ZMod n) (Ext.{w} b.pt G 0)]
    [∀ i, Module (ZMod n) (Ext.{w} (F i) G 0)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) 2)]
    (τ : Ext.{w'} A (L.obj G) 2 →ₗ[ZMod n] ZMod n)
    (hF : ∀ i, ((L.extPairingLinearMap A n (F i) G 2 0 2 rfl).compr₂ τ).IsPerfPair) :
    Function.Bijective ((L.extPairingLinearMap A n b.pt G 2 0 2 rfl).compr₂ τ).flip := by
  have hp := Functor.isPerfPair_extPairingLinearMap_compr₂_biproduct L A n hb G 2 0 2 rfl τ hF
  exact hp.bijective_right

/-- Empty coefficient biproducts need no component-perfectness premise. -/
example (n : ℕ) {I : Type*} [Finite I] [IsEmpty I] {F : I → C} {b : Bicone F}
    (hb : b.IsBilimit) (G : C) (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj b.pt) r)]
    [Module (ZMod n) (Ext.{w} b.pt G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (τ : Ext.{w'} A (L.obj G) t →ₗ[ZMod n] ZMod n) :
    ((L.extPairingLinearMap A n b.pt G r s t h).compr₂ τ).IsPerfPair := by
  let (i : I) : Module (ZMod n) (Ext.{w'} A (L.obj (F i)) r) := isEmptyElim i
  let (i : I) : Module (ZMod n) (Ext.{w} (F i) G s) := isEmptyElim i
  exact Functor.isPerfPair_extPairingLinearMap_compr₂_biproduct L A n hb G r s t h τ
    (fun i => isEmptyElim i)

/-- An actual coefficient Iso preserves both original dual-map bijectivities. -/
example (n : ℕ) {F F' G : C} (e : F ≅ F') (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)]
    [Module (ZMod n) (Ext.{w'} A (L.obj F') r)]
    [Module (ZMod n) (Ext.{w} F G s)] [Module (ZMod n) (Ext.{w} F' G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (τ : Ext.{w'} A (L.obj G) t →ₗ[ZMod n] ZMod n)
    (hp : ((L.extPairingLinearMap A n F G r s t h).compr₂ τ).IsPerfPair) :
    Function.Bijective ((L.extPairingLinearMap A n F' G r s t h).compr₂ τ) ∧
      Function.Bijective ((L.extPairingLinearMap A n F' G r s t h).compr₂ τ).flip := by
  have hq := (Functor.isPerfPair_extPairingLinearMap_compr₂_iso_iff L A n e r s t h τ).mpr hp
  exact ⟨hq.bijective_left, hq.bijective_right⟩

end IndependentWorlds

section CanonicalModulusOne

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Modulus one uses the original identity-annihilation actions at both
native Ext carriers, including the actual biproduct identity. -/
example {I : Type*} [Fintype I] {F : I → C} {b : Bicone F} (hb : b.IsBilimit)
    (hF : ∀ i, 1 • 𝟙 (F i) = 0) (G : C) (s : ℕ) :
    letI (i : I) : Module (ZMod 1) (Ext.{w} (F i) G s) :=
      Ext.zmodModuleOfNsmulIdLeft 1 (hF i) G s
    letI : Module (ZMod 1) (Ext.{w} b.pt G s) :=
      Ext.zmodModuleOfNsmulIdLeft 1 (hb.nsmul_id_eq_zero 1 hF) G s
    Function.Bijective (Ext.biproductZModLinearEquiv 1 hb G s) := by
  let (i : I) : Module (ZMod 1) (Ext.{w} (F i) G s) :=
    Ext.zmodModuleOfNsmulIdLeft 1 (hF i) G s
  let : Module (ZMod 1) (Ext.{w} b.pt G s) :=
    Ext.zmodModuleOfNsmulIdLeft 1 (hb.nsmul_id_eq_zero 1 hF) G s
  exact (Ext.biproductZModLinearEquiv 1 hb G s).bijective

end CanonicalModulusOne

/--
info: 'CategoryTheory.Functor.extPairingLinearMap_compr₂_biproduct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extPairingLinearMap_compr₂_biproduct

/--
info: 'CategoryTheory.Functor.isPerfPair_extPairingLinearMap_compr₂_biproduct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.isPerfPair_extPairingLinearMap_compr₂_biproduct

/--
info: 'CategoryTheory.Functor.isPerfPair_extPairingLinearMap_compr₂_iso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.isPerfPair_extPairingLinearMap_compr₂_iso_iff
