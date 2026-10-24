/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant
public import Aglib.Algebra.Category.ModuleCat.FullForget
public import Aglib.Algebra.Category.Grp.ZModQuotient
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Positive ZMod local constancy agrees with the original predicate

A finite additive trivialization of a genuine ZMod coefficient lifts to a
module trivialization. On each chart we replace its additive value `A` by the
actual quotient `cokernel (n • 𝟙 A)`. Its constant sheaf is unchanged because
the original coefficient is annihilated by `n`. This argument also covers
empty charts, where annihilation of the constant sheaf does not imply
annihilation of its value. No points or nonemptiness premise is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- The original constant additive sheaf is the constant sheaf of its actual
ZMod quotient whenever the constant sheaf itself is annihilated by the modulus. -/
def constantZModQuotientUnderlyingIso (X : Scheme.{u}) (n : ℕ)
    (A : AddCommGrpCat.{u + 1})
    (hA : n • 𝟙 ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) = 0) :
    (moduleUnderlying (ZMod n) X).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))).obj
        (AddCommGrpCat.zmodQuotient A n)) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A := by
  let C : AddCommGrpCat.{u + 1} ⥤ AbelianSheaf.{u, u + 1} X :=
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  letI : C.IsLeftAdjoint := (constantAdjunction X).isLeftAdjoint
  have hmap : C.map (n • 𝟙 A) = 0 := by
    rw [Functor.map_nsmul, C.map_id]
    exact hA
  exact (moduleConstantUnderlyingIso (ZMod n) X).app (AddCommGrpCat.zmodQuotient A n) ≪≫
    C.mapIso (AddCommGrpCat.zmodQuotientUnderlyingIso A n) ≪≫
    PreservesCokernel.iso C (n • 𝟙 A) ≪≫
    cokernelIsoOfEq hmap ≪≫ cokernelZeroIsoTarget

/-- A finite additive trivialization lifts on its same actual charts to
finite-type ZMod-module trivializations, even if some charts are empty. -/
def finiteTypeLocalTrivializationOfZMod {X : Scheme.{u}} (n : ℕ)
    (F : ModuleSheaf (ZMod n) X)
    (t : FiniteLocalTrivialization ((moduleUnderlying (ZMod n) X).obj F)) :
    FiniteTypeLocalTrivialization F where
  index := t.index
  chart := t.chart
  covers := t.covers
  value i := AddCommGrpCat.zmodQuotient (t.value i) n
  finite_value i := by
    let := t.finite_value i
    let := AddCommGrpCat.finite_zmodQuotient (t.value i) n
    exact Module.Finite.of_finite
  trivialization i := by
    let U := moduleUnderlying (ZMod n) (t.chart i).left
    letI : (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).Full :=
      ModuleCat.forget₂_full_of_surjective_intCast (ZMod n) ZMod.intCast_surjective
    have hz (M : ModuleCat.{u + 1} (ZMod n)) (x : M) : n • x = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod n), ZMod.natCast_self, zero_smul]
    have hF : n • 𝟙 ((moduleUnderlying (ZMod n) X).obj F) = 0 := by
      apply ObjectProperty.hom_ext
      ext V x
      exact hz (F.obj.obj V) x
    have hpull := killedBy_pullback (t.chart i).hom hF
    have hvalue : n • 𝟙 ((constantSheaf (t.chart i).left.smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj (t.value i)) = 0 := by
      apply (cancel_epi (t.trivialization i).hom).mp
      rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
      calc
        n • (t.trivialization i).hom =
            (n • 𝟙 _) ≫ (t.trivialization i).hom := by
          rw [Preadditive.nsmul_comp, Category.id_comp]
        _ = 0 := by rw [hpull, zero_comp]
    exact U.preimageIso
      ((moduleInverseImageUnderlyingIso (ZMod n) (t.chart i).hom).app F ≪≫
        t.trivialization i ≪≫
        (constantZModQuotientUnderlyingIso (t.chart i).left n (t.value i) hvalue).symm)

/-- For every modulus, original finite abelian local constancy of genuine
ZMod coefficients implies finite-type module local constancy. -/
theorem isFiniteTypeLocallyConstant_of_zmodUnderlying {X : Scheme.{u}} (n : ℕ)
    {F : ModuleSheaf (ZMod n) X}
    (hF : IsFiniteLocallyConstant ((moduleUnderlying (ZMod n) X).obj F)) :
    IsFiniteTypeLocallyConstant F := by
  obtain ⟨t⟩ := hF
  exact ⟨finiteTypeLocalTrivializationOfZMod n F t⟩

/-- At positive modulus the genuine module predicate agrees with the
original finite-abelian local-constancy predicate. -/
theorem isFiniteTypeLocallyConstant_zmod_iff {X : Scheme.{u}} (n : ℕ) (hn : 0 < n)
    (F : ModuleSheaf (ZMod n) X) :
    IsFiniteTypeLocallyConstant F ↔
      IsFiniteLocallyConstant ((moduleUnderlying (ZMod n) X).obj F) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact ⟨isFiniteLocallyConstant_underlying, isFiniteTypeLocallyConstant_of_zmodUnderlying n⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
