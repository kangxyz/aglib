/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Points
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Torsion abelian sheaves and exact sequences

The internal torsion predicate uses local annihilators on the actual underlying
presheaf. It passes to subobjects and quotients. A small conservative family
of original points proves closure under extensions through the exact native
point-fibre functors.
-/

@[expose] public noncomputable section

open Opposite CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Internal torsion of an abelian sheaf, allowing different local annihilators. -/
def IsTorsion (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  Presheaf.IsLocallyTorsion J F.obj

variable [HasSheafify J AddCommGrpCat.{w}]

/-- A genuine subobject of a torsion abelian sheaf is torsion. -/
theorem IsTorsion.of_mono {F G : Sheaf J AddCommGrpCat.{w}} (hG : IsTorsion G)
    (φ : F ⟶ G) [Mono φ] : IsTorsion F := by
  apply Presheaf.IsLocallyTorsion.of_injective hG φ.hom
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- A genuine quotient of a torsion abelian sheaf is torsion. -/
theorem IsTorsion.of_epi [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (hF : IsTorsion F)
    (φ : F ⟶ G) [Epi φ] : IsTorsion G := by
  have : Presheaf.IsLocallySurjective J φ.hom :=
    (isLocallySurjective_iff_epi' AddCommGrpCat.{w} φ).mpr inferInstance
  exact hF.of_isLocallySurjective φ.hom

omit [HasSheafify J AddCommGrpCat.{w}] in
/-- Every original point fibre of an internally torsion sheaf is torsion. -/
theorem IsTorsion.isAddTorsion_fiber [LocallySmall.{w} C]
    {F : Sheaf J AddCommGrpCat.{w}} (hF : IsTorsion F)
    (Φ : GrothendieckTopology.Point.{w} J) :
    IsAddTorsion ((Φ.sheafFiber (A := AddCommGrpCat.{w})).obj F) :=
  Presheaf.IsLocallyTorsion.isAddTorsion_fiber hF Φ

private theorem torsion_middle_of_exact (S : ShortComplex AddCommGrpCat.{w})
    (hS : S.Exact) (h₁ : IsAddTorsion S.X₁) (h₃ : IsAddTorsion S.X₃) :
    IsAddTorsion S.X₂ := by
  intro x
  obtain ⟨n, hn, hnx⟩ := (h₃ (S.g x)).exists_nsmul_eq_zero
  have hzero : S.g (n • x) = 0 := by simpa only [map_nsmul] using hnx
  obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff S).mp hS (n • x) hzero
  obtain ⟨m, hm, hma⟩ := (h₁ a).exists_nsmul_eq_zero
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [mul_nsmul, ← ha, ← map_nsmul, hma, map_zero]

/-- In a short exact sequence, internally torsion endpoints imply a torsion middle sheaf. -/
theorem IsTorsion.extension [LocallySmall.{w} C]
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (P : ObjectProperty (GrothendieckTopology.Point.{w} J))
    [ObjectProperty.Small.{w} P] (hP : P.IsConservativeFamilyOfPoints)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    (h₁ : IsTorsion S.X₁) (h₃ : IsTorsion S.X₃) : IsTorsion S.X₂ := by
  apply Presheaf.isLocallyTorsion_of_isAddTorsion_fibers P hP
  intro Φ
  let T := S.map (Φ.obj.sheafFiber (A := AddCommGrpCat.{w}))
  have hT : T.ShortExact := hS.map_of_exact _
  exact torsion_middle_of_exact T hT.exact (h₁.isAddTorsion_fiber Φ.obj)
    (h₃.isAddTorsion_fiber Φ.obj)

end CategoryTheory.Sheaf
