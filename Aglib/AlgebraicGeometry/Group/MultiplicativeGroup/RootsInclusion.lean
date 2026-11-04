/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicativeBaseChange

/-! The original roots-of-unity inclusion as a morphism of the original groups. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.MultiplicativeGroup

attribute [local instance] Over.cartesianMonoidalCategory

/-- The original equalizer inclusion as a morphism of the original groups. -/
def rootsInclusionHom (X : Scheme.{u}) (n : ℕ) :
    rootsGroupScheme X n ⟶ groupScheme X := by
  let R := rootsGroupScheme X n
  let M := groupScheme X
  let i : R.X ⟶ M.X := rootsInclusion X n
  let test (U : Over X) := MultiplicativeBaseChange.unitsSectionsEquiv X U
  let root (U : Over X) := MultiplicativeBaseChange.rootsSectionsEquiv X n U
  have hcoord (U : Over X) (a : U ⟶ R.X) : test U (a ≫ i) = (root U a).val := rfl
  have h₁ (U : Over X) : (1 : U ⟶ R.X) ≫ i = (1 : U ⟶ M.X) := by
    apply (test U).injective
    rw [hcoord, map_one, map_one]
    rfl
  have h₂ (U : Over X) (a b : U ⟶ R.X) :
      (a * b) ≫ i = (a ≫ i) * (b ≫ i) := by
    apply (test U).injective
    rw [hcoord, (root U).map_mul, (test U).map_mul, hcoord, hcoord]
    rfl
  refine Grp.homMk'' i ?_ ?_
  · simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h₁ (𝟙_ (Over X))
  · have h := h₂ (R.X ⊗ R.X) (fst R.X R.X) (snd R.X R.X)
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    exact h.trans (congrArg (fun f => f ≫ μ[M.X])
      (lift_fst_comp_snd_comp i i))

@[simp] theorem rootsInclusionHom_hom_hom (X : Scheme.{u}) (n : ℕ) :
    (rootsInclusionHom X n).hom.hom = rootsInclusion X n := rfl

/-- A map into the original roots group respects the group laws whenever its
composite into the multiplicative group does. -/
theorem isMonHom_of_rootsInclusion_comp {X : Scheme.{u}} {H : Grp (Over X)}
    {n : ℕ} (c : H.X ⟶ (rootsGroupScheme X n).X)
    [IsMonHom (c ≫ (rootsInclusionHom X n).hom.hom)] : IsMonHom c := by
  let i := (rootsInclusionHom X n).hom.hom
  have hi : Mono i := by
    unfold i
    rw [rootsInclusionHom_hom_hom]
    exact inferInstanceAs (Mono (equalizer.ι (powerMap X n) (oneMap X)))
  constructor
  · apply (cancel_mono i).mp
    simp only [Category.assoc, IsMonHom.one_hom]
  · apply (cancel_mono i).mp
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

/-- The original roots inclusion commutes with the actual root and unit base changes. -/
theorem rootsInclusionHom_baseChange {X S : Scheme.{u}} (b : S ⟶ X) (n : ℕ) :
    (MultiplicativeBaseChange.rootsBaseChangeIso b n).hom ≫ rootsInclusionHom S n =
      (Over.pullback b).mapGrp.map (rootsInclusionHom X n) ≫
        (MultiplicativeBaseChange.unitsBaseChangeIso b).hom := by
  let F := Over.pullback b
  let r := (MultiplicativeBaseChange.rootsBaseChangeIso b n).hom.hom.hom
  let g := (MultiplicativeBaseChange.unitsBaseChangeIso b).hom.hom.hom
  apply Grp.hom_ext
  apply MultiplicativeBaseChange.unitsCoordinate_ext
  change (r ≫ (rootsInclusionHom S n).hom.hom).left ≫ prod.snd =
    (F.map (rootsInclusionHom X n).hom.hom ≫ g).left ≫ prod.snd
  rw [rootsInclusionHom_hom_hom, rootsInclusionHom_hom_hom]
  change r.left ≫ MultiplicativeBaseChange.rootCoordinate S n =
    (F.map (rootsInclusion X n)).left ≫ g.left ≫ prod.snd
  have hr := MultiplicativeBaseChange.rootsBaseChangeIso_coordinate b n
  have hg := MultiplicativeBaseChange.unitsBaseChangeIso_coordinate b
  change r.left ≫ MultiplicativeBaseChange.rootCoordinate S n = _ at hr
  change g.left ≫ prod.snd = _ at hg
  let l := (F.map (rootsInclusion X n)).left
  have h₁ : l ≫ pullback.fst (scheme X).hom b =
      pullback.fst (rootsScheme X n).hom b ≫ (rootsInclusion X n).left := by
    unfold l F
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have h₂ : pullback.fst (rootsScheme X n).hom b ≫
      MultiplicativeBaseChange.rootCoordinate X n =
      l ≫ pullback.fst (scheme X).hom b ≫ prod.snd := by
    unfold MultiplicativeBaseChange.rootCoordinate
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ prod.snd) h₁.symm).trans (Category.assoc _ _ _))
  have h₃ : l ≫ (pullback.fst (scheme X).hom b ≫ prod.snd) =
      l ≫ (g.left ≫ prod.snd) :=
    congrArg (fun f : (F.obj (scheme X)).left ⟶ affineScheme => l ≫ f) hg.symm
  exact hr.trans (h₂.trans h₃)

end AlgebraicGeometry.Scheme.Group.MultiplicativeGroup
