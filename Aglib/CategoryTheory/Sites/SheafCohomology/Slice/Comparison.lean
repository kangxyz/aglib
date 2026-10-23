/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Restriction
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.FreeRepresentable
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.ExtComparison

/-!
# Original slice cohomology comparison

Exact lower shriek and restriction identify represented-object Ext with the
original `Sheaf.H` on the slice. The comparison retains the actual source
isomorphism and adjunction unit, not just abstract group isomorphism types.
-/

@[expose] public noncomputable section

universe w₁ w₂ t v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.SliceCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [HasSheafify (J.over U) AddCommGrpCat.{max v t}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{max v t})]
  [HasExt.{w₂} (Sheaf (J.over U) AddCommGrpCat.{max v t})]

/-- Large represented-object cohomology equals original cohomology on the slice. -/
def sliceComparison (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    LargeCohomology.H J F n U ≃+ Sheaf.H (F.over U) n :=
  (lowerShriekAdjunction J AddCommGrpCat.{max v t} U).sourceExtComparison
    (lowerShriekIntegersIso J U) F n

/-- The original adjunction unit, followed by the restriction of the source comparison. -/
def sliceComparisonUnit :
    sliceIntegers J U ⟶ (Hypercohomology.freeAbelianSheaf.{t} J U).over U :=
  (lowerShriekAdjunction J AddCommGrpCat.{max v t} U).unit.app (sliceIntegers J U) ≫
    (J.overPullback AddCommGrpCat.{max v t} U).map (lowerShriekIntegersIso J U).hom

/-- Formula for the actual forward comparison, including the original restriction map. -/
theorem sliceComparison_apply (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (x : LargeCohomology.H J F n U) :
    sliceComparison J U F n x =
      (Ext.mk₀ (sliceComparisonUnit J U)).comp
        (x.mapExactFunctor (J.overPullback AddCommGrpCat.{max v t} U)) (Nat.zero_add n) := by
  change Ext.{w₁} (Hypercohomology.freeAbelianSheaf.{t} J U) F n at x
  exact (lowerShriekAdjunction J AddCommGrpCat.{max v t} U).sourceExtComparison_apply
    (lowerShriekIntegersIso J U) F n x

/-- The comparison is natural in coefficients for the original cohomology maps. -/
theorem sliceComparison_naturality {F G : Sheaf J AddCommGrpCat.{max v t}}
    (g : F ⟶ G) (n : ℕ) (x : LargeCohomology.H J F n U) :
    sliceComparison J U G n (((LargeCohomology.presheafFunctor J n).map g).app (op U) x) =
      Sheaf.H.map ((J.overPullback AddCommGrpCat.{max v t} U).map g) n
        (sliceComparison J U F n x) := by
  change Ext.{w₁} (Hypercohomology.freeAbelianSheaf.{t} J U) F n at x
  exact (lowerShriekAdjunction J AddCommGrpCat.{max v t} U).sourceExtComparison_naturality
    (lowerShriekIntegersIso J U) g n x

/-- In degree zero the forward map is the original Hom adjunction. -/
theorem sliceComparison_mk₀ (F : Sheaf J AddCommGrpCat.{max v t})
    (a : Hypercohomology.freeAbelianSheaf.{t} J U ⟶ F) :
    sliceComparison J U F 0 (Ext.mk₀ a) =
      Ext.mk₀ ((lowerShriekAdjunction J AddCommGrpCat.{max v t} U).homEquiv _ _
        ((lowerShriekIntegersIso J U).hom ≫ a)) := by
  exact (lowerShriekAdjunction J AddCommGrpCat.{max v t} U).sourceExtComparison_mk₀
    (lowerShriekIntegersIso J U) F a

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{max v t})]
  [HasExt.{w₂} (Sheaf (J.over U) AddCommGrpCat.{max v t})] in
/-- The comparison unit corresponds to the actual identity generator under evaluation. -/
theorem sliceComparisonUnit_generator :
    (((constantSheafAdj (J.over U) AddCommGrpCat.{max v t} Over.mkIdTerminal).homAddEquiv
      (AddCommGrpCat.of (ULift.{max v t} ℤ))
      ((Hypercohomology.freeAbelianSheaf.{t} J U).over U)).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)) (sliceComparisonUnit J U) =
      Hypercohomology.sectionsAddEquiv J U _ (𝟙 _) := by
  change lowerShriekSectionsAddEquiv J U _ (lowerShriekIntegersIso J U).hom = _
  rw [lowerShriekIntegersIso_hom, AddEquiv.apply_symm_apply]

/-- Degree zero is normalized by evaluation at the original terminal slice object. -/
theorem sliceComparison_equiv₀ (F : Sheaf J AddCommGrpCat.{max v t})
    (x : LargeCohomology.H J F 0 U) :
    Sheaf.H.equiv₀ (F.over U) Over.mkIdTerminal (sliceComparison J U F 0 x) =
      Hypercohomology.sectionsAddEquiv J U F (Ext.addEquiv₀ x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  rw [sliceComparison_mk₀]
  have h₀ {A B : Sheaf J AddCommGrpCat.{max v t}} (a : A ⟶ B) :
      Ext.addEquiv₀ (Ext.mk₀ a) = a := Ext.addEquiv₀.apply_symm_apply a
  have h₁ {A B : Sheaf (J.over U) AddCommGrpCat.{max v t}} (a : A ⟶ B) :
      Ext.addEquiv₀ (Ext.mk₀ a) = a := Ext.addEquiv₀.apply_symm_apply a
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, h₀, h₁]
  exact lowerShriekIntegersIso_evaluation J U F a

end CategoryTheory.Sheaf.SliceCohomology

namespace CategoryTheory.Sheaf.SliceCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})]
  [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{v})]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{w₂} (Sheaf (J.over U) AddCommGrpCat.{v})]

/-- At ordinary coefficient size the source is literally Mathlib's original H'. -/
def ordinarySliceComparison (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    F.H' n U ≃+ Sheaf.H (F.over U) n := by
  let e := ((LargeCohomology.ordinaryComparison J n).app F).app (op U)
  exact e.symm.addCommGroupIsoToAddEquiv.trans (sliceComparison J U F n)

end CategoryTheory.Sheaf.SliceCohomology
