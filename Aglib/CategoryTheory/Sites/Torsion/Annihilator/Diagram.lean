/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Nat.Factorial.Basic

/-! # The positive factorial diagram of native annihilator subsheaves -/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]

/-- The native natural-number diagram with positive stage `F[(n+1)!]`. -/
def factorialAnnihilatorDiagram (F : Sheaf J AddCommGrpCat.{w}) :
    ℕ ⥤ Sheaf J AddCommGrpCat.{w} where
  obj n := annihilator F (n + 1).factorial
  map h := annihilatorMap F
    (Nat.factorial_dvd_factorial (Nat.add_le_add_right (leOfHom h) 1))
  map_id n := annihilatorMap_refl F (n + 1).factorial
  map_comp h h' := (annihilatorMap_comp F
    (Nat.factorial_dvd_factorial (Nat.add_le_add_right (leOfHom h) 1))
    (Nat.factorial_dvd_factorial (Nat.add_le_add_right (leOfHom h') 1))).symm

/-- Every original diagram arrow factors the actual inclusion into the original sheaf. -/
@[simp, reassoc]
theorem factorialAnnihilatorDiagram_map_ι (F : Sheaf J AddCommGrpCat.{w})
    {n m : ℕ} (h : n ⟶ m) :
    (factorialAnnihilatorDiagram F).map h ≫ annihilatorι F (m + 1).factorial =
      annihilatorι F (n + 1).factorial :=
  annihilatorMap_ι F
    (Nat.factorial_dvd_factorial (Nat.add_le_add_right (leOfHom h) 1))

/-- All transition maps in the factorial annihilator diagram are monomorphisms. -/
instance factorialAnnihilatorDiagram_map_mono (F : Sheaf J AddCommGrpCat.{w})
    {n m : ℕ} (h : n ⟶ m) : Mono ((factorialAnnihilatorDiagram F).map h) :=
  annihilatorMap_mono F
    (Nat.factorial_dvd_factorial (Nat.add_le_add_right (leOfHom h) 1))

/-- The original kernel inclusions form a cocone into the original coefficient sheaf. -/
def factorialAnnihilatorCocone (F : Sheaf J AddCommGrpCat.{w}) :
    Cocone (factorialAnnihilatorDiagram F) where
  pt := F
  ι :=
    { app n := annihilatorι F (n + 1).factorial
      naturality := by
        intro n m h
        change (factorialAnnihilatorDiagram F).map h ≫
            annihilatorι F (m + 1).factorial =
          annihilatorι F (n + 1).factorial ≫ 𝟙 F
        exact (factorialAnnihilatorDiagram_map_ι F h).trans
          (Category.comp_id (annihilatorι F (n + 1).factorial)).symm }

/-- Each cocone component is literally the original native kernel inclusion. -/
@[simp]
theorem factorialAnnihilatorCocone_ι_app (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    (factorialAnnihilatorCocone F).ι.app n = annihilatorι F (n + 1).factorial := rfl

/-- Every stage has a positive annihilator. -/
theorem factorialAnnihilatorDiagram_exponent_pos (n : ℕ) : 0 < (n + 1).factorial :=
  Nat.factorial_pos _

/-- The positive factorial exponents are cofinal for divisibility among positive integers. -/
theorem exists_dvd_factorialAnnihilatorExponent (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, n ∣ (k + 1).factorial :=
  ⟨n, Nat.dvd_factorial hn (Nat.le_succ n)⟩

/-- The factorial exponent annihilates the actual native stage. -/
@[simp]
theorem factorialAnnihilatorDiagram_annihilated (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    (n + 1).factorial • 𝟙 ((factorialAnnihilatorDiagram F).obj n) = 0 :=
  nsmul_id_annihilator F _

/-- The original factorial cocone inclusion is annihilated by its positive exponent. -/
theorem factorialAnnihilatorCocone_annihilated (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    (n + 1).factorial • (factorialAnnihilatorCocone F).ι.app n = 0 :=
  nsmul_annihilatorι F _

/-- An actual coefficient map induces a natural map of the factorial annihilator diagrams. -/
def factorialAnnihilatorCoefficientMap {F G : Sheaf J AddCommGrpCat.{w}} (q : F ⟶ G) :
    factorialAnnihilatorDiagram F ⟶ factorialAnnihilatorDiagram G where
  app n := annihilatorCoefficientMap q (n + 1).factorial
  naturality := by
    intro n m h
    exact annihilatorMap_coefficient_naturality q
      (Nat.factorial_dvd_factorial (Nat.add_le_add_right (leOfHom h) 1))

/-- The coefficient-induced diagram map retains the original cocone and coefficient map. -/
@[reassoc]
theorem factorialAnnihilatorCoefficientMap_ι {F G : Sheaf J AddCommGrpCat.{w}}
    (q : F ⟶ G) (n : ℕ) :
    (factorialAnnihilatorCoefficientMap q).app n ≫
        (factorialAnnihilatorCocone G).ι.app n =
      (factorialAnnihilatorCocone F).ι.app n ≫ q :=
  annihilatorCoefficientMap_ι q _

end CategoryTheory.Sheaf
