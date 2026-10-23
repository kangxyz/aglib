/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.FiniteCoproductPowers
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The canonical comparison from a coproduct cover to a family

The comparison restricts along the actual maps from each tuple intersection to
the corresponding power of the coproduct. All simplex maps, and consequently
all alternating differential signs, are retained. Its invertibility separates
the geometric coproduct-distribution map from preservation of section products.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Cech

universe c h a b w

variable {C : Type c} [Category.{h} C] [HasFiniteProducts C]
  [HasFiniteCoproducts C] {ι : Type w} [Finite ι] (U : ι → C)

/-- The actual component inclusion from an intersection into a power of the
coproduct. -/
def tupleCoproductInclusion {α : Type} [Finite α] (s : α → ι) :
    (∏ᶜ fun k => U (s k)) ⟶ ∏ᶜ fun _ : α => ∐ U :=
  Limits.Pi.map fun k => Sigma.ι U (s k)

@[reassoc (attr := simp)]
lemma tupleCoproductInclusion_π {α : Type} [Finite α] (s : α → ι) (k : α) :
    tupleCoproductInclusion U s ≫ Pi.π _ k =
      Pi.π (fun k => U (s k)) k ≫ Sigma.ι U (s k) := by
  simp [tupleCoproductInclusion]

/-- Compatibility with every coordinate map, not only the cofaces. -/
lemma tupleCoproductInclusion_naturality {α β : Type} [Finite α] [Finite β]
    (s : β → ι) (f : α → β) :
    (Pi.lift fun k => Pi.π (fun k => U (s k)) (f k)) ≫
        tupleCoproductInclusion U (s ∘ f) =
      tupleCoproductInclusion U s ≫
        (Pi.lift fun k => Pi.π (fun _ : β => ∐ U) (f k)) := by
  apply Pi.hom_ext
  intro k
  simp

/-- The canonical geometric distribution morphism. Its invertibility is a
property of the category and family, independent of coefficients or cohomology. -/
def coproductPowerComparison (α : Type) [Finite α] :
    (∐ fun s : α → ι => ∏ᶜ fun k => U (s k)) ⟶ ∏ᶜ fun _ : α => ∐ U :=
  Sigma.desc (tupleCoproductInclusion U)

@[reassoc (attr := simp)]
lemma ι_coproductPowerComparison (α : Type) [Finite α] (s : α → ι) :
    Sigma.ι _ s ≫ coproductPowerComparison U α = tupleCoproductInclusion U s := by
  simp [coproductPowerComparison]

/-- Finite pre-extensivity supplies the geometric premise for the canonical
cover comparison, including the empty family and empty power. -/
instance coproductPowerComparison_isIso [HasPullbacks C] [FinitaryPreExtensive C] (n : ℕ) :
    IsIso (coproductPowerComparison U (Fin n)) :=
  inferInstanceAs (IsIso (Sigma.desc (fun s : Fin n → ι =>
    Limits.Pi.map (fun k => Sigma.ι U (s k)))))

variable {A : Type a} [Category.{b} A] [HasProducts.{w} A]
  (P : Cᵒᵖ ⥤ A)

/-- Restrict sections on the coproduct nerve to every original tuple component. -/
def coproductCechComparison :
    (cechNerveTerminalFrom (∐ U)).rightOp ⋙ P ⟶
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P where
  app n := Pi.lift fun s => P.map (tupleCoproductInclusion U s).op
  naturality {n m} g := by
    apply Pi.hom_ext
    intro s
    dsimp [FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
      FormalCoproduct.cech, FormalCoproduct.mapPower, cechNerveTerminalFrom]
    simp only [Category.assoc]
    erw [Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun f => P.map f.op)
      (tupleCoproductInclusion_naturality U s g.toOrderHom).symm

@[reassoc (attr := simp)]
lemma coproductCechComparison_app_π (n : SimplexCategory) (s : Fin (n.len + 1) → ι) :
    (coproductCechComparison U P).app n ≫
      Pi.π (fun i : ((FormalCoproduct.mk ι U).power (ToType n)).I =>
        P.obj (op (((FormalCoproduct.mk ι U).power (ToType n)).obj i))) s =
      P.map (tupleCoproductInclusion U s).op := by
  simp [coproductCechComparison]

variable [PreservesFiniteProducts P]

/-- The literal component comparison is invertible once the geometric
finite-coproduct distribution map is invertible. -/
lemma isIso_coproductCechComparison_app (n : SimplexCategory)
    [IsIso (coproductPowerComparison U (Fin (n.len + 1)))] :
    IsIso ((coproductCechComparison U P).app n) := by
  let V := fun s : Fin (n.len + 1) → ι => ∏ᶜ fun k => U (s k)
  let e := P.mapIso (asIso (coproductPowerComparison U (Fin (n.len + 1)))).op ≪≫
    P.mapIso (opCoproductIsoProduct V) ≪≫
    PreservesProduct.iso P (fun s => op (V s))
  have he : (coproductCechComparison U P).app n = e.hom := by
    apply Pi.hom_ext
    intro s
    dsimp [e]
    erw [coproductCechComparison_app_π, Category.assoc, Category.assoc,
      piComparison_comp_π]
    rw [← P.map_comp, opCoproductIsoProduct_hom_comp_π, ← P.map_comp, ← op_comp]
    rw [ι_coproductPowerComparison]
  rw [he]
  infer_instance

/-- The canonical comparison of all cosimplicial operators. -/
def coproductCechIso
    [∀ n : ℕ, IsIso (coproductPowerComparison U (Fin (n + 1)))] :
    (cechNerveTerminalFrom (∐ U)).rightOp ⋙ P ≅
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P := by
  letI : ∀ n : SimplexCategory, IsIso ((coproductCechComparison U P).app n) :=
    fun n => isIso_coproductCechComparison_app U P n
  letI : IsIso (coproductCechComparison U P) := NatIso.isIso_of_isIso_app _
  exact asIso (coproductCechComparison U P)

variable [Preadditive A]

/-- The alternating complex comparison uses the original coface functor. -/
def coproductCechComplexIso
    [∀ n : ℕ, IsIso (coproductPowerComparison U (Fin (n + 1)))] :
    (AlgebraicTopology.alternatingCofaceMapComplex A).obj
        ((cechNerveTerminalFrom (∐ U)).rightOp ⋙ P) ≅ (cechComplexFunctor U).obj P :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso (coproductCechIso U P)

end CategoryTheory.Cech
