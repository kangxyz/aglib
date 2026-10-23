/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.Algebra.Category.CommAlgCat.Monoidal

/-!
# The original algebraic Amitsur conerve

The object is the native Čech conerve of the original algebra unit `R → S`
in `CommAlgCat R`. Its actual wide-pushout inclusions determine its maps.
The degree-zero comparison is the original copy of `S`; the successor
comparison splits off the original first tensor factor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

namespace Algebra.Amitsur

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The original algebra-unit arrow. -/
def unitArrow : Arrow (CommAlgCat.{u} R) :=
  Arrow.mk (CommAlgCat.ofHom (Algebra.ofId R S))

/-- The native Čech conerve of the original algebra-unit arrow. -/
abbrev conerve : CosimplicialObject (CommAlgCat.{u} R) := (unitArrow R S).cechConerve

/-- The original finite tensor coproduct in degree `n`. -/
abbrev term (n : ℕ) : CommAlgCat.{u} R := (conerve R S).obj ⦋n⦌

/-- An original copy of `S` in the native wide tensor pushout. -/
abbrev ι (n : ℕ) (i : Fin (n + 1)) : CommAlgCat.of R S ⟶ term R S n :=
  WidePushout.ι (fun _ : Fin (n + 1) => (unitArrow R S).hom) i

/-- The original base-ring augmentation component. -/
abbrev augmentation (n : ℕ) : CommAlgCat.of R R ⟶ term R S n :=
  WidePushout.head (fun _ : Fin (n + 1) => (unitArrow R S).hom)

/-- Maps out of the native term are determined by the original tensor factors. -/
@[ext]
theorem term_hom_ext (n : ℕ) {A : CommAlgCat.{u} R} (f g : term R S n ⟶ A)
    (h : ∀ i, ι R S n i ≫ f = ι R S n i ≫ g) : f = g := by
  apply WidePushout.hom_ext (fun _ : Fin (n + 1) => (unitArrow R S).hom) f g h
  exact CommAlgCat.isInitialSelf.hom_ext _ _

/-- Every original conerve map preserves the same original indexed factor. -/
@[reassoc]
theorem ι_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    ι R S m i ≫ (conerve R S).map f = ι R S n (f.toOrderHom i) :=
  WidePushout.ι_desc _ _ _ _ _

/-- An original coface inserts the omitted tensor position. -/
@[reassoc (attr := simp)]
theorem ι_δ (n : ℕ) (j : Fin (n + 2)) (i : Fin (n + 1)) :
    ι R S n i ≫ (conerve R S).δ j = ι R S (n + 1) (j.succAbove i) :=
  ι_map R S (SimplexCategory.δ j) i

@[reassoc]
theorem ι_δ_zero (n : ℕ) (i : Fin (n + 1)) :
    ι R S n i ≫ (conerve R S).δ 0 = ι R S (n + 1) i.succ := by
  simpa only [Fin.succAbove_zero] using ι_δ R S n 0 i

/-- The original degree-zero tensor coproduct maps to the same original algebra `S`. -/
def zeroTo : term R S 0 ⟶ CommAlgCat.of R S :=
  WidePushout.desc (CommAlgCat.ofHom (Algebra.ofId R S)) (fun _ => 𝟙 _)
    (fun _ => Category.comp_id _)

@[reassoc (attr := simp)]
theorem ι_zeroTo (i : Fin 1) : ι R S 0 i ≫ zeroTo R S = 𝟙 _ :=
  WidePushout.ι_desc _ _ _ _ _

/-- The actual degree-zero component is canonically the original `S`. -/
def zeroIso : term R S 0 ≅ CommAlgCat.of R S where
  hom := zeroTo R S
  inv := ι R S 0 0
  hom_inv_id := by
    apply term_hom_ext
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp
  inv_hom_id := ι_zeroTo R S 0

/-- The original first factor and remaining factors in the tensor successor model. -/
def successorFactor (n : ℕ) : Fin (n + 2) →
    (CommAlgCat.of R S ⟶ CommAlgCat.of R (S ⊗[R] term R S n)) :=
  Fin.cases (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft)
    (fun i => ι R S n i ≫ CommAlgCat.ofHom Algebra.TensorProduct.includeRight)

/-- The canonical map to the tensor product splitting off the original first factor. -/
def successorToTensor (n : ℕ) :
    term R S (n + 1) ⟶ CommAlgCat.of R (S ⊗[R] term R S n) :=
  WidePushout.desc (CommAlgCat.ofHom (Algebra.ofId R _)) (successorFactor R S n)
    (fun _ => CommAlgCat.isInitialSelf.hom_ext _ _)

@[reassoc (attr := simp)]
theorem ι_successorToTensor (n : ℕ) (i : Fin (n + 2)) :
    ι R S (n + 1) i ≫ successorToTensor R S n = successorFactor R S n i :=
  WidePushout.ι_desc _ _ _ _ _

@[reassoc (attr := simp)]
theorem δ_zero_successorToTensor (n : ℕ) :
    (conerve R S).δ 0 ≫ successorToTensor R S n =
      CommAlgCat.ofHom Algebra.TensorProduct.includeRight := by
  apply term_hom_ext
  intro i
  rw [ι_δ_zero_assoc, ι_successorToTensor]
  rfl

/-- The inverse map multiplies the original first factor with the original
zero coface on the remaining factors. -/
def tensorToSuccessor (n : ℕ) :
    CommAlgCat.of R (S ⊗[R] term R S n) ⟶ term R S (n + 1) :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift (ι R S (n + 1) 0).hom
    ((conerve R S).δ 0).hom (fun _ _ => Commute.all _ _))

@[reassoc (attr := simp)]
theorem includeLeft_tensorToSuccessor (n : ℕ) :
    CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫ tensorToSuccessor R S n =
      ι R S (n + 1) 0 := by
  apply CommAlgCat.hom_ext
  exact Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

@[reassoc (attr := simp)]
theorem includeRight_tensorToSuccessor (n : ℕ) :
    CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫ tensorToSuccessor R S n =
      (conerve R S).δ 0 := by
  apply CommAlgCat.hom_ext
  exact Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

/-- Every native successor term is the original tensor product of its first
`S` factor and its original preceding term. -/
def successorTensorIso (n : ℕ) :
    term R S (n + 1) ≅ CommAlgCat.of R (S ⊗[R] term R S n) where
  hom := successorToTensor R S n
  inv := tensorToSuccessor R S n
  hom_inv_id := by
    apply term_hom_ext
    intro i
    rw [ι_successorToTensor_assoc, Category.comp_id]
    cases i using Fin.cases with
    | zero => exact includeLeft_tensorToSuccessor R S n
    | succ i =>
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun f => ι R S n i ≫ f) (includeRight_tensorToSuccessor R S n)).trans
            (ι_δ_zero R S n i))
  inv_hom_id := by
    apply CommAlgCat.hom_ext
    apply Algebra.TensorProduct.ext
    · change (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫
        tensorToSuccessor R S n ≫ successorToTensor R S n).hom = _
      rw [includeLeft_tensorToSuccessor_assoc, ι_successorToTensor]
      rfl
    · change (CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫
        tensorToSuccessor R S n ≫ successorToTensor R S n).hom = _
      rw [includeRight_tensorToSuccessor_assoc, δ_zero_successorToTensor]
      rfl

end Algebra.Amitsur
