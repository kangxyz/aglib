/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Conerve
public import Aglib.Algebra.Homology.Amitsur.Opposite
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Native contraction after adding the original scalar algebra

Adding the original leading `S` factor makes the original Amitsur conerve
split. The contraction multiplies that factor with the original first
factor of the native tensor coproduct. Its opposite is an actual native
`ExtraDegeneracy`, before applying any coefficient-module functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial TensorProduct

namespace Algebra.Amitsur

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Add the original leading scalar-algebra factor, using the native tensor functor. -/
def scalarTensor : CommAlgCat.{u} R ⥤ CommAlgCat.{u} R where
  obj A := CommAlgCat.of R (S ⊗[R] A)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R S) f.hom)
  map_id A := by apply CommAlgCat.hom_ext; ext x <;> rfl
  map_comp f g := by apply CommAlgCat.hom_ext; ext x <;> rfl

/-- This is the native tensor functor, with its original objects and maps displayed. -/
theorem scalarTensor_eq_native :
    scalarTensor R S = MonoidalCategory.tensorLeft (CommAlgCat.of R S) := rfl

@[simp, reassoc (attr := simp)]
theorem includeLeft_scalarTensor {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫ (scalarTensor R S).map f =
      CommAlgCat.ofHom Algebra.TensorProduct.includeLeft := by
  apply CommAlgCat.hom_ext
  ext s
  change s ⊗ₜ[R] f.hom 1 = s ⊗ₜ[R] (1 : B)
  rw [map_one]

@[simp, reassoc (attr := simp)]
theorem includeRight_scalarTensor {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫ (scalarTensor R S).map f =
      f ≫ CommAlgCat.ofHom Algebra.TensorProduct.includeRight := by
  apply CommAlgCat.hom_ext
  ext a
  rfl

/-- The original scalar-extended augmented conerve, with its original leading `S`. -/
def scalarAugmented : CosimplicialObject.Augmented (CommAlgCat.{u} R) where
  left := CommAlgCat.of R S
  right := conerve R S ⋙ scalarTensor R S
  hom := {
    app _ := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
    naturality := by
      intro i j f
      change 𝟙 _ ≫ CommAlgCat.ofHom Algebra.TensorProduct.includeLeft =
        CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫
          (scalarTensor R S).map ((conerve R S).map f)
      rw [Category.id_comp, includeLeft_scalarTensor] }

/-- The original scalar-extended term, typed as its original tensor product. -/
abbrev scalarTerm (n : ℕ) : CommAlgCat.{u} R := CommAlgCat.of R (S ⊗[R] term R S n)

theorem scalarTerm_hom_ext (n : ℕ) {A : CommAlgCat.{u} R}
    (f g : scalarTerm R S n ⟶ A)
    (hleft : CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫ f =
      CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫ g)
    (hright : CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫ f =
      CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫ g) : f = g := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext
  · exact congrArg CommAlgCat.Hom.hom hleft
  · exact congrArg CommAlgCat.Hom.hom hright

/-- The original degree-zero retraction multiplies the original two `S` factors. -/
def scalarRetraction : scalarTerm R S 0 ⟶ CommAlgCat.of R S :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift (AlgHom.id R S) (zeroTo R S).hom
    (fun _ _ => Commute.all _ _))

/-- The original contraction consumes the first original factor into the leading scalar factor. -/
def scalarContraction (n : ℕ) : scalarTerm R S (n + 1) ⟶ scalarTerm R S n :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (successorToTensor R S n).hom (fun _ _ => Commute.all _ _))

@[simp, reassoc (attr := simp)]
theorem includeLeft_scalarRetraction :
    CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫ scalarRetraction R S = 𝟙 _ := by
  apply CommAlgCat.hom_ext
  exact Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

@[simp, reassoc (attr := simp)]
theorem includeRight_scalarRetraction :
    CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫ scalarRetraction R S = zeroTo R S := by
  apply CommAlgCat.hom_ext
  exact Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

@[simp, reassoc (attr := simp)]
theorem includeLeft_scalarContraction (n : ℕ) :
    CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫ scalarContraction R S n =
      CommAlgCat.ofHom Algebra.TensorProduct.includeLeft := by
  apply CommAlgCat.hom_ext
  exact Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

@[simp, reassoc (attr := simp)]
theorem includeRight_scalarContraction (n : ℕ) :
    CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫ scalarContraction R S n =
      successorToTensor R S n := by
  apply CommAlgCat.hom_ext
  exact Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

@[simp, reassoc (attr := simp)]
theorem ι_σ (n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 2)) :
    ι R S (n + 1) j ≫ (conerve R S).σ i = ι R S n (i.predAbove j) :=
  ι_map R S (SimplexCategory.σ i) j

/-- The first coface followed by the original leading-factor contraction is the identity. -/
@[simp, reassoc (attr := simp)]
theorem δ_zero_scalarContraction (n : ℕ) :
    (scalarTensor R S).map ((conerve R S).δ 0) ≫ scalarContraction R S n = 𝟙 _ := by
  apply scalarTerm_hom_ext R S n
  · calc
      _ = (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫
          (scalarTensor R S).map ((conerve R S).δ 0)) ≫ scalarContraction R S n :=
        (Category.assoc _ _ _).symm
      _ = CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫ scalarContraction R S n :=
        congrArg (fun f => f ≫ scalarContraction R S n)
          (includeLeft_scalarTensor R S ((conerve R S).δ 0))
      _ = CommAlgCat.ofHom Algebra.TensorProduct.includeLeft :=
        includeLeft_scalarContraction R S n
      _ = _ := (Category.comp_id _).symm
  · calc
      _ = (CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫
          (scalarTensor R S).map ((conerve R S).δ 0)) ≫ scalarContraction R S n :=
        (Category.assoc _ _ _).symm
      _ = ((conerve R S).δ 0 ≫ CommAlgCat.ofHom Algebra.TensorProduct.includeRight) ≫
          scalarContraction R S n :=
        congrArg (fun f => f ≫ scalarContraction R S n)
          (includeRight_scalarTensor R S ((conerve R S).δ 0))
      _ = (conerve R S).δ 0 ≫
          (CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫ scalarContraction R S n) :=
        Category.assoc _ _ _
      _ = (conerve R S).δ 0 ≫ successorToTensor R S n :=
        congrArg (fun f => (conerve R S).δ 0 ≫ f) (includeRight_scalarContraction R S n)
      _ = CommAlgCat.ofHom Algebra.TensorProduct.includeRight := δ_zero_successorToTensor R S n
      _ = _ := (Category.comp_id _).symm

theorem δ_one_successorToTensor_zero :
    (conerve R S).δ (1 : Fin 2) ≫ successorToTensor R S 0 =
      zeroTo R S ≫ CommAlgCat.ofHom Algebra.TensorProduct.includeLeft := by
  apply term_hom_ext
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [successorFactor]

/-- The remaining degree-zero face gives the original augmentation/retraction composite. -/
theorem δ_one_scalarContraction_zero :
    (scalarTensor R S).map ((conerve R S).δ (1 : Fin 2)) ≫ scalarContraction R S 0 =
      scalarRetraction R S ≫ CommAlgCat.ofHom Algebra.TensorProduct.includeLeft := by
  apply scalarTerm_hom_ext R S 0
  · rw [includeLeft_scalarTensor_assoc, includeLeft_scalarContraction,
      includeLeft_scalarRetraction_assoc]
  · rw [includeRight_scalarTensor_assoc, includeRight_scalarContraction,
      includeRight_scalarRetraction_assoc, δ_one_successorToTensor_zero]

theorem δ_succ_successorToTensor (n : ℕ) (i : Fin (n + 2)) :
    (conerve R S).δ i.succ ≫ successorToTensor R S (n + 1) =
      successorToTensor R S n ≫ (scalarTensor R S).map ((conerve R S).δ i) := by
  apply term_hom_ext R S (n + 1)
  intro j
  cases j using Fin.cases with
  | zero =>
      rw [ι_δ_assoc, Fin.succ_succAbove_zero, ι_successorToTensor,
        ι_successorToTensor_assoc]
      change CommAlgCat.ofHom Algebra.TensorProduct.includeLeft =
        CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫
          (scalarTensor R S).map ((conerve R S).δ i)
      exact (includeLeft_scalarTensor R S _).symm
  | succ j =>
      rw [ι_δ_assoc, Fin.succ_succAbove_succ, ι_successorToTensor,
        ι_successorToTensor_assoc]
      change ι R S (n + 1) (i.succAbove j) ≫
          CommAlgCat.ofHom Algebra.TensorProduct.includeRight =
        ι R S n j ≫ CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫
          (scalarTensor R S).map ((conerve R S).δ i)
      rw [includeRight_scalarTensor, ← Category.assoc, ι_δ]

/-- Every later original face commutes with the leading-factor contraction. -/
theorem δ_succ_scalarContraction (n : ℕ) (i : Fin (n + 2)) :
    (scalarTensor R S).map ((conerve R S).δ i.succ) ≫ scalarContraction R S (n + 1) =
      scalarContraction R S n ≫ (scalarTensor R S).map ((conerve R S).δ i) := by
  apply scalarTerm_hom_ext R S (n + 1)
  · rw [includeLeft_scalarTensor_assoc, includeLeft_scalarContraction,
      includeLeft_scalarContraction_assoc, includeLeft_scalarTensor]
  · rw [includeRight_scalarTensor_assoc, includeRight_scalarContraction,
      includeRight_scalarContraction_assoc, δ_succ_successorToTensor]

theorem σ_succ_successorToTensor (n : ℕ) (i : Fin (n + 1)) :
    (conerve R S).σ i.succ ≫ successorToTensor R S n =
      successorToTensor R S (n + 1) ≫ (scalarTensor R S).map ((conerve R S).σ i) := by
  apply term_hom_ext R S (n + 2)
  intro j
  cases j using Fin.cases with
  | zero =>
      rw [ι_σ_assoc, Fin.predAbove_right_zero, ι_successorToTensor,
        ι_successorToTensor_assoc]
      change CommAlgCat.ofHom Algebra.TensorProduct.includeLeft =
        CommAlgCat.ofHom Algebra.TensorProduct.includeLeft ≫
          (scalarTensor R S).map ((conerve R S).σ i)
      exact (includeLeft_scalarTensor R S _).symm
  | succ j =>
      rw [ι_σ_assoc, Fin.succ_predAbove_succ, ι_successorToTensor,
        ι_successorToTensor_assoc]
      change ι R S n (i.predAbove j) ≫
          CommAlgCat.ofHom Algebra.TensorProduct.includeRight =
        ι R S (n + 1) j ≫ CommAlgCat.ofHom Algebra.TensorProduct.includeRight ≫
          (scalarTensor R S).map ((conerve R S).σ i)
      rw [includeRight_scalarTensor, ← Category.assoc, ι_σ]

/-- Every original degeneracy commutes with the same original contraction. -/
theorem σ_succ_scalarContraction (n : ℕ) (i : Fin (n + 1)) :
    (scalarTensor R S).map ((conerve R S).σ i.succ) ≫ scalarContraction R S n =
      scalarContraction R S (n + 1) ≫ (scalarTensor R S).map ((conerve R S).σ i) := by
  apply scalarTerm_hom_ext R S (n + 2)
  · rw [includeLeft_scalarTensor_assoc, includeLeft_scalarContraction,
      includeLeft_scalarContraction_assoc, includeLeft_scalarTensor]
  · rw [includeRight_scalarTensor_assoc, includeRight_scalarContraction,
      includeRight_scalarContraction_assoc, σ_succ_successorToTensor]

/-- The actual scalar-extended conerve has the native extra degeneracy,
formed from the original multiplication of the leading scalar factor. -/
def scalarExtraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy
    (AlgebraicTopology.Amitsur.opAugmented (scalarAugmented R S)) where
  s' := (scalarRetraction R S).op
  s n := (scalarContraction R S n).op
  s'_comp_ε := by
    apply Quiver.Hom.unop_inj
    exact includeLeft_scalarRetraction R S
  s₀_comp_δ₁ := by
    apply Quiver.Hom.unop_inj
    exact δ_one_scalarContraction_zero R S
  s_comp_δ₀ n := by
    apply Quiver.Hom.unop_inj
    exact δ_zero_scalarContraction R S n
  s_comp_δ n i := by
    apply Quiver.Hom.unop_inj
    exact δ_succ_scalarContraction R S n i
  s_comp_σ n i := by
    apply Quiver.Hom.unop_inj
    exact σ_succ_scalarContraction R S n i

end Algebra.Amitsur
