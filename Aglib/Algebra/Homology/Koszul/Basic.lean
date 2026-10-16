/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Single
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal

/-!
# Genuine finite Koszul complexes

The Koszul complex of a finite list of ring elements is constructed by tensoring
the actual one-element multiplication complexes. The empty list gives the
monoidal unit. We prove the recursion, singleton and concatenation
identifications, the differential rule on tensor summands, finite support, and
projectivity of every term. No resolution or acyclicity is assumed as data.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- The actual Koszul chain complex of a finite ordered list of scalars. -/
noncomputable def chainComplex : List R → ChainComplex (ModuleCat R) ℕ
  | [] => HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.down ℕ)
  | a :: s => HomologicalComplex.tensorObj (singleComplex R a) (chainComplex s)

@[simp]
theorem chainComplex_nil : chainComplex ([] : List R) =
    HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.down ℕ) := rfl

@[simp]
theorem chainComplex_cons (a : R) (s : List R) :
    chainComplex (a :: s) =
      HomologicalComplex.tensorObj (singleComplex R a) (chainComplex s) := rfl

/-- A one-element list recovers its multiplication complex. -/
noncomputable def singletonIso (a : R) : chainComplex [a] ≅ singleComplex R a :=
  HomologicalComplex.rightUnitor (singleComplex R a)

/-- Concatenating lists corresponds to tensoring their actual complexes. -/
noncomputable def appendIso : (s t : List R) →
    chainComplex (s ++ t) ≅ HomologicalComplex.tensorObj (chainComplex s) (chainComplex t)
  | [], t => (HomologicalComplex.leftUnitor (chainComplex t)).symm
  | a :: s, t => (whiskerLeftIso (singleComplex R a) (appendIso s t)) ≪≫
      (HomologicalComplex.associator (singleComplex R a) (chainComplex s) (chainComplex t)).symm

/-- The canonical inclusion of each tensor summand in the recursive complex. -/
noncomputable abbrev ιCons (a : R) (s : List R) (i j n : ℕ) (h : i + j = n) :
    (singleComplex R a).X i ⊗ (chainComplex s).X j ⟶ (chainComplex (a :: s)).X n :=
  HomologicalComplex.ιTensorObj (singleComplex R a) (chainComplex s) i j n h

/-- The differential is the sum of the signed horizontal and vertical differentials. -/
@[reassoc]
theorem ιCons_d (a : R) (s : List R) (i j n m : ℕ) (h : i + j = n) :
    ιCons a s i j n h ≫ (chainComplex (a :: s)).d n m =
      HomologicalComplex.mapBifunctor.d₁ (singleComplex R a) (chainComplex s)
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i j m +
      HomologicalComplex.mapBifunctor.d₂ (singleComplex R a) (chainComplex s)
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i j m := by
  change HomologicalComplex.ιTensorObj (singleComplex R a) (chainComplex s) i j n h ≫
    (HomologicalComplex.tensorObj (singleComplex R a) (chainComplex s)).d n m = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]

/-- The one-element factor is zero above its length. -/
theorem single_isZero_X (a : R) (n : ℕ) (h : 1 < n) : IsZero ((singleComplex R a).X n) := by
  obtain (_ | _ | n) := n
  · omega
  · omega
  · exact isZero_zero _

/-- The tensor product of bounded nonnegative complexes has the sum support bound. -/
theorem tensor_isZero_X (K L : ChainComplex (ModuleCat R) ℕ) (p q : ℕ)
    (hK : ∀ n, p < n → IsZero (K.X n)) (hL : ∀ n, q < n → IsZero (L.X n))
    (n : ℕ) (hn : p + q < n) : IsZero ((HomologicalComplex.tensorObj K L).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  have hz : IsZero (K.X i ⊗ L.X j) := by
    by_cases hi : p < i
    · exact Functor.map_isZero ((tensoringRight (ModuleCat R)).obj (L.X j)) (hK i hi)
    · exact Functor.map_isZero ((tensoringLeft (ModuleCat R)).obj (K.X i))
        (hL j (by omega))
  exact hz.eq_of_src _ _

/-- A finite list has no terms above its length. -/
theorem isZero_X (s : List R) (n : ℕ) (h : s.length < n) :
    IsZero ((chainComplex s).X n) := by
  induction s generalizing n with
  | nil =>
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (𝟙_ (ModuleCat R)) n (by simpa using (Nat.ne_of_gt h))
  | cons a s ih =>
    exact tensor_isZero_X (singleComplex R a) (chainComplex s) 1 s.length
      (single_isZero_X a) ih n (by simpa [Nat.add_comm] using h)

/-- Consequently all homology above the length vanishes, without regularity. -/
theorem exactAt_above_length (s : List R) (n : ℕ) (h : s.length < n) :
    (chainComplex s).ExactAt n :=
  HomologicalComplex.ExactAt.of_isZero (isZero_X s n h)

/-- Tensoring a projective module with a term of a one-element complex stays projective. -/
theorem single_tensor_projective (a : R) (X : ModuleCat R) [Projective X] (i : ℕ) :
    Projective ((singleComplex R a).X i ⊗ X) := by
  obtain (_ | _ | i) := i
  · exact Projective.of_iso (λ_ X).symm inferInstance
  · exact Projective.of_iso (λ_ X).symm inferInstance
  · exact (Functor.map_isZero ((tensoringRight (ModuleCat R)).obj X)
      (isZero_zero _)).projective

/-- Every term of the actual finite Koszul complex is projective. -/
instance chainComplex_projective (s : List R) (n : ℕ) : Projective ((chainComplex s).X n) := by
  induction s generalizing n with
  | nil =>
    by_cases hn : n = 0
    · subst n
      exact Projective.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat R))).symm
        (inferInstanceAs (Projective (ModuleCat.of R R)))
    · exact (isZero_X [] n (Nat.pos_of_ne_zero hn)).projective
  | cons a s ih =>
    have (j : ℕ) : Projective ((chainComplex s).X j) := ih j
    change Projective (∐ fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
      (singleComplex R a).X ij.val.1 ⊗ (chainComplex s).X ij.val.2)
    constructor
    intro E X f e _
    refine ⟨Sigma.desc (fun ij => ?_), ?_⟩
    · have : Projective ((singleComplex R a).X ij.val.1 ⊗ (chainComplex s).X ij.val.2) :=
        single_tensor_projective a _ ij.val.1
      exact Projective.factorThru (Sigma.ι
        (fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
          (singleComplex R a).X ij.val.1 ⊗ (chainComplex s).X ij.val.2) ij ≫ f) e
    · apply Sigma.hom_ext
      intro ij
      have : Projective ((singleComplex R a).X ij.val.1 ⊗ (chainComplex s).X ij.val.2) :=
        single_tensor_projective a _ ij.val.1
      rw [← Category.assoc, Sigma.ι_comp_desc, Projective.factorThru_comp]

end ChainComplex.Koszul
