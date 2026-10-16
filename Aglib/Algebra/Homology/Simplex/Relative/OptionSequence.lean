/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Contraction
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Removing one vertex in the native relative-simplex complex

Allowing the extra vertex `none` gives the actual short exact sequence

`C(Option ι, univ) → C(Option ι, range some) → C(ι, univ)`.

Its first map is extension by zero; its second map evaluates on tuples of
`some` vertices. When `ι` is nonempty, the middle complex has the explicit
insertion contraction, so the native connecting homomorphism is an
isomorphism in every pair of successive degrees.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial

universe u v

namespace AlgebraicTopology.RelativeSimplex

variable {ι : Type v} {R : Type u} [Ring R] {S T : Set ι} {n : ℕ}

/-- The actual inclusion for a stronger required support, by extension by zero. -/
def supportMap (_h : S ⊆ T) (n : ℕ) : Cochains R T n →ₗ[R] Cochains R S n where
  toFun x a := extendByZero x a.val
  map_add' x y := by
    classical
    ext a
    dsimp [extendByZero]
    split_ifs <;> simp
  map_smul' r x := by
    classical
    ext a
    dsimp [extendByZero]
    split_ifs <;> simp

theorem extendByZero_supportMap (h : S ⊆ T) (x : Cochains R T n)
    (a : Fin (n + 1) → ι) : extendByZero (supportMap h n x) a = extendByZero x a := by
  classical
  by_cases ha : S ⊆ Set.range a
  · simp only [extendByZero, dite_eq_left ha, supportMap, LinearMap.coe_mk, AddHom.coe_mk]
  · have hT : ¬ T ⊆ Set.range a := fun h' => ha (h.trans h')
    simp only [extendByZero, dite_eq_right ha, dite_eq_right hT]

/-- The inclusion of support conditions is a genuine cosimplicial map. -/
def cosimplicialSupportMap (h : S ⊆ T) : cosimplicial R T ⟶ cosimplicial R S where
  app n := ModuleCat.ofHom (supportMap h n.len)
  naturality {_ _} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    change extendByZero (positionMap f.toOrderHom x) a.val =
      extendByZero (supportMap h _ x) (a.val ∘ f.toOrderHom)
    rw [extendByZero_positionMap, extendByZero_supportMap]

/-- The same canonical inclusion on the native alternating complexes. -/
def complexSupportMap (h : S ⊆ T) : complex R T ⟶ complex R S :=
  (alternatingCofaceMapComplex _).map (cosimplicialSupportMap h)

@[simp]
theorem complexSupportMap_f (h : S ⊆ T) (n : ℕ) :
    (complexSupportMap (R := R) h).f n = ModuleCat.ofHom (supportMap h n) := rfl

/-- A full-support tuple on the old vertices gives an admissible tuple of
`some` vertices in the enlarged vertex set. -/
def someTuple (a : Tuple (Set.univ : Set ι) n) : Tuple (Set.range (@Option.some ι)) n :=
  ⟨Option.some ∘ a.val, by
    rintro i ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := a.property (Set.mem_univ j)
    exact ⟨k, congrArg Option.some hk⟩⟩

theorem someTuple_injective :
    Function.Injective (someTuple : Tuple (Set.univ : Set ι) n → _) := by
  intro a b hab
  apply Subtype.ext
  funext k
  exact Option.some.inj (congrFun (congrArg Subtype.val hab) k)

theorem some_supported_iff (a : Fin (n + 1) → ι) :
    Set.range (@Option.some ι) ⊆ Set.range (Option.some ∘ a) ↔ Set.univ ⊆ Set.range a := by
  constructor
  · intro h i hi
    obtain ⟨k, hk⟩ := h ⟨i, rfl⟩
    exact ⟨k, Option.some.inj hk⟩
  · rintro h _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := h (Set.mem_univ i)
    exact ⟨k, congrArg Option.some hk⟩

/-- The original evaluation on tuples with no new vertex. -/
def restrictSome (n : ℕ) :
    Cochains R (Set.range (@Option.some ι)) n →ₗ[R] Cochains R (Set.univ : Set ι) n where
  toFun x a := x (someTuple a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extendByZero_restrictSome (x : Cochains R (Set.range (@Option.some ι)) n)
    (a : Fin (n + 1) → ι) :
    extendByZero (restrictSome n x) a = extendByZero x (Option.some ∘ a) := by
  classical
  by_cases ha : Set.univ ⊆ Set.range a
  · have hsome := (some_supported_iff a).mpr ha
    simp only [extendByZero, dite_eq_left ha, dite_eq_left hsome, restrictSome,
      LinearMap.coe_mk, AddHom.coe_mk, someTuple]
  · have hsome : ¬ Set.range (@Option.some ι) ⊆ Set.range (Option.some ∘ a) :=
      fun h => ha ((some_supported_iff a).mp h)
    simp only [extendByZero, dite_eq_right ha, dite_eq_right hsome]

/-- Restricting tuples to the old vertices is a genuine cosimplicial map. -/
def cosimplicialRestrictSome :
    cosimplicial R (Set.range (@Option.some ι)) ⟶ cosimplicial R (Set.univ : Set ι) where
  app n := ModuleCat.ofHom (restrictSome n.len)
  naturality {_ _} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    change extendByZero x ((Option.some ∘ a.val) ∘ f.toOrderHom) =
      extendByZero (restrictSome _ x) (a.val ∘ f.toOrderHom)
    rw [extendByZero_restrictSome]
    rfl

/-- The canonical restriction chain map on the actual alternating complexes. -/
def complexRestrictSome :
    complex R (Set.range (@Option.some ι)) ⟶ complex R (Set.univ : Set ι) :=
  (alternatingCofaceMapComplex _).map cosimplicialRestrictSome

@[simp]
theorem complexRestrictSome_f (n : ℕ) :
    (complexRestrictSome (R := R) (ι := ι)).f n = ModuleCat.ofHom (restrictSome n) := rfl

/-- The actual vertex-removal short complex. -/
def optionSequence (R : Type u) [Ring R] (ι : Type v) :
    ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℕ) :=
  ShortComplex.mk (complexSupportMap (Set.subset_univ (Set.range (@Option.some ι))))
    complexRestrictSome (by
      ext n x
      apply funext
      intro a
      change extendByZero x (Option.some ∘ a.val) = 0
      apply extendByZero_of_not_supported
      intro h
      obtain ⟨k, hk⟩ := h (Set.mem_univ none)
      cases hk)

theorem exists_someTuple_of_not_univ_supported
    (b : Tuple (Set.range (@Option.some ι)) n)
    (hb : ¬ Set.univ ⊆ Set.range b.val) :
    ∃ a : Tuple (Set.univ : Set ι) n, someTuple a = b := by
  classical
  have hnone : none ∉ Set.range b.val := by
    intro hn
    apply hb
    intro i hi
    cases i with
    | none => exact hn
    | some i => exact b.property ⟨i, rfl⟩
  have hex (k : Fin (n + 1)) : ∃ i, b.val k = some i := by
    cases hk : b.val k with
    | none => exact (hnone ⟨k, hk⟩).elim
    | some i => exact ⟨i, rfl⟩
  choose a ha using hex
  have hsurj : Set.univ ⊆ Set.range a := by
    intro i hi
    obtain ⟨k, hk⟩ := b.property ⟨i, rfl⟩
    exact ⟨k, Option.some.inj ((ha k).symm.trans hk)⟩
  refine ⟨⟨a, hsurj⟩, Subtype.ext ?_⟩
  funext k
  exact (ha k).symm

/-- The vertex-removal sequence is genuinely short exact in every degree. -/
theorem optionSequence_shortExact (R : Type u) [Ring R] (ι : Type v) :
    (optionSequence R ι).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change restrictSome n x = 0 at hx
    let z : Cochains R (Set.univ : Set (Option ι)) n :=
      fun a => x ⟨a.val, fun i hi => a.property (Set.mem_univ i)⟩
    refine ⟨z, ?_⟩
    funext b
    change extendByZero z b.val = x b
    by_cases hb : Set.univ ⊆ Set.range b.val
    · simp only [extendByZero, dite_eq_left hb, z]
    · rw [extendByZero_of_not_supported z b.val hb]
      obtain ⟨a, rfl⟩ := exists_someTuple_of_not_univ_supported b hb
      exact (congrFun hx a).symm
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y hxy
    funext a
    let b : Tuple (Set.range (@Option.some ι)) n :=
      ⟨a.val, fun i hi => a.property (Set.mem_univ i)⟩
    have h := congrFun hxy b
    change extendByZero x a.val = extendByZero y a.val at h
    simpa only [extendByZero_apply] using h
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro y
    refine ⟨Function.extend someTuple y (fun _ => 0), ?_⟩
    funext a
    change Function.extend someTuple y (fun _ => 0) (someTuple a) = y a
    exact someTuple_injective.extend_apply y (fun _ => 0) a

/-- The native connecting homomorphism removes one vertex and shifts the
actual full-support homology by one degree. -/
def optionDeltaIso (R : Type u) [Ring R] (ι : Type v) [Nonempty ι] (n : ℕ) :
    (complex R (Set.univ : Set ι)).homology n ≅
      (complex R (Set.univ : Set (Option ι))).homology (n + 1) := by
  have hmid : (complex R (Set.range (@Option.some ι))).Acyclic :=
    acyclic_of_nonempty_of_not_mem none (by simp)
      ⟨some (Classical.choice ‹Nonempty ι›), ⟨_, rfl⟩⟩
  exact (optionSequence_shortExact R ι).δIso n (n + 1) (by simp)
    (hmid n).isZero_homology (hmid (n + 1)).isZero_homology

end AlgebraicTopology.RelativeSimplex
