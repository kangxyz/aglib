/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.TorsorAction.Basic
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Kernel markings form a free transitive automorphism orbit whenever a marking exists, using the
existing all-test-object kernel universal property.

Source: `lean/R5Lab/Aglib/CategoryTheory/TorsorAction/KernelMarking.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `d8f2184d5d5a4fd5ff66ce0c1953777414d43d43f051ba1bec2acc99e814df99`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open _root_.CategoryTheory

namespace CategoryTheory.KernelMarking

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A G E : Grp C} {p : G ⟶ E}

/-- A genuine universal kernel inclusion cancels morphisms from every test object.
Source: auxiliary marking-orbit argument at the module snapshot. -/
theorem inclusion_cancel (m : KernelMarking A G E p) {T : C}
    (a b : T ⟶ A.X) (h : a ≫ m.inclusion.hom.hom = b ≫ m.inclusion.hom.hom) : a = b := by
  obtain ⟨c, _, hc⟩ := m.unique_lift (b ≫ m.inclusion.hom.hom)
    (by simp [Category.assoc, m.over])
  exact (hc a h).trans (hc b rfl).symm

/-- The kernel inclusion is a monomorphism in the ambient Cartesian category.
Source: auxiliary marking-orbit argument at the module snapshot. -/
instance inclusion_mono (m : KernelMarking A G E p) : Mono m.inclusion.hom.hom where
  right_cancellation a b h := inclusion_cancel m a b h

/-- It is also a monomorphism of genuine internal groups.
Source: auxiliary marking-orbit argument at the module snapshot. -/
instance inclusion_grp_mono (m : KernelMarking A G E p) : Mono m.inclusion where
  right_cancellation f g h := by
    apply Grp.hom_ext
    apply (cancel_mono m.inclusion.hom.hom).mp
    exact congrArg (fun z => z.hom.hom) h

/-- Lift the first inclusion uniquely through the second, on the actual coefficient object.
Source: auxiliary marking-orbit argument at the module snapshot. -/
def comparisonMap (m m' : KernelMarking A G E p) : A.X ⟶ A.X :=
  (m'.unique_lift m.inclusion.hom.hom m.over).choose

/-- The ambient comparison map factors the entire kernel inclusion.
Source: auxiliary marking-orbit argument at the module snapshot. -/
@[simp] theorem comparisonMap_fac (m m' : KernelMarking A G E p) :
    comparisonMap m m' ≫ m'.inclusion.hom.hom = m.inclusion.hom.hom :=
  (m'.unique_lift m.inclusion.hom.hom m.over).choose_spec.1

/-- Cancellation through the second inclusion proves preservation of the unit on every test object.
Source: auxiliary marking-orbit argument at the module snapshot. -/
theorem comparisonMap_one (m m' : KernelMarking A G E p) {T : C} :
    (1 : T ⟶ A.X) ≫ comparisonMap m m' = 1 := by
  apply (cancel_mono m'.inclusion.hom.hom).mp
  simp [Category.assoc]

/-- Cancellation through the second inclusion proves multiplication on every test object.
Source: auxiliary marking-orbit argument at the module snapshot. -/
theorem comparisonMap_mul (m m' : KernelMarking A G E p) {T : C}
    (a b : T ⟶ A.X) :
    (a * b) ≫ comparisonMap m m' = (a ≫ comparisonMap m m') * (b ≫ comparisonMap m m') := by
  apply (cancel_mono m'.inclusion.hom.hom).mp
  simp [Category.assoc, MonObj.mul_comp]

/-- The universally constructed comparison is a genuine group-object homomorphism.
Source: auxiliary marking-orbit argument at the module snapshot. -/
def comparisonHom (m m' : KernelMarking A G E p) : A ⟶ A :=
  Grp.homMk'' (comparisonMap m m')
    (by rw [MonObj.one_eq_one]; exact comparisonMap_one m m')
    (by
      rw [MonObj.mul_eq_mul, comparisonMap_mul]
      simp [CategoryTheory.Hom.mul_def])

/-- Factorization holds as equality of the full group-object morphisms.
Source: auxiliary marking-orbit argument at the module snapshot. -/
@[simp] theorem comparisonHom_fac (m m' : KernelMarking A G E p) :
    comparisonHom m m' ≫ m'.inclusion = m.inclusion := by
  apply Grp.hom_ext
  exact comparisonMap_fac m m'

/-- There is only one genuine comparison homomorphism with this factorization.
Source: auxiliary marking-orbit argument at the module snapshot. -/
theorem comparisonHom_unique (m m' : KernelMarking A G E p) (f : A ⟶ A)
    (h : f ≫ m'.inclusion = m.inclusion) : f = comparisonHom m m' :=
  (cancel_mono m'.inclusion).mp (h.trans (comparisonHom_fac m m').symm)

/-- Reverse universal lifting makes the comparison a genuine automorphism of the coefficient group.
Source: auxiliary marking-orbit argument at the module snapshot. -/
def comparisonIso (m m' : KernelMarking A G E p) : Aut A where
  hom := comparisonHom m m'
  inv := comparisonHom m' m
  hom_inv_id := by
    apply (cancel_mono m.inclusion).mp
    simp [Category.assoc]
  inv_hom_id := by
    apply (cancel_mono m'.inclusion).mp
    simp [Category.assoc]

/-- Any two markings of the same group-object morphism differ by a unique actual automorphism.
Source: auxiliary marking-orbit argument for `K2-018#prop:k2018-arithmetic-characters`
at the module snapshot. -/
theorem existsUnique_comparison (m m' : KernelMarking A G E p) :
    ∃! α : Aut A, α.hom ≫ m'.inclusion = m.inclusion := by
  refine ⟨comparisonIso m m', comparisonHom_fac m m', ?_⟩
  intro α hα
  apply Aut.ext
  exact comparisonHom_unique m m' α.hom hα

/-- Re-mark a kernel by precomposing with an actual internal group automorphism.
Source: auxiliary marking-orbit argument at the module snapshot. -/
def reMark (m : KernelMarking A G E p) (α : Aut A) : KernelMarking A G E p where
  inclusion := α.hom ≫ m.inclusion
  over := by
    simp only [Grp.comp_hom_hom, Category.assoc, m.over, MonObj.comp_one]
  unique_lift k hk := by
    obtain ⟨a, ha, hu⟩ := m.unique_lift k hk
    have hih : α.inv.hom.hom ≫ α.hom.hom.hom = 𝟙 A.X :=
      congrArg (fun z : A ⟶ A => z.hom.hom) α.inv_hom_id
    have hhi : α.hom.hom.hom ≫ α.inv.hom.hom = 𝟙 A.X :=
      congrArg (fun z : A ⟶ A => z.hom.hom) α.hom_inv_id
    refine ⟨a ≫ α.inv.hom.hom, ?_, ?_⟩
    · change (a ≫ α.inv.hom.hom) ≫ (α.hom.hom.hom ≫ m.inclusion.hom.hom) = k
      rw [Category.assoc, ← Category.assoc α.inv.hom.hom α.hom.hom.hom, hih,
        Category.id_comp, ha]
    · intro b hb
      have hba : b ≫ α.hom.hom.hom = a := hu _
        (by simpa only [Grp.comp_hom_hom, Category.assoc] using hb)
      calc
        b = (b ≫ α.hom.hom.hom) ≫ α.inv.hom.hom := by
          simp only [Category.assoc, hhi, Category.comp_id]
        _ = a ≫ α.inv.hom.hom := by rw [hba]

/-- Identity precomposition fixes a kernel marking.
Source: auxiliary marking-orbit argument at the module snapshot. -/
@[simp] theorem reMark_one (m : KernelMarking A G E p) : reMark m 1 = m := by
  apply _root_.CategoryTheory.KernelMarking.ext
  exact Category.id_comp m.inclusion

/-- Precomposition is a right action for mathlib's automorphism multiplication convention.
Source: auxiliary marking-orbit argument at the module snapshot. -/
theorem reMark_mul (m : KernelMarking A G E p) (α β : Aut A) :
    reMark m (α * β) = reMark (reMark m α) β := by
  apply _root_.CategoryTheory.KernelMarking.ext
  exact Category.assoc β.hom α.hom m.inclusion

/-- Re-marking is free: distinct actual group automorphisms give distinct markings.
Source: auxiliary marking-orbit argument at the module snapshot. -/
theorem reMark_injective (m : KernelMarking A G E p) : Function.Injective (reMark m) := by
  intro α β h
  apply Aut.ext
  apply (cancel_mono m.inclusion).mp
  exact congrArg KernelMarking.inclusion h

/-- The marking set is one free automorphism orbit whenever a marking exists.
Source: auxiliary marking-orbit argument for `K2-018#prop:k2018-arithmetic-characters`
at the module snapshot. -/
theorem existsUnique_reMark (m m' : KernelMarking A G E p) :
    ∃! α : Aut A, reMark m α = m' := by
  obtain ⟨α, hα, hunique⟩ := existsUnique_comparison m' m
  refine ⟨α, _root_.CategoryTheory.KernelMarking.ext _ _ hα, ?_⟩
  intro β hβ
  exact hunique β (congrArg KernelMarking.inclusion hβ)

/-- Inverse precomposition supplies the corresponding left action of the actual `Aut A` group.
Source: auxiliary marking-orbit argument at the module snapshot. -/
instance automorphismAction : MulAction (Aut A) (KernelMarking A G E p) where
  smul α m := reMark m α⁻¹
  one_smul m := by
    change reMark m ((1 : Aut A)⁻¹) = m
    rw [inv_one, reMark_one]
  mul_smul α β m := by
    change reMark m (α * β)⁻¹ = reMark (reMark m β⁻¹) α⁻¹
    rw [mul_inv_rev, reMark_mul]

/-- The left automorphism action is free on actual markings.
Source: auxiliary marking-orbit argument at the module snapshot. -/
theorem smul_injective (m : KernelMarking A G E p) :
    Function.Injective (fun α : Aut A => α • m) := by
  intro α β h
  have hi : α⁻¹ = β⁻¹ := reMark_injective m h
  exact inv_injective hi

/-- The left automorphism action has a unique element carrying any marking to another.
Source: auxiliary marking-orbit argument for `K2-018#prop:k2018-arithmetic-characters`
at the module snapshot. -/
theorem existsUnique_smul (m m' : KernelMarking A G E p) :
    ∃! α : Aut A, α • m = m' := by
  obtain ⟨α, hα, hunique⟩ := existsUnique_reMark m m'
  refine ⟨α⁻¹, ?_, ?_⟩
  · change reMark m α⁻¹⁻¹ = m'
    simpa using hα
  · intro β hβ
    have hi : β⁻¹ = α := hunique β⁻¹ hβ
    simpa using congrArg (fun γ : Aut A => γ⁻¹) hi

end CategoryTheory.KernelMarking
