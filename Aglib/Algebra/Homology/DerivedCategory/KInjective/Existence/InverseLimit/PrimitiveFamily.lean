/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InverseLimit.CoherentChoice
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InverseLimit.Predecessors
public import Aglib.Algebra.Homology.CompatiblePrimitive

/-!
# Compatible primitives over a well-founded inverse diagram

This intermediate theorem assumes exactness of the entire predecessor limits.
The final ordinal induction must discharge that hypothesis; it is not an
inverse-limit exactness axiom.
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex.InverseLimit

variable {J : Type w} [PartialOrder J]
  (F : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)

/-- Compatible elements with respect to every transition of the native diagram. -/
def Compatible (n : ℤ) (x : ∀ i, (F.obj (op i)).X n) : Prop :=
  ∀ i j (h : j ≤ i), (F.map (homOfLE h).op).f n (x i) = x j

lemma compatible_of_strict (n : ℤ) (x : ∀ i, (F.obj (op i)).X n)
    (hx : ∀ i j (h : j < i), (F.map (homOfLE h.le).op).f n (x i) = x j) :
    Compatible F n x := by
  intro i j h
  obtain h | rfl := lt_or_eq_of_le h
  · exact hx i j h
  · simp

variable [∀ (i : J) (n : ℤ), HasLimit
    (predecessors F i ⋙ HomologicalComplex.eval AddCommGrpCat (.up ℤ) n)]

/-- A coherent predecessor family of primitives extends to the current stage.
The comparison surjectivity is onto the entire predecessor limit. -/
lemma extend_primitive (n : ℤ)
    (x : ∀ i, (F.obj (op i)).X n) (hx : Compatible F n x)
    (hcycle : ∀ i, (F.obj (op i)).d n (n + 1) (x i) = 0)
    (i : J) (hi : (F.obj (op i)).ExactAt n)
    (hpred : (limit (predecessors F i)).ExactAt (n - 1))
    (hsurj : Function.Surjective ((predecessorComparison F i).f (n - 2)))
    (z : ∀ j : Set.Iio i, (F.obj (op j.val)).X (n - 1))
    (hz : ∀ j, (F.obj (op j.val)).d (n - 1) n (z j) = x j.val)
    (hzc : Compatible (predecessors F i) (n - 1) z) :
    ∃ y : (F.obj (op i)).X (n - 1),
      (F.obj (op i)).d (n - 1) n y = x i ∧
      ∀ j : Set.Iio i, (F.map (homOfLE j.property.le).op).f (n - 1) y = z j := by
  let zlim := limitElement (predecessors F i) (n - 1) (fun j => z j.unop)
    (fun j k f => hzc j.unop k.unop (leOfHom f.unop))
  have hproj (j : (Set.Iio i)ᵒᵖ) :
      (limit.π (predecessors F i) j).f (n - 1) zlim = z j.unop :=
    limitElement_π (predecessors F i) (n - 1) _ _ j
  have hzlim : (limit (predecessors F i)).d (n - 1) n zlim =
      (predecessorComparison F i).f n (x i) := by
    apply limitElement_ext (predecessors F i) n
    intro j
    have hc := congrArg (fun f => f zlim) ((limit.π (predecessors F i) j).comm (n - 1) n)
    simp only [ConcreteCategory.comp_apply] at hc
    rw [← hc, hproj]
    change (F.obj (op j.unop.val)).d (n - 1) n (z j.unop) = _
    rw [hz]
    have hp := congrArg (fun f => f.f n) (predecessorComparison_π F i j)
    have hp' := congrArg (fun f => f (x i)) hp
    simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hp'
    rw [hp']
    exact (hx i j.unop.val j.unop.property.le).symm
  obtain ⟨y, hy, hpy⟩ := exists_compatible_primitive (predecessorComparison F i) n
    hi hpred hsurj (x i) (hcycle i) zlim hzlim
  refine ⟨y, hy, ?_⟩
  intro j
  have he := congrArg (fun a => (limit.π (predecessors F i) (op j)).f (n - 1) a) hpy
  rw [hproj] at he
  have hp := congrArg (fun f => f.f (n - 1)) (predecessorComparison_π F i (op j))
  have hp' := congrArg (fun f => f y) hp
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hp'
  exact hp'.symm.trans he

end CochainComplex.InverseLimit
