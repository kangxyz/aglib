/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.CategoryTheory.Subobject.HasCardinalLT

/-!
# A uniform regular ordinal for the actual replacement tower

The bound simultaneously controls all prescribed test complexes and the
separator's subobjects. Native Grothendieck smallness and native regular-cardinal
existence supply the bound; no presentability or replacement axiom is assumed.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ) (G : C)

/-- The native subobject types whose sizes control factorization into the tower. -/
def replacementSizeFamily : Option ι → Type (max u v)
  | none => Subobject G
  | some i => Subobject (A i)

/-- A single regular cardinal bounds the tests and all subobjects of the separator. -/
lemma exists_replacementCardinal :
    ∃ κ : Cardinal.{w}, κ.IsRegular ∧ HasCardinalLT (Subobject G) κ ∧
      ∀ i, HasCardinalLT (Subobject (A i)) κ := by
  have (i : Option ι) : Small.{w} (replacementSizeFamily A G i) := by
    cases i <;> dsimp [replacementSizeFamily] <;> infer_instance
  obtain ⟨κ, hκ, h⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
    (replacementSizeFamily A G)
  exact ⟨κ, hκ, h none, fun i => h (some i)⟩

/-- The constructed uniform regular cardinal. -/
def replacementCardinal : Cardinal.{w} := (exists_replacementCardinal A G).choose

lemma replacementCardinal_isRegular : (replacementCardinal A G).IsRegular :=
  (exists_replacementCardinal A G).choose_spec.1

instance replacementCardinal_fact : Fact (replacementCardinal A G).IsRegular :=
  ⟨replacementCardinal_isRegular A G⟩

lemma replacementCardinal_separator : HasCardinalLT (Subobject G) (replacementCardinal A G) :=
  (exists_replacementCardinal A G).choose_spec.2.1

lemma replacementCardinal_test (i : ι) :
    HasCardinalLT (Subobject (A i)) (replacementCardinal A G) :=
  (exists_replacementCardinal A G).choose_spec.2.2 i

lemma replacementCardinal_subobject (S : Subobject G) :
    HasCardinalLT (Subobject (Subobject.underlying.obj S)) (replacementCardinal A G) :=
  Subobject.hasCardinalLT_of_mono (replacementCardinal_separator A G) S.arrow

/-- The actual small regular ordinal used for transfinite iteration. -/
abbrev replacementIndex : Type w := (replacementCardinal A G).ord.ToType

instance replacementIndex_nonempty : Nonempty (replacementIndex A G) := by
  simpa using (replacementCardinal_isRegular A G).ne_zero

instance replacementIndexOrderBot : OrderBot (replacementIndex A G) :=
  WellFoundedLT.toOrderBot _

instance replacementIndex_noMaxOrder : NoMaxOrder (replacementIndex A G) :=
  Cardinal.noMaxOrder (replacementCardinal_isRegular A G).aleph0_le

instance replacementIndex_isCardinalFiltered :
    IsCardinalFiltered (replacementIndex A G) (replacementCardinal A G) := inferInstance

end CochainComplex
