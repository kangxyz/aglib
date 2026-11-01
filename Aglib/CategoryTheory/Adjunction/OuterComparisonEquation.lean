/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.TripleMateStructural

/-! # Whole compatibility after identifying the original outer-adjoint maps -/

@[expose] public noncomputable section
namespace CategoryTheory
variable {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
  {M N : A ⥤ B} {Q : A ⥤ E} {P : B ⥤ D} {I S : E ⥤ D}

/-- The original four-map square before concrete component evaluation. -/
def OuterComparisonEquation (σ : Q ⋙ I ⟶ M ⋙ P)
    (b : M ⟶ N) (bI : I ⟶ S) (c : N ⋙ P ⟶ Q ⋙ S) : Prop :=
  ∀ K, σ.app K ≫ P.map (b.app K) ≫ c.app K = bI.app (Q.obj K)

/-- Whole original map identifications transport the proved canonical triple square. -/
theorem outerComparisonEquation_of_triple {U : D ⥤ E} {V : B ⥤ A}
    (t : Adjunction.Triple I U S) (t' : Adjunction.Triple M V N)
    [I.Full] [I.Faithful] [M.Full] [M.Faithful]
    (σ : Q ⋙ I ⟶ M ⋙ P) (b : M ⟶ N) (bI : I ⟶ S) (c : N ⋙ P ⟶ Q ⋙ S)
    (hb : b = t'.leftToRight) (hbI : bI = t.leftToRight)
    (h : Adjunction.TripleMateStructuralEquation t t' σ c) :
    OuterComparisonEquation σ b bI c := by
  subst b
  subst bI
  exact h

end CategoryTheory
