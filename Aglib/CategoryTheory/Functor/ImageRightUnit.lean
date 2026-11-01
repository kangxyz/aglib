/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageComparison
public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly

/-! # Assembly of the original right-unit image triangle

The open face and the central identity-open contraction are separate inputs.
Neither is replaced by the desired image triangle. The actual supplied map is
retained by its compositor formula.
-/

@[expose] public section
namespace CategoryTheory
variable {U A B D E : Type*}
  [Category* U] [Category* A] [Category* B] [Category* D] [Category* E]
  {J : U ⥤ A} {L : U ⥤ B} {M N : A ⥤ B}
  {Q : A ⥤ E} {P : B ⥤ D} {P₀ : B ⥤ E} {I : E ⥤ D} {R : D ⥤ E}

/-- The original source-open face of a right-unit refinement. -/
def RightUnitOpenEquation (c : J ⋙ M ≅ L) (δ : L ⟶ J ⋙ N) (b : M ⟶ N) : Prop :=
  ∀ K, c.hom.app K ≫ δ.app K = b.app (J.obj K)

/-- The identity-open contraction before inserting the source open immersion. -/
def RightUnitMiddleEquation (σ : Q ⋙ I ⟶ M ⋙ P) (b : M ⟶ N)
    (d : P ⋙ R ≅ P₀) (e : N ⋙ P₀ ≅ Q) (ε : I ⋙ R ≅ 𝟭 E) : Prop :=
  ∀ K, R.map (σ.app K) ≫ R.map (P.map (b.app K)) ≫
    d.hom.app (N.obj K) ≫ e.hom.app K = ε.hom.app (Q.obj K)

/-- The actual original image comparison contracts the supplied right-unit map. -/
def RightUnitImageEquation (δ : L ⟶ J ⋙ N) (e : N ⋙ P₀ ≅ Q)
    (ε : I ⋙ R ≅ 𝟭 E) (α : J ⋙ Q ⋙ I ⋙ R ⟶ L ⋙ P₀) : Prop :=
  ∀ K, α.app K ≫ (imageComparison δ e).app K = ε.hom.app (Q.obj (J.obj K))

/-- The original open and middle faces imply the actual right-unit image triangle. -/
theorem rightUnitImageEquation (σ : Q ⋙ I ⟶ M ⋙ P)
    (c : J ⋙ M ≅ L) (δ : L ⟶ J ⋙ N) (b : M ⟶ N)
    (d : P ⋙ R ≅ P₀) (e : N ⋙ P₀ ≅ Q) (ε : I ⋙ R ≅ 𝟭 E)
    (α : J ⋙ Q ⋙ I ⋙ R ⟶ L ⋙ P₀)
    (hopen : RightUnitOpenEquation c δ b)
    (hmiddle : RightUnitMiddleEquation σ b d e ε)
    (hα : ImageCompositionFormula σ c d α) :
    RightUnitImageEquation δ e ε α := by
  intro K
  rw [hα, imageComparison_app]
  calc
    _ = R.map (σ.app (J.obj K)) ≫
        (R.map (P.map (c.hom.app K)) ≫
          (d.hom.app (L.obj K) ≫ P₀.map (δ.app K))) ≫
        e.hom.app (J.obj K) := by simp only [Category.assoc]
    _ = R.map (σ.app (J.obj K)) ≫
        (R.map (P.map (c.hom.app K)) ≫
          (R.map (P.map (δ.app K)) ≫ d.hom.app (N.obj (J.obj K)))) ≫
        e.hom.app (J.obj K) := by rw [← d.hom.naturality]; rfl
    _ = R.map (σ.app (J.obj K)) ≫ R.map (P.map (c.hom.app K ≫ δ.app K)) ≫
        d.hom.app (N.obj (J.obj K)) ≫ e.hom.app (J.obj K) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [hopen]; exact hmiddle (J.obj K)

end CategoryTheory
