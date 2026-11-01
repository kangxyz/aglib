/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageRightUnit

/-! # Original outer-adjoint compatibility contracts the right-unit middle face -/

@[expose] public section
namespace CategoryTheory
variable {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
  {M N : A ⥤ B} {Q : A ⥤ E} {P : B ⥤ D} {P₀ : B ⥤ E}
  {I S : E ⥤ D} {R : D ⥤ E}

/-- The whole original direct-image structural triangle, before evaluating a native object. -/
def RightUnitStructuralEquation (c : N ⋙ P ≅ Q ⋙ S) (d : P ⋙ R ≅ P₀)
    (e : N ⋙ P₀ ≅ Q) (t : S ⋙ R ≅ 𝟭 E) : Prop :=
  Functor.isoWhiskerLeft N d ≪≫ e =
    (Functor.associator N P R).symm ≪≫ Functor.isoWhiskerRight c R ≪≫
      Functor.associator Q S R ≪≫ Functor.isoWhiskerLeft Q t ≪≫ Functor.rightUnitor Q

/-- Canonical outer-adjoint compatibility, original proper coherence and the original identity
contraction imply the right-unit middle equation without assuming an exceptional unit law. -/
theorem rightUnitMiddleEquation_of_outerComparison
    (σ : Q ⋙ I ⟶ M ⋙ P) (b : M ⟶ N) (bI : I ⟶ S)
    (c : N ⋙ P ≅ Q ⋙ S) (d : P ⋙ R ≅ P₀) (e : N ⋙ P₀ ≅ Q)
    (t : S ⋙ R ≅ 𝟭 E) (ε : I ⋙ R ≅ 𝟭 E)
    (hσ : ∀ K, σ.app K ≫ P.map (b.app K) ≫ c.hom.app K = bI.app (Q.obj K))
    (hs : RightUnitStructuralEquation c d e t)
    (hi : Functor.whiskerRight bI R ≫ t.hom = ε.hom) :
    RightUnitMiddleEquation σ b d e ε := by
  intro K
  have hsK := congrArg (fun z => z.hom.app K) hs
  have hiK := congrArg (fun z => z.app (Q.obj K)) hi
  change R.map (bI.app (Q.obj K)) ≫ t.hom.app (Q.obj K) =
    ε.hom.app (Q.obj K) at hiK
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Category.id_comp] at hsK
  change d.hom.app (N.obj K) ≫ e.hom.app K =
    R.map (c.hom.app K) ≫ t.hom.app (Q.obj K) ≫ 𝟙 ((𝟭 E).obj (Q.obj K)) at hsK
  rw [Category.comp_id (t.hom.app (Q.obj K))] at hsK
  rw [hsK, ← R.map_comp_assoc, ← R.map_comp_assoc, Category.assoc, hσ, hiK]

end CategoryTheory
