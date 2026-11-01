/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AbelGeometry
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Dimension

/-!
# Abel images below the genus are proper subsets

The original Jacobian dimension equals the coherent genus. Combining it with
the bound for the actual proper ordered Abel image shows that degree below
the genus cannot cover the Jacobian. This is a dimension assertion, distinct
from the subsequent rank-one fibre and birationality arguments.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Scheme Scheme.RelativePicard Scheme.Group

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

/-- Below the genus, the actual based Abel morphism cannot cover the original
Jacobian. This is an upper-dimension argument, not Abel birationality. -/
theorem not_surjective_jacobianAbelMorphism {n : ℕ} (hn : n < coherentGenus k X) :
    ¬ Function.Surjective (jacobianAbelMorphism hX o ho P R n).left := by
  let := picardCommGrpObj X.hom P R
  intro hsurj
  have : Surjective (jacobianAbelMorphism hX o ho P R n).left := ⟨hsurj⟩
  have := isProper_jacobianAbelMorphism hX o ho P R n
  have hd := Scheme.Hom.topologicalKrullDim_le_of_isProper_of_surjective
    (jacobianAbelMorphism hX o ho P R n).left
  rw [topologicalKrullDim_identityComponentOver_eq_coherentGenus hX P R,
    topologicalKrullDim_parameter hX n] at hd
  have hlt : (n : WithBot ℕ∞) < (coherentGenus k X : WithBot ℕ∞) := by exact_mod_cast hn
  exact hlt.not_ge hd

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
