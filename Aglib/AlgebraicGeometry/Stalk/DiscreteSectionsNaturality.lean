/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.DiscreteSections

/-!
# Naturality of original discrete-scheme unit coordinates

The coordinates commute with every original scheme map between discrete
schemes. This is the original germ/stalk-map square on actual units.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable {P Q : Scheme.{u}} [DiscreteTopology P] [DiscreteTopology Q] (f : Q ⟶ P)

/-- Literal naturality of the actual discrete global-unit coordinates. -/
theorem globalUnitsStalkProduct_naturality (a : Γ(P, ⊤)ˣ) (q : Q) :
    globalUnitsStalkProduct Q (Units.map f.appTop.hom.toMonoidHom a) q =
      Units.map (f.stalkMap q).hom.toMonoidHom (globalUnitsStalkProduct P a (f q)) := by
  apply Units.ext
  have hQ := globalSectionsStalkProduct_apply Q (f.appTop (a : Γ(P, ⊤))) q
  have hP := globalSectionsStalkProduct_apply P (a : Γ(P, ⊤)) (f q)
  exact hQ.trans ((f.germ_stalkMap_apply ⊤ q trivial (a : Γ(P, ⊤))).symm.trans
    (congrArg (fun b => (f.stalkMap q) b) hP.symm))

/-- Global units on a discrete scheme are equal exactly when all original unit germs agree. -/
theorem globalUnits_eq_iff_germs (a b : Γ(P, ⊤)ˣ) :
    a = b ↔ ∀ p : P, Units.map (P.presheaf.germ ⊤ p trivial).hom.toMonoidHom a =
      Units.map (P.presheaf.germ ⊤ p trivial).hom.toMonoidHom b := by
  constructor
  · rintro rfl p
    rfl
  · intro h
    apply (globalUnitsStalkProduct P).injective
    funext p
    exact (globalUnitsStalkProduct_apply P a p).trans
      ((h p).trans (globalUnitsStalkProduct_apply P b p).symm)

end AlgebraicGeometry.Scheme
