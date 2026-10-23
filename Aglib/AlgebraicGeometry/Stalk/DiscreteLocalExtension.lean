/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.DiscreteSections

/-!
# Matching local unit representatives on an actual discrete pullback

If a discrete source maps to one point of a scheme, equality of the actual
unit germs at that point proves equality after restriction. The local unit
is pulled back by the original appLE map, retaining its exact domain open.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable {Q P U : Scheme.{u}} [DiscreteTopology Q]

/-- Original unit restrictions agree when their actual germs agree at the constant image point. -/
theorem units_pullback_eq_appLE_of_constant_image (f : Q ⟶ P) (g : P ⟶ U)
    (p : P) (hf : ∀ q : Q, f q = p) (W : U.Opens) (hpW : g p ∈ W)
    (a : Γ(P, ⊤)ˣ) (s : Γ(U, W)ˣ)
    (h : (g.stalkMap p) (U.presheaf.germ W (g p) hpW (s : Γ(U, W))) =
      P.presheaf.germ ⊤ p trivial (a : Γ(P, ⊤))) :
    Units.map f.appTop.hom.toMonoidHom a =
      Units.map ((f ≫ g).appLE W ⊤
        (fun q _ => show g (f q) ∈ W from (hf q).symm ▸ hpW)).hom.toMonoidHom s := by
  apply Units.ext
  apply (globalSectionsStalkProduct Q).injective
  funext q
  have hqp := hf q
  subst p
  have hfg : (f ≫ g).appLE W ⊤
        (fun q' _ => show g (f q') ∈ W from (hf q').symm ▸ hpW) ≫
      Q.presheaf.germ ⊤ q trivial =
      U.presheaf.germ W ((f ≫ g) q) hpW ≫ (f ≫ g).stalkMap q := by
    let i : (⊤ : Q.Opens) ⟶ (f ≫ g) ⁻¹ᵁ W :=
      homOfLE (fun q' _ => show g (f q') ∈ W from (hf q').symm ▸ hpW)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (f ≫ g).app W ≫ k)
        (Q.presheaf.germ_res i q trivial)).trans
          ((f ≫ g).germ_stalkMap W q hpW).symm)
  have hv := congrArg (fun k : Γ(U, W) ⟶ Q.presheaf.stalk q => k.hom (s : Γ(U, W))) hfg
  have hc := congrArg (fun k : U.presheaf.stalk (g (f q)) ⟶ Q.presheaf.stalk q =>
    k.hom (U.presheaf.germ W (g (f q)) hpW (s : Γ(U, W)))) (Hom.stalkMap_comp f g q)
  exact (globalSectionsStalkProduct_apply Q _ q).trans
    ((f.germ_stalkMap_apply ⊤ q trivial (a : Γ(P, ⊤))).symm.trans
      ((congrArg (fun b => (f.stalkMap q) b) h.symm).trans
        (hc.symm.trans (hv.symm.trans (globalSectionsStalkProduct_apply Q _ q).symm))))

end AlgebraicGeometry.Scheme
