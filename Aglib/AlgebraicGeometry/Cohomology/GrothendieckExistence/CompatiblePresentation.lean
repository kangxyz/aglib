/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion

/-!
# Canonical completion factors of compatible generators

Compatible maps from an algebraic coefficient into an annihilated tower
factor uniquely through its original completion. This construction requires
only annihilation, not cartesian reduction, and therefore also applies to the
ordinary relation tower. Stagewise epimorphisms remain epimorphisms after
factoring through the original quotient units.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable {X : Scheme.{u}} (K : X.IdealSheafData)
  {P : X.Modules} {F : ℕᵒᵖ ⥤ X.Modules}
  (hF : ∀ n : ℕ, killedByIdealSheaf (K ^ n) (F.obj (op n)))
  (p : (Functor.const ℕᵒᵖ).obj P ⟶ F)

/-- The unique stagewise factors through the actual ideal-sheaf quotients
form a natural transformation on the original diagrams. -/
def compatibleQuotientDesc : idealSheafQuotientTower X K P ⟶ F where
  app n := idealSheafQuotientDesc X (K ^ n.unop) (p.app n) (hF n.unop)
  naturality m n g := by
    apply (cancel_epi ((idealSheafQuotientUnit X (K ^ m.unop)).app P)).mp
    change (idealSheafQuotientUnit X (K ^ m.unop)).app P ≫
        idealSheafQuotientMap X (K ^ m.unop)
          (idealSheaf_pow_le X K (leOfHom g.unop)) P ≫
        idealSheafQuotientDesc X (K ^ n.unop) (p.app n) (hF n.unop) =
      (idealSheafQuotientUnit X (K ^ m.unop)).app P ≫
        idealSheafQuotientDesc X (K ^ m.unop) (p.app m) (hF m.unop) ≫ F.map g
    have hl := congrArg
      (fun v => v ≫ idealSheafQuotientDesc X (K ^ n.unop) (p.app n) (hF n.unop))
      (idealSheafQuotientUnit_map X (K ^ m.unop)
        (idealSheaf_pow_le X K (leOfHom g.unop)) P)
    have hr := congrArg (fun v => v ≫ F.map g)
      (idealSheafQuotientUnit_desc X (K ^ m.unop) (p.app m) (hF m.unop))
    have hn := p.naturality g
    change 𝟙 P ≫ p.app n = p.app m ≫ F.map g at hn
    have hn' : p.app n = p.app m ≫ F.map g := (Category.id_comp _).symm.trans hn
    exact (Category.assoc _ _ _).symm.trans
      (hl.trans ((idealSheafQuotientUnit_desc X (K ^ n.unop)
        (p.app n) (hF n.unop)).trans (hn'.trans
          (hr.symm.trans (Category.assoc _ _ _)))))

/-- The factor preserves every original algebraic-to-formal generator map. -/
@[reassoc (attr := simp)]
theorem idealSheafQuotientTowerUnit_compatibleQuotientDesc :
    idealSheafQuotientTowerUnit X K P ≫ compatibleQuotientDesc K hF p = p := by
  apply NatTrans.ext
  funext n
  exact idealSheafQuotientUnit_desc X (K ^ n.unop) (p.app n) (hF n.unop)

/-- There is no choice in the compatible factor once the original maps from
an algebraic coefficient have been fixed. -/
theorem compatibleQuotientDesc_unique
    (q : idealSheafQuotientTower X K P ⟶ F)
    (hq : idealSheafQuotientTowerUnit X K P ≫ q = p) :
    q = compatibleQuotientDesc K hF p := by
  apply NatTrans.ext
  funext n
  apply (cancel_epi ((idealSheafQuotientUnit X (K ^ n.unop)).app P)).mp
  have hn := NatTrans.congr_app hq n
  change (idealSheafQuotientUnit X (K ^ n.unop)).app P ≫ q.app n = p.app n at hn
  change (idealSheafQuotientUnit X (K ^ n.unop)).app P ≫ q.app n =
    (idealSheafQuotientUnit X (K ^ n.unop)).app P ≫
      idealSheafQuotientDesc X (K ^ n.unop) (p.app n) (hF n.unop)
  rw [idealSheafQuotientUnit_desc]
  exact hn

/-- A surjective generator map remains an epimorphism after its canonical
factor through the corresponding quotient. -/
instance compatibleQuotientDesc_app_epi (n : ℕᵒᵖ) [Epi (p.app n)] :
    Epi ((compatibleQuotientDesc K hF p).app n) := by
  apply epi_of_epi_fac (f := (idealSheafQuotientUnit X (K ^ n.unop)).app P)
    (h := p.app n)
  exact idealSheafQuotientUnit_desc X (K ^ n.unop) (p.app n) (hF n.unop)

variable [IsLocallyNoetherian X]

/-- Compatible maps from a coherent algebraic coefficient into a coherent
formal system induce a morphism from its actual completion. -/
def completionDesc (P : X.CoherentSheaf) (F : AdicSystem X K)
    (p : (Functor.const ℕᵒᵖ).obj P.obj ⟶ F.obj) :
    (completionFunctor X K).obj P ⟶ F :=
  ObjectProperty.homMk (compatibleQuotientDesc K F.property.annihilated p)

end AlgebraicGeometry.Scheme.Modules.Coherent
