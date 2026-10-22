/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitObjects

/-!
# Lifting original covers through an actual inverse-limit description

Actual finite-etale object descent reduces lifting a cover of the original
fibre to lifting the pullbacks of stage covers. The fibre isomorphism and all
projection maps are retained in the statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

/-- Lift arbitrary original fibre covers by descending them to actual stages
and then using the specified stage lifts. This is a general reduction, not
an unconditional henselian comparison theorem. -/
theorem baseChange_essSurj_of_stage_lifts
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {s t} (g : s ⟶ t), IsAffineHom (D.map g)]
    [∀ s, CompactSpace (D.obj s)] [∀ s, QuasiSeparatedSpace (D.obj s)]
    (c : Cone D) (hc : IsLimit c)
    {K X : Scheme.{u}} (i : K ⟶ X) (e : K ≅ c.pt)
    (h : ∀ s (C : FiniteEtale (D.obj s)), ∃ W : FiniteEtale X,
      Nonempty ((baseChange i).obj W ≅
        (baseChange (e.hom ≫ c.π.app s)).obj C)) :
    (baseChange i).EssSurj where
  mem_essImage C := by
    obtain ⟨s, V, ⟨d⟩⟩ := exists_cover_of_isLimit D c hc ((baseChange e.inv).obj C)
    obtain ⟨W, ⟨hW⟩⟩ := h s V
    refine ⟨W, ⟨?_⟩⟩
    exact hW ≪≫ (baseChangeComp (c.π.app s) e.hom).app V ≪≫
      (baseChange e.hom).mapIso d ≪≫
        (baseChangeComp e.inv e.hom).symm.app C ≪≫
          (eqToIso (congrArg baseChange e.hom_inv_id)).app C ≪≫
            (baseChangeId K).app C

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
