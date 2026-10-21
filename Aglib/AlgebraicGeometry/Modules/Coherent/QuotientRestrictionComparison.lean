/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Restricting original quotient comparison isomorphisms -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

variable {X U V : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X) (t : V ⟶ U)
  [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion t]
  (h : t ≫ j = k) {M G : X.Modules}
  {QU : U.Modules} {QV : V.Modules}

/-- The comparison on a smaller chart is induced by the original larger-chart
comparison and the specified actual local restriction isomorphism. -/
def quotientRestrictionComparison (e : G.restrict j ≅ QU) (d : QU.restrict t ≅ QV) :
    G.restrict k ≅ QV :=
  (((restrictFunctorComp t j).symm ≪≫ restrictFunctorCongr h).app G).symm ≪≫
    (restrictFunctor t).mapIso e ≪≫ d

/-- The induced smaller-chart comparison retains the original quotient map. -/
@[reassoc]
theorem quotientRestrictionComparison_quotient
    (p : M ⟶ G) (qU : M.restrict j ⟶ QU) (qV : M.restrict k ⟶ QV)
    (e : G.restrict j ≅ QU) (d : QU.restrict t ≅ QV)
    (he : (restrictFunctor j).map p ≫ e.hom = qU)
    (hd : (restrictFunctor t).map qU ≫ d.hom =
      (((restrictFunctorComp t j).symm ≪≫ restrictFunctorCongr h).app M).hom ≫ qV) :
    (restrictFunctor k).map p ≫ (quotientRestrictionComparison j k t h e d).hom = qV := by
  let r := (restrictFunctorComp t j).symm ≪≫ restrictFunctorCongr h
  have hn := r.hom.naturality p
  dsimp only [Functor.comp_map] at hn
  apply (cancel_epi (r.hom.app M)).mp
  change r.hom.app M ≫ ((restrictFunctor k).map p ≫
    (r.inv.app G ≫ (restrictFunctor t).map e.hom ≫ d.hom)) = r.hom.app M ≫ qV
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, he]
  exact hd

end AlgebraicGeometry.Scheme.Modules
