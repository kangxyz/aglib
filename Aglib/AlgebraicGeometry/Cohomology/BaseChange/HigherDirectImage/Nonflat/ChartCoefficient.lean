/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.RestrictPullback

/-!
# Original coefficient arrows on commuting open charts

Restriction of a geometric coefficient arrow is the native restriction
adjunction mate of its composite with the target restriction unit. Its unit
equation retains every original direct-image comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {X Y U V : Scheme.{u}}
  (p : Y ⟶ X) (a : U ⟶ X) (c : V ⟶ Y) (q : V ⟶ U)
  [IsOpenImmersion a] [IsOpenImmersion c] (w : q ≫ a = c ≫ p)
  {M : X.Modules} {N : Y.Modules} (ψ : M ⟶ (pushforward p).obj N)

/-- The original coefficient arrow on a pair of commuting open charts. -/
def chartCoefficient : M.restrict a ⟶ (pushforward q).obj (N.restrict c) :=
  ((restrictAdjunction a).homEquiv _ _).symm
    (ψ ≫ (pushforward p).map ((restrictAdjunction c).unit.app N) ≫
      (pushforwardComp c p).hom.app (N.restrict c) ≫
      (pushforwardCongr w.symm).hom.app (N.restrict c) ≫
      (pushforwardComp q a).inv.app (N.restrict c))

/-- The restricted coefficient retains exactly the original source and target restriction
units and the actual direct-image composition and equality comparisons. -/
@[reassoc]
theorem chartCoefficient_unit :
    (restrictAdjunction a).unit.app M ≫
        (pushforward a).map (chartCoefficient p a c q w ψ) =
      ψ ≫ (pushforward p).map ((restrictAdjunction c).unit.app N) ≫
        (pushforwardComp c p).hom.app (N.restrict c) ≫
        (pushforwardCongr w.symm).hom.app (N.restrict c) ≫
        (pushforwardComp q a).inv.app (N.restrict c) :=
  Equiv.apply_symm_apply ((restrictAdjunction a).homEquiv _ _) _

include w in
/-- The actual target chart open maps into the preimage of the actual source chart open. -/
theorem chartCoefficient_image_le (O : U.Opens) :
    c ''ᵁ (q ⁻¹ᵁ O) ≤ p ⁻¹ᵁ (a ''ᵁ O) := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨q z, hz, congrArg (fun t : V ⟶ X => t z) w⟩

/-- The chart coefficient is the original coefficient followed by the actual restriction
map of target sections. This formula uses no cohomology replacement. -/
theorem chartCoefficient_app (O : U.Opens) :
    (chartCoefficient p a c q w ψ).app O =
      ψ.app (a ''ᵁ O) ≫ N.presheaf.map (homOfLE (chartCoefficient_image_le p a c q w O)).op := by
  simp only [chartCoefficient, Adjunction.homEquiv_symm_apply, Hom.comp_app,
    restrictAdjunction_counit_app_app]
  change (ψ ≫ (pushforward p).map ((restrictAdjunction c).unit.app N) ≫
    (pushforwardComp c p).hom.app (N.restrict c) ≫
    (pushforwardCongr w.symm).hom.app (N.restrict c) ≫
    (pushforwardComp q a).inv.app (N.restrict c)).app (a ''ᵁ O) ≫ _ = _
  simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, Category.comp_id, Category.assoc]
  change ψ.app (a ''ᵁ O) ≫ N.presheaf.map _ ≫ N.presheaf.map _ ≫
    N.presheaf.map _ = _
  simp only [← Functor.map_comp]
  congr 1

/-- Restricting an actual coefficient arrow twice agrees with restricting to the composite
charts through the original restriction-composition comparisons. -/
theorem chartCoefficient_comp {U' V' : Scheme.{u}}
    (e : U' ⟶ U) (d : V' ⟶ V) (q' : V' ⟶ U')
    [IsOpenImmersion e] [IsOpenImmersion d] (w' : q' ≫ e = d ≫ q)
    (wo : q' ≫ (e ≫ a) = (d ≫ c) ≫ p) :
    (restrictFunctorComp e a).inv.app M ≫
        chartCoefficient p (e ≫ a) (d ≫ c) q' wo ψ ≫
        (pushforward q').map ((restrictFunctorComp d c).hom.app N) =
      chartCoefficient q e d q' w' (chartCoefficient p a c q w ψ) := by
  apply Scheme.Modules.hom_ext
  intro O
  have hi : (e ≫ a) ''ᵁ O = a ''ᵁ (e ''ᵁ O) := by simp
  have hn := ψ.mapPresheaf.naturality (eqToHom hi).op
  simp only [Hom.comp_app, chartCoefficient_app, restrictFunctorComp_inv_app_app,
    pushforward_map_app, restrictFunctorComp_hom_app_app, Category.assoc]
  change M.presheaf.map (eqToHom hi).op ≫ ψ.app ((e ≫ a) ''ᵁ O) ≫
    N.presheaf.map _ ≫ N.presheaf.map _ =
      ψ.app (a ''ᵁ (e ''ᵁ O)) ≫ N.presheaf.map _ ≫ N.presheaf.map _
  change M.presheaf.map (eqToHom hi).op ≫ ψ.app ((e ≫ a) ''ᵁ O) =
    ψ.app (a ''ᵁ (e ''ᵁ O)) ≫ N.presheaf.map _ at hn
  rw [reassoc_of% hn]
  change ψ.app (a ''ᵁ (e ''ᵁ O)) ≫ N.presheaf.map _ ≫ N.presheaf.map _ ≫
    N.presheaf.map _ = ψ.app (a ''ᵁ (e ''ᵁ O)) ≫ N.presheaf.map _ ≫ N.presheaf.map _
  simp only [← Functor.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.Modules.Nonflat
