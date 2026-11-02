/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MateHomEquiv
public import Mathlib.AlgebraicGeometry.Modules.Sheaf


/-!
# Original adjoints of composite module-pullback arrows

The original pullback-composition isomorphism is conjugate to the original
pushforward-composition isomorphism. Applying that native equality before
specializing coefficients retains the original structural units and arrows.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules


private theorem composite_adjoint {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {J : E ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ J) {M : C} {N : D} {P : E}
    (f : F.obj M ⟶ N) (g : H.obj N ⟶ P) :
    (adj₁.comp adj₂).homEquiv M P (H.map f ≫ g) =
      adj₁.homEquiv M N f ≫ G.map (adj₂.homEquiv N P g) := by
  rw [Adjunction.comp_homEquiv]
  exact (congrArg (adj₁.homEquiv M (J.obj P))
    (adj₂.homEquiv_naturality_left f g)).trans
      (adj₁.homEquiv_naturality_right f (adj₂.homEquiv N P g))

/-- The actual composed pullback arrow has its original composed coefficient adjoint. -/
theorem pullbackCompositeAdjoint {X Y Z : Scheme.{u}} (b : Y ⟶ X) (c : Z ⟶ Y)
    (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
    (f : (pullback b).obj M ⟶ N) (g : (pullback c).obj N ⟶ P) :
    (pullbackPushforwardAdjunction (c ≫ b)).homEquiv M P
      ((pullbackComp c b).inv.app M ≫ (pullback c).map f ≫ g) =
    (pullbackPushforwardAdjunction b).homEquiv M N f ≫
      (pushforward b).map ((pullbackPushforwardAdjunction c).homEquiv N P g) ≫
      (pushforwardComp c b).hom.app P := by
  let adj₁ := pullbackPushforwardAdjunction b
  let adj₂ := pullbackPushforwardAdjunction c
  have h := CategoryTheory.homEquiv_conjugate (adj₁.comp adj₂)
    (pullbackPushforwardAdjunction (c ≫ b)) (pullbackComp c b).inv
      ((pullback c).map f ≫ g)
  have hh := composite_adjoint adj₁ adj₂ f g
  have ht := congrArg (fun t => t.app P) (conjugateEquiv_pullbackComp_inv c b)
  exact h.trans ((congrArg (fun q => q ≫
    (conjugateEquiv (adj₁.comp adj₂) (pullbackPushforwardAdjunction (c ≫ b))
      (pullbackComp c b).inv).app P) hh).trans
      ((congrArg (fun q => (adj₁.homEquiv M N f ≫
        (pushforward b).map (adj₂.homEquiv N P g)) ≫ q) ht).trans
          (Category.assoc _ _ _)))

end AlgebraicGeometry.Scheme.Modules
