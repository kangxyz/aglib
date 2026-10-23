/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.PointedEvaluationBaseChange

/-! # Original pointed direct-image evaluation on actual geometric germs -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge
open CoefficientStalkBaseChange

variable {X S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The original unit followed by the original counit evaluates a direct-image
section at the actual pulled-back geometric point. -/
@[reassoc]
theorem germ_pointedDirectImageEvaluation (f : X ⟶ S)
    (x : Spec (.of Ω) ⟶ X) (s : Spec (.of Ω) ⟶ S) (hx : x ≫ f = s)
    (F : AbelianSheaf.{u, u + 1} X) (U : S.Etale)
    (p : Over.mk s ⟶ (Etale.forget S).obj U) :
    (pointSmallEtale s).toPresheafFiber U p ((directImage f).obj F).obj ≫
        pointedDirectImageEvaluation f x s hx F =
      (pointSmallEtale x).toPresheafFiber ((siteBaseChange f).obj U)
        (pointedPulledBackPoint f x s hx U p) F.obj := by
  let V := (siteBaseChange f).obj U
  let t := pointedPulledBackPoint f x s hx U p
  let L := (directImage f).obj F
  let ε := (inverseImageAdjunction f).counit.app F
  let g₀ := (pointSmallEtale s).toPresheafFiber U p L.obj
  let g₁ := (pointSmallEtale x).toPresheafFiber V t ((inverseImage f).obj L).obj
  let g₂ := (pointSmallEtale x).toPresheafFiber V t F.obj
  let a := ((inverseImageAdjunction f).unit.app L).hom.app (op U)
  let b := ε.hom.app (op V)
  let c := (pointSmallEtale x).sheafFiber.map ε
  let z := pointedStalkUnit f x L s hx
  have hu : g₀ ≫ z = a ≫ g₁ := germ_pointedStalkUnit f x L s hx U p
  have hn : g₁ ≫ c = b ≫ g₂ :=
    (pointSmallEtale x).toPresheafFiber_naturality ε.hom V t
  have ht : a ≫ b = 𝟙 _ := congrArg (fun k => k.hom.app (op U))
    ((inverseImageAdjunction f).right_triangle_components F)
  change g₀ ≫ z ≫ c = g₂
  exact (Category.assoc g₀ z c).symm.trans
    ((congrArg (fun k => k ≫ c) hu).trans
      ((Category.assoc a g₁ c).trans
        ((congrArg (fun k => a ≫ k) hn).trans
          ((Category.assoc a b g₂).symm.trans
            ((congrArg (fun k => k ≫ g₂) ht).trans (Category.id_comp g₂))))))

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
