/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.BinaryGluing
public import Aglib.AlgebraicGeometry.Limits.OpenCover
public import Aglib.CategoryTheory.Limits.Equifibered

/-!
# Limits of actual binary open gluings

The native pointwise pushout cone is limiting whenever the two chart cones
are limiting and all displayed overlap squares are cartesian. The proof
checks the actual cone over an open cover of one stage. It does not assume
that the glued diagram has a limit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u v w

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.BinaryGluing

attribute [local instance] IsCofiltered.isConnected

variable {I : Type v} [Category.{w} I] [IsCofiltered I]
  {W U V : I ⥤ Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
  [∀ i, IsOpenImmersion (f.app i)] [∀ i, IsOpenImmersion (g.app i)]
  (hf : f.Equifibered) (hg : g.Equifibered)
  (cW : Cone W) (cU : Cone U) (cV : Cone V)
  (f₀ : cW.pt ⟶ cU.pt) (g₀ : cW.pt ⟶ cV.pt)
  [IsOpenImmersion f₀] [IsOpenImmersion g₀]
  (hf₀ : ∀ i, f₀ ≫ cU.π.app i = cW.π.app i ≫ f.app i)
  (hg₀ : ∀ i, g₀ ≫ cV.π.app i = cW.π.app i ≫ g.app i)
  (Hf : ∀ i, IsPullback (cW.π.app i) f₀ (f.app i) (cU.π.app i))
  (Hg : ∀ i, IsPullback (cW.π.app i) g₀ (g.app i) (cV.π.app i))

/-- The original open-pushout cone is a limit, with its native projections.
Only the two chart cones need independent limit certificates. -/
def isLimitCone (hcU : IsLimit cU) (hcV : IsLimit cV) :
    IsLimit (cone f g cW cU cV f₀ g₀ hf₀ hg₀) := by
  let i : I := Classical.choice IsCofiltered.nonempty
  let c := cone f g cW cU cV f₀ g₀ hf₀ hg₀
  have hlocal : IsLimit ((Over.conePost (diagram f g) i).obj c) := by
    apply Scheme.Cover.isLimit_of_pullback
      (OpenNormalizationGluing.twoChartCover (f.app i) (g.app i))
    intro a
    cases a
    · exact NatTrans.Equifibered.isLimit_overPullbackCone (left f g)
        (left_equifibered f g hg) cU hcU c (pushout.inl f₀ g₀)
        (fun j => cone_inl_isPullback f g cW cU cV f₀ g₀ hf₀ hg₀ j (Hg j)) i
    · exact NatTrans.Equifibered.isLimit_overPullbackCone (right f g)
        (right_equifibered f g hf) cV hcV c (pushout.inr f₀ g₀)
        (fun j => cone_inr_isPullback f g cW cU cV f₀ g₀ hf₀ hg₀ j (Hf j)) i
  exact (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c)
    (isLimitOfPreserves (Over.forget ((diagram f g).obj i)) hlocal)

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.BinaryGluing
