/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ProjectiveTranslation
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.ProjectivePinching

/-!
# Pinching the same split singular Weierstrass cubic

Source: frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`IntrinsicSplitNode/ValueOne.lean`, lines 301–341.
SHA-256: `456fa148ece80652b570110e61ff7aa374ea52a4d46f3e703d0d2239f1120acf`.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.PinchedLine
/-- The literal standard-origin section in the original infinity pushout chart. -/
abbrev infinitySection (k : Type u) [Field k] : Spec (.of k) ⟶ pinchedGluing k :=
  Spec.map (CommRingCat.ofHom (WeierstrassCurve.CriticalCubic.AdaptedInfinity.standardOrigin k)) ≫
    pushout.inr (gluingToNode k) (gluingToInfinity k)
end AlgebraicGeometry.Scheme.PinchedLine
namespace WeierstrassCurve.Projective.SplitNode
variable (k : Type u) [Field k] (W : WeierstrassCurve k) (x y r s : k)
  (he : W.toAffine.Equation x y)
  (hx : W.toAffine.polynomialX.evalEval x y = 0)
  (hy : W.toAffine.polynomialY.evalEval x y = 0)
  (hne : r ≠ s)
  (hr : r ^ 2 + W.a₁ * r - (W.a₂ + 3 * x) = 0)
  (hs : s ^ 2 + W.a₁ * s - (W.a₂ + 3 * x) = 0)

/-- The original projective equation is pinched through its actual singular point. -/
def originalIsoPinchedOver : Over.mk (structureMap W) ≅
    Over.mk (Scheme.PinchedLine.pinchedStructure k) :=
  Translation.originalToCriticalOverIso W x y he hx hy ≪≫
    CriticalCubic.ProjectivePinching.criticalIsoPinchedOver
      k W.a₁ (W.a₂ + 3 * x) r s hne hr hs

@[reassoc] theorem originalIsoPinchedOver_structure :
    (originalIsoPinchedOver k W x y r s he hx hy hne hr hs).hom.left ≫
      Scheme.PinchedLine.pinchedStructure k = structureMap W :=
  (originalIsoPinchedOver k W x y r s he hx hy hne hr hs).hom.w

@[reassoc] theorem originalIsoPinchedOver_infinity :
    infinitySection W ≫ (originalIsoPinchedOver k W x y r s he hx hy hne hr hs).hom.left =
      Scheme.PinchedLine.infinitySection k := by
  change infinitySection W ≫
    ((Translation.originalToCriticalOverIso W x y he hx hy).hom.left ≫
      (CriticalCubic.ProjectivePinching.pinchedIsoCritical
        k W.a₁ (W.a₂ + 3 * x) r s hne hr hs).inv) = _
  apply (cancel_mono (CriticalCubic.ProjectivePinching.pinchedIsoCritical
    k W.a₁ (W.a₂ + 3 * x) r s hne hr hs).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Translation.originalToCriticalOverIso_infinity]
  exact (CriticalCubic.ProjectivePinching.pinchedToCritical_infinity_section
    k W.a₁ (W.a₂ + 3 * x) r s hne hr hs).symm
end WeierstrassCurve.Projective.SplitNode
end
