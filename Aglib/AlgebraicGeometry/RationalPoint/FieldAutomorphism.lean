/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.RationalPoint.ExtensionSource

/-!
# The actual spectrum action of a coefficient-fixing field automorphism

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.PeriodDescent`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 103–119.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.OverField
universe u
variable {F K : Type u} [Field F] [Field K]
  (f : F →+* K) (σ : K ≃+* K) (hfix : σ.toRingHom.comp f = f)

/-- The actual action on Spec K over the fixed original base Spec F. -/
def extensionPointAutomorphism : extensionPointSource f ⟶ extensionPointSource f :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    exact congrArg (fun g : F →+* K => Spec.map (CommRingCat.ofHom g)) hfix)

include hfix in
lemma automorphism_fixes_image (x : F) : σ (f x) = f x :=
  DFunLike.congr_fun hfix x

@[simp] theorem extensionPointAutomorphism_left :
    (extensionPointAutomorphism f σ hfix).left = Spec.map (CommRingCat.ofHom σ.toRingHom) := rfl

end AlgebraicGeometry.Scheme.OverField
