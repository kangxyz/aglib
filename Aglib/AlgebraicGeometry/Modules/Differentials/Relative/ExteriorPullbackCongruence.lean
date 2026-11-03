/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Congruence
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient


/-!
# Structural equality for the original raw pullback arrow

Equality of structural morphisms gives the complete naturality square for the
same raw exterior pullback. The original differential congruence is retained;
equality induction uses its proved reflexivity, not a replacement comparison.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- The original raw pullback respects equality of the original structural maps. -/
theorem rawFormsPullback_congr {X Y T : Scheme.{u}} {a a' : X ⟶ T}
    (ha : a = a') (b : Y ⟶ X) (n : ℕ) :
    (pullback b).map
        ((moduleExteriorPowerFunctor X n).map
          (relativeDifferentialCongrIso a ha).hom) ≫
      rawFormsPullback a' b n =
    rawFormsPullback a b n ≫
      (moduleExteriorPowerFunctor Y n).map
        (relativeDifferentialCongrIso (b ≫ a)
          (congrArg (fun t => b ≫ t) ha)).hom := by
  cases ha
  rw [relativeDifferentialCongrIso_refl,
    relativeDifferentialCongrIso_refl]
  simp only [Iso.refl_hom]
  have hX := CategoryTheory.Functor.map_id (moduleExteriorPowerFunctor X n)
    (show X.Modules from relativeDifferentialSheaf a)
  have hY := CategoryTheory.Functor.map_id (moduleExteriorPowerFunctor Y n)
    (show Y.Modules from relativeDifferentialSheaf (b ≫ a))
  have hb := CategoryTheory.Functor.map_id (pullback b)
    (moduleExteriorPower X (relativeDifferentialSheaf a) n)
  exact (congrArg (fun z => (pullback b).map z ≫ rawFormsPullback a b n) hX).trans
    ((congrArg (fun z => z ≫ rawFormsPullback a b n) hb).trans
      ((Category.id_comp (rawFormsPullback a b n)).trans
        ((Category.comp_id (rawFormsPullback a b n)).symm.trans
          (congrArg (fun z => rawFormsPullback a b n ≫ z) hY.symm))))

end AlgebraicGeometry.Scheme.Modules.Differentials
