/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalRestriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.UnitComparisons

/-! # Actual open pullback of completion for an arbitrary ideal sheaf

The comparison uses the original quotient units at every order. It supplies
restriction of bounded reconstruction triples without assuming that a chart
ideal is extended from a fixed base ring.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsOpenImmersion p] (K : X.IdealSheafData)

local instance coefficient_isQuasicoherent (M : X.CoherentSheaf) : M.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (M.property R j).1)

omit [IsLocallyNoetherian Y] in
/-- Every transition retains the actual quotient-unit comparison. -/
theorem openIdealPullbackQuotientIso_transition (M : X.CoherentSheaf)
    {m n : ℕ} (h : n ≤ m) :
    (pullback p).map (idealSheafQuotientMap X (K ^ m)
      (idealSheaf_pow_le X K h) M.obj) ≫ (openIdealPullbackQuotientIso p K M.obj n).hom =
    (openIdealPullbackQuotientIso p K M.obj m).hom ≫
      idealSheafQuotientMap Y (K.comap p ^ m)
        (idealSheaf_pow_le Y (K.comap p) h) ((pullback p).obj M.obj) := by
  apply (cancel_epi ((pullback p).map
    ((idealSheafQuotientUnit X (K ^ m)).app M.obj))).mp
  rw [← Functor.map_comp_assoc, idealSheafQuotientUnit_map,
    openIdealPullbackQuotientIso_unit]
  rw [← Category.assoc, openIdealPullbackQuotientIso_unit,
    idealSheafQuotientUnit_map]

/-- The original completion diagram under actual open pullback. -/
def openIdealPullbackCompletionDiagramIso (M : X.CoherentSheaf) :
    idealSheafQuotientTower X K M.obj ⋙ pullback p ≅
      idealSheafQuotientTower Y (K.comap p) ((pullback p).obj M.obj) :=
  NatIso.ofComponents (fun n => openIdealPullbackQuotientIso p K M.obj n.unop) (by
    intro m n g
    exact openIdealPullbackQuotientIso_transition p K M (leOfHom g.unop))

/-- The formal comparison and all original units as one certificate. -/
def openIdealPullbackCompletionComparison (M : X.CoherentSheaf) :
    {e : (openIdealPullbackFunctor p K).obj ((completionFunctor X K).obj M) ≅
      (completionFunctor Y (K.comap p)).obj ((coherentPullback p).obj M) //
      ∀ n, (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app M.obj) ≫
        e.hom.hom.app (op n) =
        (idealSheafQuotientUnit Y (K.comap p ^ n)).app ((pullback p).obj M.obj)} :=
  formalComparisonOfComponents
    ((openIdealPullbackFunctor p K).obj ((completionFunctor X K).obj M))
    ((completionFunctor Y (K.comap p)).obj ((coherentPullback p).obj M))
    ((pullback p).obj M.obj)
    (fun n => (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app M.obj))
    (fun n => (idealSheafQuotientUnit Y (K.comap p ^ n)).app
      ((pullback p).obj M.obj))
    (fun n => openIdealPullbackQuotientComparison p K M.obj n)
    (fun f => openIdealPullbackQuotientIso_transition p K M (leOfHom f.unop))

/-- Actual coherent completion commutes with original arbitrary-ideal formal
open pullback, without changing the formal category. -/
def openIdealPullbackCompletionIso (M : X.CoherentSheaf) :
    (openIdealPullbackFunctor p K).obj ((completionFunctor X K).obj M) ≅
      (completionFunctor Y (K.comap p)).obj ((coherentPullback p).obj M) :=
  (openIdealPullbackCompletionComparison p K M).val

/-- The original completion comparison retains each original quotient unit. -/
theorem openIdealPullbackCompletionIso_unit (M : X.CoherentSheaf) (n : ℕ) :
    (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app M.obj) ≫
      (openIdealPullbackCompletionIso p K M).hom.hom.app (op n) =
    (idealSheafQuotientUnit Y (K.comap p ^ n)).app ((pullback p).obj M.obj) :=
  (openIdealPullbackCompletionComparison p K M).property n

/-- The completion comparison retains the original coherent map as well. -/
theorem openIdealPullbackCompletionIso_naturality {M N : X.CoherentSheaf} (a : M ⟶ N) :
    (openIdealPullbackFunctor p K).map ((completionFunctor X K).map a) ≫
      (openIdealPullbackCompletionIso p K N).hom =
    (openIdealPullbackCompletionIso p K M).hom ≫
      (completionFunctor Y (K.comap p)).map ((coherentPullback p).map a) := by
  apply formalMap_square_of_units
    ((openIdealPullbackFunctor p K).map ((completionFunctor X K).map a))
    ((completionFunctor Y (K.comap p)).map ((coherentPullback p).map a))
    (openIdealPullbackCompletionIso p K M).hom
    (openIdealPullbackCompletionIso p K N).hom ((pullback p).map a.hom)
    (fun n => (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app M.obj))
    (fun n => (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app N.obj))
    (fun n => (idealSheafQuotientUnit Y (K.comap p ^ n)).app ((pullback p).obj M.obj))
    (fun n => (idealSheafQuotientUnit Y (K.comap p ^ n)).app ((pullback p).obj N.obj))
  · intro n
    change (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app M.obj) ≫
        (pullback p).map ((idealSheafQuotientFunctor X (K ^ n)).map a.hom) =
      (pullback p).map a.hom ≫
        (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app N.obj)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg ((pullback p).map)
      ((idealSheafQuotientUnit X (K ^ n)).naturality a.hom).symm
  · intro n
    exact ((idealSheafQuotientUnit Y (K.comap p ^ n)).naturality
      ((pullback p).map a.hom)).symm
  · exact openIdealPullbackCompletionIso_unit p K M
  · exact openIdealPullbackCompletionIso_unit p K N

end AlgebraicGeometry.Scheme.Modules.Coherent
