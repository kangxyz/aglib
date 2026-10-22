/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPullback
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pullback

/-! # Original formal pullback commutes with coherent completion -/

@[expose] public noncomputable section

open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

local instance coefficient_isQuasicoherent (M : X.CoherentSheaf) : M.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (M.property R j).1)

omit [IsLocallyNoetherian Y] in
/-- Transition compatibility at the explicit quotient objects, before specialization
into the native tower. This keeps every unit and comparison under one typing. -/
theorem baseIdealPullbackQuotientIso_transition (M : X.CoherentSheaf)
    {m n : ℕ} (h : n ≤ m) :
    (pullback p).map (idealSheafQuotientMap X (idealThickeningIdealSheaf f I ^ m)
      (idealSheaf_pow_le X _ h) M.obj) ≫
        (baseIdealPullbackQuotientIso p f I M.obj n).hom =
      (baseIdealPullbackQuotientIso p f I M.obj m).hom ≫
        idealSheafQuotientMap Y (idealThickeningIdealSheaf (p ≫ f) I ^ m)
          (idealSheaf_pow_le Y _ h) ((pullback p).obj M.obj) := by
  apply (cancel_epi ((pullback p).map
    ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ m)).app M.obj))).mp
  rw [← Functor.map_comp_assoc, idealSheafQuotientUnit_map,
    baseIdealPullbackQuotientIso_unit]
  rw [← Category.assoc, baseIdealPullbackQuotientIso_unit,
    idealSheafQuotientUnit_map]

/-- The original completion diagrams compare on every actual quotient unit. -/
def baseIdealPullbackCompletionDiagramIso (M : X.CoherentSheaf) :
    idealSheafQuotientTower X (idealThickeningIdealSheaf f I) M.obj ⋙ pullback p ≅
      idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I)
        ((pullback p).obj M.obj) :=
  NatIso.ofComponents (fun n => baseIdealPullbackQuotientIso p f I M.obj n.unop) (by
    intro m n g
    exact baseIdealPullbackQuotientIso_transition p f I M (leOfHom g.unop))

/-- The comparison is an isomorphism in the original native formal category. -/
def baseIdealPullbackCompletionIso (M : X.CoherentSheaf) :
    (baseIdealPullbackFunctor p f I).obj ((completionFunctor X
      (idealThickeningIdealSheaf f I)).obj M) ≅
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj
      ((coherentPullback p).obj M) :=
  ObjectProperty.isoMk _ (baseIdealPullbackCompletionDiagramIso p f I M)

/-- Forgetting formal membership recovers the same whole diagram comparison. -/
theorem baseIdealPullbackCompletionIso_hom (M : X.CoherentSheaf) :
    (baseIdealPullbackCompletionIso p f I M).hom.hom =
      (baseIdealPullbackCompletionDiagramIso p f I M).hom := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent
