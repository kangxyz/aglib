/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Cycles
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology

/-!
# The followed homology unit and the original restriction map

The original middle component of a coefficient map determines its map on cycles.
The original cycle projections then identify the followed adjunction homology
unit with the homology of that same coefficient map. No new homology model is
chosen, and the left adjoint need not preserve homology.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [G.PreservesHomology]

/-- The followed original homology mate is the homology of the actual restriction
map, provided its middle component is the original adjunction unit. -/
theorem homologyComparison_followed_unit
    (adj : F ⊣ G) (S : ShortComplex C) (T : ShortComplex D)
    (δ : S.map F ⟶ T) (r : S ⟶ T.map G)
    (hr : r.τ₂ = adj.unit.app S.X₂ ≫ G.map δ.τ₂) :
    adj.unit.app S.homology ≫
        G.map (adj.homologyComparison S ≫ ShortComplex.homologyMap δ) =
      ShortComplex.homologyMap r ≫ (T.mapHomologyIso G).hom := by
  have hc : adj.cyclesUnitMap S δ =
      ShortComplex.cyclesMap r ≫ (T.mapCyclesIso G).hom := by
    apply (cancel_mono (G.map T.iCycles)).mp
    rw [cyclesUnitMap_iCycles, Category.assoc,
      ShortComplex.mapCyclesIso_hom_iCycles, ShortComplex.cyclesMap_i, hr]
  apply (cancel_epi S.homologyπ).mp
  rw [homologyComparison_map_homologyπ,
    ← Category.assoc, ShortComplex.homologyπ_naturality]
  rw [Category.assoc, ShortComplex.homologyπ_mapHomologyIso_hom, hc]
  simp only [Category.assoc]

end CategoryTheory.Adjunction

namespace HomologicalComplex

open scoped TensorProduct ChangeOfRings

universe u v w uι

/-- On an actual unit pure tensor, followed scalar-extension homology is the
homology of the same original restriction complex map. -/
theorem extendScalarsHomologyMap_followed_one_tmul
    {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    {ι : Type uι} {c : ComplexShape ι} (σ : R →+* S)
    (K : HomologicalComplex (ModuleCat.{max v w} R) c)
    (L : HomologicalComplex (ModuleCat.{max v w} S) c)
    (δ : ((ModuleCat.extendScalars σ).mapHomologicalComplex c).obj K ⟶ L)
    (r : K ⟶ ((ModuleCat.restrictScalars σ).mapHomologicalComplex c).obj L)
    (n : ι)
    (hr : r.f n = (ModuleCat.extendRestrictScalarsAdj σ).unit.app (K.X n) ≫
      (ModuleCat.restrictScalars σ).map (δ.f n)) (z : K.homology n) :
    (extendScalarsHomologyMap σ K n ≫ homologyMap δ n) ((1 : S) ⊗ₜ[R,σ] z) =
      ((L.sc n).mapHomologyIso (ModuleCat.restrictScalars σ)).hom
        (homologyMap r n z) := by
  have h := (ModuleCat.extendRestrictScalarsAdj σ).homologyComparison_followed_unit
    (K.sc n) (L.sc n)
    ((shortComplexFunctor (ModuleCat.{max v w} S) c n).map δ)
    ((shortComplexFunctor (ModuleCat.{max v w} R) c n).map r) hr
  exact ConcreteCategory.congr_hom h z

end HomologicalComplex
