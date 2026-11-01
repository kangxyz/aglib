/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Complete scalar-mate comparison with the original whole-space objects

The original source index map, coefficient transfer, two whole-space
isomorphisms and global tensor map are retained together. The lower raw map
is the original adjunction mate of the same composite, not a replacement map.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped ChangeOfRings

universe u w

namespace ModuleCat

/-- The complete data of the original scalar mate and its top comparison. -/
structure TensorTopComparison {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S) where
  sourceRaw : ModuleCat.{max u w} R
  sourceOpen : ModuleCat.{max u w} R
  sourceGlobal : ModuleCat.{max u w} R
  targetOpen : ModuleCat.{max u w} S
  targetGlobal : ModuleCat.{max u w} S
  sourceIndex : sourceRaw ⟶ sourceOpen
  coefficientMap : sourceOpen ⟶ (restrictScalars σ).obj targetOpen
  sourceTop : sourceOpen ≅ sourceGlobal
  targetTop : targetOpen ≅ targetGlobal
  globalTensor : (extendScalars σ).obj sourceGlobal ⟶ targetGlobal
  top_fac : ((extendRestrictScalarsAdj.{max u w, u, u} σ).homEquiv _ _).symm
      coefficientMap ≫ targetTop.hom = (extendScalars σ).map sourceTop.hom ≫ globalTensor

namespace TensorTopComparison

variable {R S : Type u} [CommRing R] [CommRing S] {σ : R →+* S}

/-- Construct the whole comparison from its specified original objects and maps. -/
def ofMaps (A B C : ModuleCat.{max u w} R) (D E : ModuleCat.{max u w} S)
    (j : A ⟶ B) (η : B ⟶ (restrictScalars σ).obj D) (eA : B ≅ C) (eB : D ≅ E)
    (δ : (extendScalars σ).obj C ⟶ E)
    (h : ((extendRestrictScalarsAdj.{max u w, u, u} σ).homEquiv B D).symm η ≫ eB.hom =
      (extendScalars σ).map eA.hom ≫ δ) : TensorTopComparison σ where
  sourceRaw := A
  sourceOpen := B
  sourceGlobal := C
  targetOpen := D
  targetGlobal := E
  sourceIndex := j
  coefficientMap := η
  sourceTop := eA
  targetTop := eB
  globalTensor := δ
  top_fac := h

/-- The unchanged raw lower edge is the mate of the original indexed transfer. -/
def bottom (d : TensorTopComparison.{u, w} σ) :
    (extendScalars σ).obj d.sourceRaw ⟶ d.targetOpen :=
  ((extendRestrictScalarsAdj.{max u w, u, u} σ).homEquiv _ _).symm
    (d.sourceIndex ≫ d.coefficientMap)

/-- Compare that same lower edge with the original global tensor map. -/
theorem fac (d : TensorTopComparison.{u, w} σ) :
    d.bottom ≫ d.targetTop.hom =
      (extendScalars σ).map (d.sourceIndex ≫ d.sourceTop.hom) ≫ d.globalTensor := by
  let adj := extendRestrictScalarsAdj.{max u w, u, u} σ
  calc
    _ = ((extendScalars σ).map d.sourceIndex ≫
        (adj.homEquiv _ _).symm d.coefficientMap) ≫ d.targetTop.hom :=
      congrArg (fun f => f ≫ d.targetTop.hom)
        (adj.homEquiv_naturality_left_symm d.sourceIndex d.coefficientMap)
    _ = (extendScalars σ).map d.sourceIndex ≫
        ((extendScalars σ).map d.sourceTop.hom ≫ d.globalTensor) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f => (extendScalars σ).map d.sourceIndex ≫ f) d.top_fac)
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ d.globalTensor)
        ((extendScalars σ).map_comp d.sourceIndex d.sourceTop.hom).symm)

end TensorTopComparison
end ModuleCat
