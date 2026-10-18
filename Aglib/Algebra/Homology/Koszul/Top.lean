/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Basic
public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Elements

/-!
# Original ordered top frames of finite Koszul complexes

The highest term of the actual recursive tensor Koszul complex is the original
ring module. The frame uses the original shifted-column projection and keeps
the native inclusion equation. The empty list uses the original degree-zero
single isomorphism. No regularity, finiteness, Noetherian or nontrivial-ring
hypothesis is needed. These frames define the original top Ext cocycles.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

namespace ChainComplex.Koszul
variable {R : Type u} [CommRing R]

/-- The shifted top-column projection identifies the actual top term of a nonempty list. -/
def topComponentConsIso (a : R) (s : List R) :
    (chainComplex (a :: s)).X (s.length + 1) ≅ (chainComplex s).X s.length where
  hom := singleTensorπOne a (chainComplex s) s.length
  inv := singleTensorιOne a (chainComplex s) s.length
  hom_inv_id := by
    change singleTensorπOne a (chainComplex s) s.length ≫
        singleTensorιOne a (chainComplex s) s.length =
      𝟙 ((HomologicalComplex.tensorObj (singleComplex R a) (chainComplex s)).X
        (s.length + 1))
    have hz : singleTensorπZero a (chainComplex s) (s.length + 1) = 0 :=
      (isZero_X s (s.length + 1) (by omega)).eq_of_tgt _ _
    simpa only [hz, zero_comp, zero_add] using
      singleTensor_decomposition a (chainComplex s) s.length
  inv_hom_id := singleTensorιOne_πOne a (chainComplex s) s.length

/-- The ordered top term of the original tensor Koszul complex is the original ring module. -/
def topComponentIso : (s : List R) → (chainComplex s).X s.length ≅ ModuleCat.of R R
  | [] => HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
      (𝟙_ (ModuleCat R))
  | a :: s => topComponentConsIso a s ≪≫ topComponentIso s

/-- The original shifted-column inclusion preserves the ordered top frame. -/
@[reassoc]
theorem topComponentIso_cons (a : R) (s : List R) :
    (singleTensorιOne a (chainComplex s) s.length) ≫ (topComponentIso (a :: s)).hom =
      (topComponentIso s).hom := by
  change (singleTensorιOne a (chainComplex s) s.length) ≫
    (singleTensorπOne a (chainComplex s) s.length ≫ (topComponentIso s).hom) = _
  rw [← Category.assoc, singleTensorιOne_πOne, Category.id_comp]

end ChainComplex.Koszul
