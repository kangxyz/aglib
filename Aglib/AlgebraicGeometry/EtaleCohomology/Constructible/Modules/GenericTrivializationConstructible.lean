/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericLocalConstancy
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericTrivializationDenseGalois

/-!
# Actual dense Galois trivialization of constructible module coefficients

The dense-open local-constancy supplier feeds the original connected Galois
trivialization. Composing its two actual open inclusions retains the original
module coefficient, finite module value, cover and pullback comparison.
This supplies the cover used in the curve dimension argument, without a
global finite-type local-constancy hypothesis on the original coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [Ring R]

/-- Every constructible native module sheaf on an integral scheme becomes
constant on an actual connected Galois finite etale cover of a dense affine open. -/
def denseGaloisConstantTrivializationOfConstructible
    {X : Scheme.{u}} [IsIntegral X] (F : ModuleSheaf R X) (hF : IsConstructible F) :
    DenseGaloisConstantTrivialization F := by
  apply Classical.choice
  obtain ⟨U, j, _, hj, hjdense, hU, hFj⟩ :=
    exists_dense_affine_open_isFiniteTypeLocallyConstant F hF
  have : IsOpenImmersion j := hj
  have : IsDominant j := hjdense
  have : IsIntegral U := hU
  let t := denseGaloisConstantTrivialization ((moduleInverseImage R j).obj F) hFj
  have : IsOpenImmersion t.inclusion := t.open_inclusion
  have : IsDominant t.inclusion := t.dense_inclusion
  refine ⟨{ base := t.base
            inclusion := t.inclusion ≫ j
            affine_base := t.affine_base
            open_inclusion := inferInstance
            dense_inclusion := inferInstance
            connected_base := t.connected_base
            cover := t.cover
            galois_cover := t.galois_cover
            connected_cover := t.connected_cover
            surjective_cover := t.surjective_cover
            value := t.value
            finite_value := t.finite_value
            iso := ?_ }⟩
  exact eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F)
      (Category.assoc t.cover.obj.hom t.inclusion j).symm) ≪≫
    (moduleInverseImageComp R j (t.cover.obj.hom ≫ t.inclusion)).app F ≪≫ t.iso

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
