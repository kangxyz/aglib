/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFaithful
public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomSection
public import Mathlib.AlgebraicGeometry.FunctionField
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.Nonzero` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`67a8b81dce4770ea9b27c0e163c4fd222328db370544292b431fafafe56d566e`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle dualLineBundle isLocallyRankOne_iff_local_unit)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap pullbackTensorMap_naturality tensorSheafLeftUnit tensorSheafMap)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Nonvanishing for genuine line-bundle maps

Actual pure tensors prove tensoring a zero map is zero. A genuine local unit
chart on an integral scheme proves the identity of a line bundle is nonzero;
monomorphisms out of it are therefore nonzero. The canonical transpose
remains nonzero after any scheme pullback under which the original map is
nonzero, by the actual tensor comparison and literal dual-evaluation square.
All arguments are proved; no additional mathematical theorem family occurs.
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable (X : Scheme.{u})
theorem tensorSheafMap_zero_left {M M' N N' : X.Modules} (b : N ⟶ N') :
    tensorSheafMap X (0 : M ⟶ M') b = 0 := by
  have h : PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      (0 : M ⟶ M').val b.val = 0 := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    change (0 : M'.val.obj U) ⊗ₜ b.val.app U n = 0
    simp
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (0 : M ⟶ M').val b.val) = 0
  rw [h, Functor.map_zero]

theorem lineBundle_id_ne_zero [IsIntegral X] (L : LineBundle X) : (𝟙 L.val) ≠ 0 := by
  intro h
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property (genericPoint X)
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  have hr := congrArg ((SheafOfModules.overFunctor X.ringCatSheaf U).map) h
  change (𝟙 L.val.over U) = 0 at hr
  have hu : (𝟙 (SheafOfModules.unit (X.ringCatSheaf.over U))) = 0 := by
    have hh := congrArg (fun k ↦ e.inv ≫ k ≫ e.hom) hr
    erw [Category.id_comp, Iso.inv_hom_id] at hh
    simpa only [comp_zero, zero_comp] using hh
  have he := congrArg (fun k : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U) ↦
      k.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X,U))) hu
  change (1 : Γ(X,U)) = 0 at he
  exact one_ne_zero he

theorem lineBundleMap_ne_zero_of_mono [IsIntegral X] (L : LineBundle X) {N : X.Modules}
    (φ : (show X.Modules from L.val) ⟶ N) [Mono φ] : φ ≠ 0 := by
  intro h
  apply lineBundle_id_ne_zero X L
  apply (cancel_mono φ).mp
  simp [h]

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X) (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit
    X.ringCatSheaf))
theorem transpose_pullback_ne_zero
    (hφ : (Scheme.Modules.pullback g).map φ ≠ 0) :
    (Scheme.Modules.pullback g).map (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X
        φ) ≠ 0 := by
  intro h
  have ht := pullbackTensorMap_naturality g
      (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ) (𝟙 L.val)
  haveI :=
      Scheme.Modules.Invertible.PullbackTensor.Local.pullbackTensorMap_isIso g (dualLineBundle
          X L).val L.val
    (dualLineBundle X L).property
  have hz : (Scheme.Modules.pullback g).map
      (tensorSheafMap X (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ) (𝟙 L.val))
          = 0 := by
    apply (cancel_mono (pullbackTensorMap g (dualLineBundle X L).val L.val)).mp
    rw [zero_comp]
    exact ht.trans (by rw [h, tensorSheafMap_zero_left, comp_zero])
  have he := congrArg ((Scheme.Modules.pullback g).map)
      (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose_dualEvaluation X L φ)
  simp only [CategoryTheory.Functor.map_comp, hz, zero_comp] at he
  apply hφ
  apply (cancel_epi ((Scheme.Modules.pullback g).map (tensorSheafLeftUnit X L.val).hom)).mp
  simpa using he.symm
end AlgebraicGeometry.Scheme.Modules.Invertible
