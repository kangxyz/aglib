/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.TensorFaithful` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5ad04648d836828bd7c027dceaf7f235e4d453fa24188b0b55adf4514835704d`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle isLocallyRankOne_iff_restrict_unit)
open _root_.AlgebraicGeometry.Scheme.Modules
  (tensorSheaf tensorSheafLeftUnit tensorSheafLeftUnit_tmul tensorSheafMap tensorSheafMap_comp
    tensorSheafMap_tmul tensorSheafUnit)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Tensoring with a line bundle detects zero

The unit calculation uses actual pure tensors and the actual left-unitor.
A global trivialization transports that calculation, and the canonical
restriction-tensor isomorphism transports it to each genuine local unit chart.
Sheaf separation detects zero from these open-local restrictions. No added
mathematical theorem family is retained; the first factor is an actual line
bundle and the second factor is any actual module sheaf.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Incoming unconditional PullbackTensor/Local source SHA256:
82413655aa5481197b6c45951e52b6dfe77faa4bbb9acc5a67f13eb9c17a602e.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable (X : Scheme.{u})
theorem eq_zero_of_local_restrict {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (Scheme.Modules.restrictFunctor U.ι).map φ = 0) :
    φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  change φ.app V m = 0
  have hc : Presheaf.equalizerSieve (F := N.val.presheaf) (φ.app V m) 0 ∈
      (Opens.grothendieckTopology X) V := by
    intro x hxV
    obtain ⟨U, hxU, hU⟩ := h x
    have ho : (SheafOfModules.overFunctor X.ringCatSheaf U).map φ = 0 := by
      apply (Scheme.Modules.overEquiv U).functor.map_injective
      rw [Functor.map_zero]
      apply (cancel_mono ((Scheme.Modules.overFunctorEquiv U).hom.app N)).mp
      rw [zero_comp]
      change (SheafOfModules.overFunctor X.ringCatSheaf U ⋙
        (Scheme.Modules.overEquiv U).functor).map φ ≫ _ = _
      rw [(Scheme.Modules.overFunctorEquiv U).hom.naturality, hU, comp_zero]
    let A := U ⊓ V
    let p : A ⟶ V := homOfLE inf_le_right
    let A' : Over U := Over.mk (homOfLE (show A ≤ U from inf_le_left))
    refine ⟨A, p, ?_, hxU, hxV⟩
    have he := congrArg (fun k : (SheafOfModules.overFunctor X.ringCatSheaf U).obj M ⟶
        (SheafOfModules.overFunctor X.ringCatSheaf U).obj N ↦
        k.val.app (op A') (M.val.map p.op m)) ho
    change φ.app A (M.val.map p.op m) = 0 at he
    change N.val.map p.op (φ.app V m) = N.val.map p.op 0
    rw [map_zero]
    exact (PresheafOfModules.naturality_apply φ.val p.op m).symm.trans he
  apply N.isSheaf.isSeparated V _ hc
  intro W j hj
  exact hj

theorem tensorSheafMap_unit_detects_zero {N N' : X.Modules} (φ : N ⟶ N')
    (h : tensorSheafMap X (𝟙 (SheafOfModules.unit X.ringCatSheaf)) φ = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  change φ.val.app (op V) m = 0
  have he := congrArg (fun k : (show X.Modules from tensorSheaf X
      (SheafOfModules.unit X.ringCatSheaf) N) ⟶ (show X.Modules from tensorSheaf X
      (SheafOfModules.unit X.ringCatSheaf) N') ↦
      k.val.app (op V) ((tensorSheafUnit X _ N).app (op V) ((1 : Γ(X,V)) ⊗ₜ m))) h
  rw [tensorSheafMap_tmul] at he
  change (tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) N').app (op V)
    ((1 : Γ(X,V)) ⊗ₜ φ.val.app (op V) m) = 0 at he
  have he' := congrArg ((tensorSheafLeftUnit X N').hom.val.app (op V)) he
  simpa only [tensorSheafLeftUnit_tmul, map_zero, one_smul] using he'

theorem tensorSheafMap_trivial_detects_zero {M N N' : X.Modules} (φ : N ⟶ N')
    (e : M ≅ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (h : tensorSheafMap X (𝟙 M) φ = 0) : φ = 0 := by
  apply tensorSheafMap_unit_detects_zero X φ
  have he := congrArg (fun k : (show X.Modules from tensorSheaf X M N) ⟶
      (show X.Modules from tensorSheaf X M N') ↦
      tensorSheafMap X e.inv (𝟙 N) ≫ k ≫ tensorSheafMap X e.hom (𝟙 N')) h
  simpa only [← Category.assoc, tensorSheafMap_comp, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id, comp_zero, zero_comp] using he

theorem tensorSheafMap_lineBundle_detects_zero (L : LineBundle X) {N N' : X.Modules}
    (φ : N ⟶ N') (h : tensorSheafMap X (𝟙 L.val) φ = 0) : φ = 0 := by
  apply eq_zero_of_local_restrict X φ
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit L.val).mp L.property x
  refine ⟨U, hxU, ?_⟩
  apply tensorSheafMap_trivial_detects_zero U.toScheme _ e
  have hn := _root_.AlgebraicGeometry.Scheme.Modules.restrictTensorMap_naturality X U (𝟙 L.val) φ
  erw [CategoryTheory.Functor.map_id] at hn
  have := _root_.AlgebraicGeometry.Scheme.Modules.restrictTensorMap_isIso X U L.val N'
  apply (cancel_mono (_root_.AlgebraicGeometry.Scheme.Modules.restrictTensorMap X U L.val N')).mp
  rw [zero_comp]
  simpa only [CategoryTheory.Functor.map_id, h, Functor.map_zero, comp_zero] using hn
end AlgebraicGeometry.Scheme.Modules.Invertible
