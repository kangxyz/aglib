/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.TensorProduct.Domain
public import Aglib.AlgebraicGeometry.Geometrically.Connected.CommonOverfield

/-!
# Connectedness under arbitrary field extensions of an algebraically closed field

Scratch B02 FE-04 implementation, repository basis
`1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e`; Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
The field fibre is a tensor-product spectrum of a proved domain, and Mathlib's
open-map and connected-fibre theorems apply to every scheme over the field.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Algebra.TensorProduct
open scoped _root_.TensorProduct

namespace AlgebraicGeometry.Scheme.Geometrically
universe u

/-- An arbitrary extension field of an algebraically closed field has a
geometrically connected spectrum. No algebraicity or finiteness is assumed. -/
theorem fieldSpec_geometricallyConnected
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Z : Scheme.{u} => ConnectedSpace Z) (R := k)
    (f := Spec.map (CommRingCat.ofHom (algebraMap k K)))).mpr
  intro L _ _
  let := tensorProduct_isDomain k K L
  rw [(pullbackSpecIso k K L).hom.homeomorph.connectedSpace_iff]
  infer_instance

/-- Base change by any extension of an algebraically closed field preserves
connectedness for an arbitrary scheme, via the actual open projection with
geometrically connected fibres. -/
theorem connectedSpace_fieldBaseChange
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k)) [ConnectedSpace Y] :
    ConnectedSpace
      (Limits.pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) := by
  let := fieldSpec_geometricallyConnected k K
  infer_instance

/-- Connectedness over the chosen algebraic closure implies connectedness over
every extension field. The common overfield is the latter field's algebraic
closure, and both projection comparisons are actual pullback isomorphisms. -/
theorem connectedSpace_extension_of_connected_algebraicClosure
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of F))
    (h : ConnectedSpace (Limits.pullback q
      (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))) : Scheme.{u})) :
    ConnectedSpace
      (Limits.pullback q (Spec.map (CommRingCat.ofHom (algebraMap F K))) : Scheme.{u}) := by
  let e := commonClosureEmbedding F K
  let : Algebra (AlgebraicClosure F) (AlgebraicClosure K) := e.toRingHom.toAlgebra
  let bF : Spec (CommRingCat.of (AlgebraicClosure F)) ⟶ Spec (CommRingCat.of F) :=
    Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))
  let bK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) :=
    Spec.map (CommRingCat.ofHom (algebraMap F K))
  let c : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶
      Spec (CommRingCat.of (AlgebraicClosure F)) :=
    Spec.map (CommRingCat.ofHom e.toRingHom)
  let d : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have hcomp : c ≫ bF = d ≫ bK := by
    dsimp [c, bF, d, bK]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg (fun f : F →+* AlgebraicClosure K => f x)
      (commonClosureEmbedding_compatible F K)
  have h₁ : ConnectedSpace (Limits.pullback (Limits.pullback.snd q bF) c : Scheme.{u}) := by
    let := h
    exact connectedSpace_fieldBaseChange (AlgebraicClosure F) (AlgebraicClosure K)
      (Limits.pullback.snd q bF)
  have hFL : ConnectedSpace (Limits.pullback q (c ≫ bF) : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso q bF c).hom.homeomorph.connectedSpace_iff.mp h₁
  have hKL : ConnectedSpace (Limits.pullback q (d ≫ bK) : Scheme.{u}) := hcomp ▸ hFL
  have h₂ : ConnectedSpace (Limits.pullback (Limits.pullback.snd q bK) d : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso q bK d).hom.homeomorph.connectedSpace_iff.mpr hKL
  exact connectedSpace_of_fieldBaseChange (Limits.pullback.snd q bK) d h₂

/-- For every field and every scheme over it, connectedness of the actual
algebraic-closure base change detects geometric connectedness. -/
theorem geometricallyConnected_of_connected_algebraicClosure
    (F : Type u) [Field F] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of F))
    (h : ConnectedSpace (Limits.pullback q
      (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))) : Scheme.{u})) :
    GeometricallyConnected q := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Z : Scheme.{u} => ConnectedSpace Z) (R := F) (f := q)).mpr
  intro K _ _
  exact connectedSpace_extension_of_connected_algebraicClosure F K q h

end AlgebraicGeometry.Scheme.Geometrically
