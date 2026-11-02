/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverGlobal
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitAutomorphisms
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisBaseChange
public import Aglib.CategoryTheory.Galois.FiberCompatibleReflection
public import Aglib.CategoryTheory.Galois.Iso
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Original Galois covers descend to an actual finite intermediate field

Object descent and simultaneous descent of the original automorphisms are
combined on the native finite-field diagram. Surjective field projections
derive source connectedness; fibre-compatible reflection preserves Galoisness
and the original deck order. No point, algebraic closure, or smoothness is an
input.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
open AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

universe u

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (.of K)) [GeometricallyConnected p]

local instance fieldGalois_limitConnected :
    ConnectedSpace (pullback p (Spec.algebraMap K Ω) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap K Ω))

local instance fieldGalois_stageConnected (s : Finset Ω) :
    ConnectedSpace (((FieldLimit.schemeDiagram K Ω p).obj (op s)).left) := by
  change ConnectedSpace
    (pullback (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p : Scheme.{u})
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (pullback.fst (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p)

/-- The original Galois cover descends to a native finite-field stage with
unchanged deck order and its actual original reconstruction isomorphism. -/
theorem exists_qcqs_galois_cover
    (Y : FiniteEtale (pullback p (Spec.algebraMap K Ω))) [IsGalois Y] :
    ∃ (s : Finset Ω)
      (Z : FiniteEtale (((FieldLimit.schemeDiagram K Ω p).obj (op s)).left)),
      IsGalois Z ∧ Nat.card (Aut Z) = Nat.card (Aut Y) ∧
        Nonempty ((baseChange (FieldLimit.fieldProjection K Ω p (op s))).obj Z ≅ Y) := by
  classical
  obtain ⟨s, Yi, ⟨e⟩⟩ := exists_qcqs_cover K Ω p Y
  let D := fieldSchemeDiagram K Ω p
  let c := standardFieldCone K Ω p
  let : ConnectedSpace c.pt :=
    inferInstanceAs (ConnectedSpace (pullback p (Spec.algebraMap K Ω) : Scheme.{u}))
  have {i j : (Finset Ω)ᵒᵖ} (a : i ⟶ j) : IsAffineHom (D.map a) :=
    inferInstanceAs (IsAffineHom ((FieldLimit.schemeDiagram K Ω p).map a).left)
  have (i : (Finset Ω)ᵒᵖ) : CompactSpace (D.obj i) := FieldLimit.stage_compact K Ω p i
  have (i : (Finset Ω)ᵒᵖ) : QuasiSeparatedSpace (D.obj i) :=
    FieldLimit.stage_quasiSeparated K Ω p i
  obtain ⟨j, k, hsurj⟩ := exists_iteratedCover_mapAut_surjective D c (op s) Yi
    (standardFieldConeIsLimit K Ω p) Y e
  let : ConnectedSpace (D.obj k.left) := fieldGalois_stageConnected K Ω p k.left.unop
  let Z := iteratedCover D (op s) Yi j k
  let b : c.pt ⟶ D.obj k.left := c.π.app k.left
  let E : (baseChange b).obj Z ≅ Y :=
    iteratedCoverIso D c (op s) Yi j k ≪≫ e
  let : Surjective b := fieldProjection_surjective K Ω p k.left.unop
  let : ConnectedSpace Y.obj.left := Connectedness.connectedSpace_of_categoricalConnected Y
  let eX : ((baseChange b).obj Z).obj.left ≅ Y.obj.left := (forgetToScheme c.pt).mapIso E
  let : ConnectedSpace ((baseChange b).obj Z).obj.left :=
    eX.inv.surjective.connectedSpace eX.inv.continuous
  let : ConnectedSpace (pullback Z.obj.hom b : Scheme.{u}) :=
    inferInstanceAs (ConnectedSpace ((baseChange b).obj Z).obj.left)
  let : ConnectedSpace Z.obj.left :=
    (pullback.fst Z.obj.hom b).surjective.connectedSpace (pullback.fst Z.obj.hom b).continuous
  let x := algebraicClosureResiduePoint c.pt
    (Classical.choice (inferInstance : Nonempty c.pt))
  let : IsGalois ((baseChange b).obj Z) := isGalois_of_iso (fiberToFinite x) E.symm
  have hraw : Function.Surjective (Functor.mapAut Z (baseChange b)) := by
    intro σ
    obtain ⟨ρ, hρ⟩ := hsurj (Aut.autMulEquivOfIso E σ)
    refine ⟨ρ, (Aut.autMulEquivOfIso E).injective ?_⟩
    exact hρ
  let : IsConnected Z := Connectedness.categoricalConnected_of_connectedSpace Z
  let : IsGalois Z := isGalois_of_fiberCompatible_of_mapAut_surjective
    (fiberToFinite (x ≫ b)) (fiberToFinite x) (baseChange b)
    (fiberToFiniteBaseChangeIso b x) Z hraw
  refine ⟨k.left.unop, Z, inferInstance, ?_, ⟨E⟩⟩
  exact (baseChange_card_aut_of_connected b Z).symm.trans
    (Nat.card_congr (Aut.autMulEquivOfIso E).toEquiv)

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
