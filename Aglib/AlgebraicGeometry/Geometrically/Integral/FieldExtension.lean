/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.TensorProduct.Domain
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Integrality under extension of an algebraically closed ground field

The original spectrum of an arbitrary extension field is geometrically
integral: each field-valued fibre is the actual tensor-product spectrum,
and the tensor product is a proved domain. Native geometric integrality,
flatness and openness then show that every field base change of an integral
locally Noetherian scheme is integral. No finite degree, separability,
smoothness, or geometric-integrality hypothesis is inserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Algebra.TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Geometrically

universe u

/-- An arbitrary extension of an algebraically closed field has a genuinely
geometrically integral spectrum. Its field fibres are the original tensor
products of fields, which are domains. -/
theorem fieldSpec_geometricallyIntegral
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (fun Z : Scheme.{u} => IsIntegral Z) :=
    ⟨fun e h => by
      let := h
      exact IsIntegral.of_isIso e.hom⟩
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Z : Scheme.{u} => IsIntegral Z) (R := k)
    (f := Spec.map (CommRingCat.ofHom (algebraMap k K)))).mpr
  intro L _ _
  let := tensorProduct_isDomain k K L
  exact IsIntegral.of_isIso (pullbackSpecIso k K L).inv

/-- The literal field base change of an integral locally Noetherian scheme
over an algebraically closed field is integral. The extension field is
arbitrary, and need not itself be algebraically closed or algebraic. -/
theorem isIntegral_fieldBaseChange
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  let := fieldSpec_geometricallyIntegral k K
  infer_instance

end AlgebraicGeometry.Scheme.Geometrically
