/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.FieldExtensionArbitrary

/-! # Ordinary fibre bounds on all field-valued fibres

A field-valued point factors through the original residue field of its image.
The native iterated-pullback isomorphism identifies its fibre with a field
extension of the original ordinary fibre. The general finite-type dimension
bound therefore retains the same bound, without integrality or reducedness
of the fibres and without a Noetherian base hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

set_option backward.isDefEq.respectTransparency.types false in
/-- A bound on all original ordinary fibres bounds every field-valued fibre
of a locally finite-type morphism. The extending field can be arbitrary. -/
theorem Hom.geometricFiber_dimension_le_of_fiber_dimension_le
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (d : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ (d : ℕ))
    (K : Type u) [Field K] (η : Spec (.of K) ⟶ S) :
    topologicalKrullDim (pullback (C := Scheme) f η) ≤ (d : ℕ) := by
  let s := η (IsLocalRing.closedPoint K)
  let g : Spec (.of (S.residueField s)) ⟶ S := S.fromSpecResidueField s
  let : LocallyOfFiniteType (pullback.snd f g) :=
    MorphismProperty.pullback_snd f g inferInstance
  let a : Spec (.of K) ⟶ Spec (.of (S.residueField s)) :=
    Spec.map (descResidueField (Scheme.stalkClosedPointTo η))
  have ha : a ≫ g = η :=
    descResidueField_stalkClosedPointTo_fromSpecResidueField K S η
  have hbase : topologicalKrullDim (pullback (C := Scheme) (pullback.snd f g) a) ≤ (d : ℕ) :=
    ((pullback.snd f g).topologicalKrullDim_fieldBaseChange_le_of_finiteType a).trans (hdim s)
  have he := IsHomeomorph.topologicalKrullDim_eq _
    (pullbackLeftPullbackSndIso f g a ≪≫ pullback.congrHom rfl ha).hom.homeomorph.isHomeomorph
  exact he.symm.le.trans hbase

end AlgebraicGeometry.Scheme
