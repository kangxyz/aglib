/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Descent.FieldOfDefinition.Presentation
public import Aglib.RingTheory.Descent.FieldOfDefinition.Etale
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineCoverAlgebra
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineCoverBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureAffine
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FieldLimit

/-!
# Actual finite-field-stage cover objects on affine tensor charts

The input is the previously constructed and frozen `finiteEtaleModel`.
This file begins the global cover-object descent assignment by passing its
actual tensor equivalence through Spec and the existing cover base-change functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TensorProduct
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
open AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Spec of an algebra equivalence, with its actual structural-map compatibility. -/
def specCoverIso {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Finite A B] [Algebra.Etale A B]
    [Module.Finite A C] [Algebra.Etale A C] (e : B ≃ₐ[A] C) :
    specCover A B ≅ specCover A C :=
  AffineDescent.specCoverIso e

variable (K Ω R : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω] [CommRing R] [Algebra K R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every finite étale cover of `Spec (R ⊗[K] Ω)` descends, as an actual cover
object, to `Spec (R ⊗[K] K(s))` for a finite subset `s` of Ω. -/
def tensorAffineCoverDescent (Y : Scheme.FiniteEtale (Spec (.of (R ⊗[K] Ω)))) :
    Σ s : Finset Ω, Σ Z : Scheme.FiniteEtale (Spec
      (.of (_root_.Algebra.Descent.FieldOfDefinition.stageRing K Ω R s))),
      (baseChange (Spec.algebraMap (_root_.Algebra.Descent.FieldOfDefinition.stageRing K Ω R s)
        (R ⊗[K] Ω))).obj Z ≅ Y := by
  let M := algebraModel Y
  let D := _root_.Algebra.Descent.FieldOfDefinition.finiteEtaleModel K Ω R M.algebra
  exact ⟨D.stage, specCover (_root_.Algebra.Descent.FieldOfDefinition.stageRing K Ω R D.stage)
    D.Model,
    PurelyInseparable.Global.specBaseChangeIso
      (_root_.Algebra.Descent.FieldOfDefinition.stageRing K Ω R D.stage) (R ⊗[K] Ω) D.Model ≪≫
      specCoverIso D.equiv ≪≫ M.coverIso⟩

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 419ec44ea29221064801f0076fef3f228453b5cbea9b515d08b20eed360a9a69.
Definitions, hypotheses and universes are retained modulo native names. -/
