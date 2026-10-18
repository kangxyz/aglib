/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Affine

/-! The spectrum equivalence respects actual field-valued point fibres.
For a separably closed base field its actual identity-point fibre is an
equivalence with finite types. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)

universe u
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

/-- The equivalence between `Ω`-valued points of `Spec A` over `Spec K` and
`K`-algebra homomorphisms `A →ₐ[K] Ω`. -/
def finiteEtaleAlgebraFiberEquiv (A : CommAlgCat.FiniteEtale.{u} K) :
    Fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      ((finiteEtaleSpecFunctor K).obj (op A)) ≃ (A →ₐ[K] Ω) where
  toFun p := ((algebraSpecOver K).preimage
    (X := op (CommAlgCat.of K Ω)) (Y := op A.obj) p).unop.hom
  invFun φ := (algebraSpecOver K).map (CommAlgCat.ofHom φ).op
  left_inv p := (algebraSpecOver K).map_preimage
    (X := op (CommAlgCat.of K Ω)) (Y := op A.obj) p
  right_inv φ := by
    change ((algebraSpecOver K).preimage (X := op (CommAlgCat.of K Ω)) (Y := op A.obj)
      ((algebraSpecOver K).map (CommAlgCat.ofHom φ).op)).unop.hom = φ
    rw [_root_.CategoryTheory.Functor.preimage_map]
    rfl

theorem finiteEtaleAlgebraFiberEquiv_naturality
    {A B : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ} (f : A ⟶ B)
    (p : Fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      ((finiteEtaleSpecFunctor K).obj A)) :
    finiteEtaleAlgebraFiberEquiv K Ω B.unop
        ((fiberToFinite (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).map
          ((finiteEtaleSpecFunctor K).map f) p) =
      (finiteEtaleAlgebraFiberEquiv K Ω A.unop p).comp f.unop.hom.hom := by
  change ((algebraSpecOver K).preimage
      (X := op (CommAlgCat.of K Ω)) (Y := op B.unop.obj)
      (p ≫ (algebraSpecOver K).map f.unop.hom.op)).unop.hom =
    (((algebraSpecOver K).preimage
      (X := op (CommAlgCat.of K Ω)) (Y := op A.unop.obj) p).unop.hom).comp f.unop.hom.hom
  erw [_root_.CategoryTheory.Functor.preimage_comp,
    _root_.CategoryTheory.Functor.preimage_map]
  rfl

/-- The natural isomorphism from the scheme fibre of the finite étale spectrum
functor to the algebra fibre functor `CommAlgCat.FiniteEtale.fiber K Ω`. -/
def finiteEtaleFieldFiberIso :
    finiteEtaleSpecFunctor K ⋙
      fiberToFinite (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≅
        CommAlgCat.FiniteEtale.fiber.{u} K Ω :=
  NatIso.ofComponents
    (fun A => FintypeCat.equivEquivIso (finiteEtaleAlgebraFiberEquiv K Ω A.unop))
    (fun {A B} f => by
      ext p
      exact finiteEtaleAlgebraFiberEquiv_naturality K Ω f p)

variable [IsSepClosed K]

instance instIsEquivalenceClosedFieldFiber :
    (fiberToFinite (𝟙 (Spec (CommRingCat.of K)))).IsEquivalence := by
  have hpoint : Spec.map (CommRingCat.ofHom (algebraMap K K)) =
      𝟙 (Spec (CommRingCat.of K)) := by
    change Spec.map (𝟙 (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K))
    exact Spec.map_id _
  have e := finiteEtaleFieldFiberIso K K
  rw [hpoint] at e
  have : (finiteEtaleSpecFunctor K ⋙
      fiberToFinite (𝟙 (Spec (CommRingCat.of K)))).IsEquivalence :=
    _root_.CategoryTheory.Functor.isEquivalence_of_iso e.symm
  exact _root_.CategoryTheory.Functor.isEquivalence_of_comp_left
    (finiteEtaleSpecFunctor K) (fiberToFinite (𝟙 (Spec (CommRingCat.of K))))

/-- The equivalence from finite étale covers of `Spec K` to finite types given by
the identity-point fibre functor, for the separably closed field `K`. -/
def closedFieldCoverEquivalence : Scheme.FiniteEtale (Spec (CommRingCat.of K)) ≌ FintypeCat.{u} :=
  (fiberToFinite (𝟙 (Spec (CommRingCat.of K)))).asEquivalence

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 149e5022dbee1a9cc64dad9a3f9d10bac46c8bc2657faac6f70374252634194e.
Definitions, hypotheses and universes are retained modulo native names. -/
