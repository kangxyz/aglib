/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic
public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Aglib.RingTheory.RootsOfUnity.FiniteCharacter

/-!
# Actual field restriction through geometric-fibre transport

Auxiliary field and coefficient naturality for
`K2-018#prop:k2018-arithmetic-characters` and
`K2-018#prop:k2018-integrality-test`, mathematical snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, expose SHA256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
Engineering input: the immutable 224-module snapshot inherited from the interrupted
Tate-localization phase, based on HEAD 7dcde130 plus the frozen monodromy leaves
(pending independent acceptance). Governing entry HEAD: b919ab59; Lean4.34.1/mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612.

The compatible closure embedding is constructed by the existing closed-point
lifting theorem. The field fundamental-group restriction is induced by actual
finite-cover pullback and the actual fibre comparison. The literal commuting
automorphism/embedding equation is derived by evaluating on finite subfield
covers, then cyclotomic compatibility follows from primitive-root evaluation.
No Galois restriction, character equality or basepoint identification is supplied.
The compatible closure embedding is chosen; independence of that choice is a
separate question for the normalized coefficient construction.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Group.BaseChange (scalarExtensionMap)

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Functor
open scoped CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv_left
  fiberToFinite fiberToFiniteBaseChangeIso)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldEmbeddingBaseChange
universe u
variable {F K : Type u} [Field F] [Field K] (i : F →+* K)

/-- The composite closed point of F induced by its actual field embedding into K. -/
abbrev extensionPoint := FieldGalois.geometricPoint K ≫ scalarExtensionMap i

/-- The compatible map of chosen algebraic closures is constructed from the actual point. -/
abbrev closureEmbedding : AlgebraicClosure F →+* AlgebraicClosure K :=
  (GeometricFibres.closedPointEmbedding F (AlgebraicClosure K) (extensionPoint i)).1

/-- Its compatibility with the original field embedding. -/
theorem closureEmbedding_comp :
    (closureEmbedding i).comp (algebraMap F (AlgebraicClosure F)) =
      (algebraMap K (AlgebraicClosure K)).comp i := by
  have h := (GeometricFibres.closedPointEmbedding F (AlgebraicClosure K) (extensionPoint i)).2
  simpa only [closureEmbedding, extensionPoint, FieldGalois.geometricPoint,
    EtaleFundamentalGroups.fieldPoint, scalarExtensionMap, ← Spec.map_comp, Spec.preimage_map,
      CommRingCat.hom_comp, CommRingCat.hom_ofHom] using h

/-- The actual scheme arrow between the two field-valued points. -/
abbrev closurePointArrow : Over.mk (extensionPoint i) ⟶ Over.mk (FieldGalois.geometricPoint F) :=
  GeometricFibres.closedPointArrow F (AlgebraicClosure K) (extensionPoint i)

@[simp] theorem closurePointArrow_left :
    (closurePointArrow i).left = Spec.map (CommRingCat.ofHom (closureEmbedding i)) := rfl

/-- Natural comparison of the actual global finite-cover fibre with the local pullback fibre. -/
def fieldFiberComparison :
    fiberToFinite (FieldGalois.geometricPoint F) ≅
      baseChange (scalarExtensionMap i) ⋙ fiberToFinite (FieldGalois.geometricPoint K) :=
  GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i) ≪≫
    fiberToFiniteBaseChangeIso (scalarExtensionMap i) (FieldGalois.geometricPoint K)

/-- The resulting actual continuous field-fundamental-group restriction. -/
def fieldRestriction : FieldGalois.FieldFundamentalGroup K →ₜ* FieldGalois.FieldFundamentalGroup
  F where
  __ := (Aut.autMulEquivOfIso (fieldFiberComparison i).symm).toMonoidHom.comp
    (((whiskeringLeft (Scheme.FiniteEtale (Spec (.of F)))
      (Scheme.FiniteEtale (Spec (.of K))) FintypeCat).obj
      (baseChange (scalarExtensionMap i))).mapAut (fiberToFinite (FieldGalois.geometricPoint K)))
  continuous_toFun := by
    rw [Topology.IsInducing.continuous_iff
      (PreGaloisCategory.autEmbedding_isClosedEmbedding
        (fiberToFinite (FieldGalois.geometricPoint F))).isInducing, continuous_pi_iff]
    intro Y
    change Continuous (fun a : FieldGalois.FieldFundamentalGroup K =>
      Aut.autMulEquivOfIso ((fieldFiberComparison i).app Y).symm
        (PreGaloisCategory.autEmbedding (fiberToFinite (FieldGalois.geometricPoint K)) a
          ((baseChange (scalarExtensionMap i)).obj Y)))
    exact continuous_of_discreteTopology.comp
      ((continuous_apply ((baseChange (scalarExtensionMap i)).obj Y)).comp continuous_induced_dom)

@[simp] theorem fieldRestriction_apply (γ : FieldGalois.FieldFundamentalGroup K)
    (Y : Scheme.FiniteEtale (Spec (.of F))) (q : Fiber (FieldGalois.geometricPoint F) Y) :
    (fieldRestriction i γ).hom.app Y q =
      (fieldFiberComparison i).inv.app Y
        (γ.hom.app ((baseChange (scalarExtensionMap i)).obj Y)
          ((fieldFiberComparison i).hom.app Y q)) := rfl

/-- The natural comparison is literal precomposition with the constructed closure arrow,
followed by the actual scheme pullback lift. -/
theorem fieldFiberComparison_hom_fst (Y : Scheme.FiniteEtale (Spec (.of F)))
    (q : Fiber (FieldGalois.geometricPoint F) Y) :
    ((fieldFiberComparison i).hom.app Y q).left ≫
      pullback.fst Y.obj.hom (scalarExtensionMap i) = (closurePointArrow i).left ≫ q.left := by
  change ((fiberToFiniteBaseChangeIso (scalarExtensionMap i) (FieldGalois.geometricPoint
    K)).hom.app Y
    ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app Y
      q)).left ≫ _ = _
  rw [finiteBaseChangeIso_hom_apply, fiberBaseChangeEquiv_left, pullback.lift_fst]
  rfl

/-- The constructed comparison intertwines the actual fibre actions. -/
theorem fieldFiberComparison_equivariant (γ : FieldGalois.FieldFundamentalGroup K)
    (Y : Scheme.FiniteEtale (Spec (.of F))) (q : Fiber (FieldGalois.geometricPoint F) Y) :
    (fieldFiberComparison i).hom.app Y ((fieldRestriction i γ).hom.app Y q) =
      γ.hom.app ((baseChange (scalarExtensionMap i)).obj Y) ((fieldFiberComparison i).hom.app Y
        q) := by
  rw [fieldRestriction_apply]
  exact ConcreteCategory.congr_hom ((fieldFiberComparison i).inv_hom_id_app Y) _

variable [CharZero F] [CharZero K]

/-- Actual restriction on absolute Galois groups through the proved field/fibre equivalences. -/
def absoluteRestriction : Field.absoluteGaloisGroup K →ₜ* Field.absoluteGaloisGroup F where
  __ := (FieldGalois.fundamentalGroupContinuousEquiv F).symm.toMonoidHom.comp
    ((fieldRestriction i).toMonoidHom.comp (FieldGalois.fundamentalGroupContinuousEquiv
      K).toMonoidHom)
  continuous_toFun := (FieldGalois.fundamentalGroupContinuousEquiv F).continuous_invFun.comp
    ((fieldRestriction i).continuous.comp (FieldGalois.fundamentalGroupContinuousEquiv
      K).continuous_toFun)

/-- The closure-arrow square holds on every actual finite-cover point. -/
theorem restriction_point_square (τ : Field.absoluteGaloisGroup K)
    (Y : Scheme.FiniteEtale (Spec (.of F))) (q : Fiber (FieldGalois.geometricPoint F) Y) :
    Spec.map (CommRingCat.ofHom (closureEmbedding i)) ≫
      Spec.map (CommRingCat.ofHom (FieldGalois.asAutomorphism F (absoluteRestriction i
        τ)).toRingHom) ≫ q.left =
    Spec.map (CommRingCat.ofHom (FieldGalois.asAutomorphism K τ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (closureEmbedding i)) ≫ q.left := by
  have h := congrArg (fun z : Fiber (FieldGalois.geometricPoint K)
      ((baseChange (scalarExtensionMap i)).obj Y) =>
        z.left ≫ pullback.fst Y.obj.hom (scalarExtensionMap i))
    (fieldFiberComparison_equivariant i (FieldGalois.fundamentalGroupContinuousEquiv K τ) Y q)
  rw [fieldFiberComparison_hom_fst] at h
  have hF := FieldGalois.fundamentalGroupContinuousEquiv_apply F (absoluteRestriction i τ) Y q
  have hFR : FieldGalois.fundamentalGroupContinuousEquiv F (absoluteRestriction i τ) =
      fieldRestriction i (FieldGalois.fundamentalGroupContinuousEquiv K τ) :=
    (FieldGalois.fundamentalGroupContinuousEquiv F).apply_symm_apply _
  rw [hFR] at hF
  rw [hF, FieldGalois.fundamentalGroupContinuousEquiv_apply] at h
  change Spec.map (CommRingCat.ofHom (closureEmbedding i)) ≫
    (Spec.map (CommRingCat.ofHom (FieldGalois.asAutomorphism F (absoluteRestriction i
      τ)).toRingHom) ≫ q.left) =
      (Spec.map (CommRingCat.ofHom (FieldGalois.asAutomorphism K τ).toRingHom) ≫
        ((fieldFiberComparison i).hom.app Y q).left) ≫ pullback.fst Y.obj.hom (scalarExtensionMap
          i) at h
  rw [Category.assoc, fieldFiberComparison_hom_fst, closurePointArrow_left] at h
  exact h

/-- Evaluating the actual finite-field cover gives the literal automorphism/embedding equation. -/
theorem absoluteRestriction_finite (τ : Field.absoluteGaloisGroup K)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L]
    (φ : L →ₐ[F] AlgebraicClosure F) (x : L) :
    closureEmbedding i (FieldGalois.asAutomorphism F (absoluteRestriction i τ) (φ x)) =
      FieldGalois.asAutomorphism K τ (closureEmbedding i (φ x)) := by
  have h := restriction_point_square i τ (FieldGalois.finiteFieldCover F L)
    (FieldGalois.fieldLift F L φ)
  change Spec.map (CommRingCat.ofHom (closureEmbedding i)) ≫
    Spec.map (CommRingCat.ofHom (FieldGalois.asAutomorphism F (absoluteRestriction i
      τ)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) =
    Spec.map (CommRingCat.ofHom (FieldGalois.asAutomorphism K τ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (closureEmbedding i)) ≫ Spec.map (CommRingCat.ofHom
        φ.toRingHom) at h
  simp only [← Spec.map_comp, Spec.map_inj] at h
  exact congrArg (fun z : CommRingCat.of L ⟶ CommRingCat.of (AlgebraicClosure K) => z.hom x) h

/-- Every algebraic-closure element lies in a finite subfield, so the square holds everywhere. -/
theorem absoluteRestriction_commutes (τ : Field.absoluteGaloisGroup K) (x : AlgebraicClosure F) :
    closureEmbedding i (FieldGalois.asAutomorphism F (absoluteRestriction i τ) x) =
      FieldGalois.asAutomorphism K τ (closureEmbedding i x) := by
  let L := IntermediateField.adjoin F {x}
  let : FiniteDimensional F L := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral x)
  exact absoluteRestriction_finite i τ L L.val (IntermediateField.AdjoinSimple.gen F x)

/-- The constructed actual Galois restriction preserves the finite cyclotomic character. -/
theorem cyclotomicCharacter_restriction (n : ℕ) [NeZero n] (τ : Field.absoluteGaloisGroup K) :
    Field.absoluteGaloisGroup.CyclotomicCharacter.character F n (absoluteRestriction i τ) =
      Field.absoluteGaloisGroup.CyclotomicCharacter.character K n τ := by
  open Field.absoluteGaloisGroup.CyclotomicCharacter in
  have hζ := primitiveRoot_spec F n
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  apply (closureEmbedding i).injective
  rw [map_pow, map_pow]
  have hj : (closureEmbedding i (Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot F
    n)) ^ n = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  rw [← map_pow, ← Field.absoluteGaloisGroup.CyclotomicCharacter.character_eval F n
    (absoluteRestriction i τ) _ hζ.pow_eq_one]
  exact (absoluteRestriction_commutes i τ _).trans
    (Field.absoluteGaloisGroup.CyclotomicCharacter.character_eval K n τ _ hj)

end AlgebraicGeometry.Scheme.FiniteEtale.FieldEmbeddingBaseChange

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 39ac167ae6628d289a6debcd095dd71aabe24c385f051dc68c305cf59b9acd85.
Definitions, hypotheses and universes are retained modulo native names. -/
