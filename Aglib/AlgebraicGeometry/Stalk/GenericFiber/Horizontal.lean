/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.DedekindGenericFiber
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# Horizontal points and the actual generic fibre

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.GenericFiberCodimensionOne`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `3a7aff19070984be943d67839f1e1510a24fcdda2eb67d6ec67be02f1aa84b25`, selected lines [[39,
214]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u
namespace AlgebraicGeometry.Scheme.LocalRing.GenericFiber

variable (A F : Type u) [CommRing A] [IsDedekindDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))

omit [IsDedekindDomain A] in
theorem projection_injective : Function.Injective (projection A F p) := by
  let := baseMap_preimmersion A F
  exact (projection A F p).isEmbedding.injective

theorem projection_over_genericPoint (x : scheme A F p) :
    p (projection A F p x) = genericPoint (Spec (.of A)) := by
  have h := congrArg (fun f => f x) (pullback.condition (f := p) (g := baseMap A F))
  change p (projection A F p x) = baseMap A F (pullback.snd p (baseMap A F) x) at h
  rw [Subsingleton.elim (pullback.snd p (baseMap A F) x) (IsLocalRing.closedPoint F),
    baseMap_closedPoint_eq_genericPoint A F] at h
  exact h

theorem projection_imagePrime_eq_bot (x : scheme A F p) :
    (DedekindBase.imagePrime p (projection A F p x)).asIdeal = ⊥ :=
  (DedekindBase.image_eq_genericPoint_iff p (projection A F p x)).mp
    (projection_over_genericPoint A F p x)

/-- Constants in a horizontal point's actual residue field, via its canonical stalk map. -/
def horizontalResidueConstants (y : Y) (hy : p y = genericPoint (Spec (.of A))) :
    F →+* Y.residueField y :=
  (Y.residue y).hom.comp (DedekindBase.horizontalToStalk F p y
    ((DedekindBase.image_eq_genericPoint_iff p y).mp hy))

theorem horizontalResidue_triangle (y : Y) (hy : p y = genericPoint (Spec (.of A))) :
    Y.fromSpecResidueField y ≫ p =
      Spec.map (CommRingCat.ofHom (horizontalResidueConstants A F p y hy)) ≫ baseMap A F := by
  have hl : Y.fromSpecResidueField y ≫ p =
      Spec.map (CommRingCat.ofHom ((Y.residue y).hom.comp (DedekindBase.baseToStalk p y))) := by
    dsimp only [Scheme.fromSpecResidueField]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk p, Spec.fromSpecStalk_eq]
    simp only [← Spec.map_comp]
    rfl
  have hr : CommRingCat.ofHom ((Y.residue y).hom.comp (DedekindBase.baseToStalk p y)) =
      CommRingCat.ofHom (algebraMap A F) ≫
        CommRingCat.ofHom (horizontalResidueConstants A F p y hy) := by
    apply CommRingCat.hom_ext
    ext a
    change Y.residue y (DedekindBase.baseToStalk p y a) =
      Y.residue y (DedekindBase.horizontalToStalk F p y
        ((DedekindBase.image_eq_genericPoint_iff p y).mp hy) (algebraMap A F a))
    rw [DedekindBase.horizontalToStalk_algebraMap]
  rw [hl, hr, Spec.map_comp]
  rfl

/-- The residue-field-valued arrow lifted into the literal fraction-field pullback. -/
def horizontalResidueLift (y : Y) (hy : p y = genericPoint (Spec (.of A))) :
    Spec (Y.residueField y) ⟶ scheme A F p :=
  pullback.lift (Y.fromSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (horizontalResidueConstants A F p y hy)))
    (horizontalResidue_triangle A F p y hy)

/-- The point of the actual generic fibre selected by the residue-field lift. -/
def horizontalLift (y : Y) (hy : p y = genericPoint (Spec (.of A))) : scheme A F p :=
  horizontalResidueLift A F p y hy (IsLocalRing.closedPoint (Y.residueField y))

@[simp] theorem horizontalLift_projection (y : Y) (hy : p y = genericPoint (Spec (.of A))) :
    projection A F p (horizontalLift A F p y hy) = y := by
  change (horizontalResidueLift A F p y hy ≫ projection A F p)
    (IsLocalRing.closedPoint (Y.residueField y)) = _
  rw [horizontalResidueLift, pullback.lift_fst]
  exact Scheme.fromSpecResidueField_apply _ _

theorem existsUnique_horizontalLift (y : Y) (hy : p y = genericPoint (Spec (.of A))) :
    ∃! x : scheme A F p, projection A F p x = y := by
  refine ⟨horizontalLift A F p y hy, horizontalLift_projection A F p y hy, ?_⟩
  intro x hx
  apply projection_injective A F p
  exact hx.trans (horizontalLift_projection A F p y hy).symm

omit [IsDedekindDomain A] in
/-- The actual generic-fibre projection preserves stalk dimension one. -/
theorem projection_codimensionOne_dimension (x : CodimensionOnePoint (scheme A F p)) :
    ringKrullDim (Y.presheaf.stalk (projection A F p x.1)) = 1 :=
  (ringKrullDim_eq_of_ringEquiv (stalkEquiv A F p x.1)).trans x.2

omit [IsDedekindDomain A] in
/-- The actual projection on dimension-one points, using its canonical stalk equivalence. -/
def codimensionOneProjection (x : CodimensionOnePoint (scheme A F p)) :
    CodimensionOnePoint Y :=
  ⟨projection A F p x.1, projection_codimensionOne_dimension A F p x⟩

/-- A horizontal dimension-one point lifted using its actual projection-stalk equivalence. -/
def codimensionOneHorizontalLift (y : CodimensionOnePoint Y)
    (hy : p y.1 = genericPoint (Spec (.of A))) : CodimensionOnePoint (scheme A F p) :=
  ⟨horizontalLift A F p y.1 hy, by
    have h := (ringKrullDim_eq_of_ringEquiv (stalkEquiv A F p (horizontalLift A F p y.1 hy))).symm
    rw [horizontalLift_projection] at h
    exact h.trans y.2⟩

/-- Dimension-one points of the generic fibre are exactly horizontal dimension-one points.
The inverse is constructed from the actual residue-field-valued pullback lift. -/
def horizontalCodimensionOneEquiv :
    CodimensionOnePoint (scheme A F p) ≃
      {y : CodimensionOnePoint Y // p y.1 = genericPoint (Spec (.of A))} where
  toFun x := ⟨codimensionOneProjection A F p x,
    projection_over_genericPoint A F p x.1⟩
  invFun y := codimensionOneHorizontalLift A F p y.1 y.2
  left_inv x := by
    apply Subtype.ext
    apply projection_injective A F p
    exact horizontalLift_projection A F p _ _
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact horizontalLift_projection A F p _ _

@[simp] theorem horizontalCodimensionOneEquiv_image (x : CodimensionOnePoint (scheme A F p)) :
    (horizontalCodimensionOneEquiv A F p x).1 =
      codimensionOneProjection A F p x := rfl

/-- The actual projection's stalk equivalence induces its canonical residue-field equivalence. -/
def residueFieldRingEquiv (x : scheme A F p) :
    Y.residueField (projection A F p x) ≃+* (scheme A F p).residueField x :=
  IsLocalRing.ResidueField.mapEquiv (stalkEquiv A F p x)

omit [IsDedekindDomain A] in
@[simp] theorem residueFieldRingEquiv_apply (x : scheme A F p)
    (a : Y.residueField (projection A F p x)) :
    residueFieldRingEquiv A F p x a = (projection A F p).residueFieldMap x a := rfl

omit [IsDedekindDomain A] in
theorem residueFieldRingEquiv_toRingHom (x : scheme A F p) :
    (residueFieldRingEquiv A F p x).toRingHom =
      ((projection A F p).residueFieldMap x).hom := rfl

omit [IsDedekindDomain A] in
theorem residueFieldRingEquiv_reduction (x : scheme A F p)
    (a : Y.presheaf.stalk (projection A F p x)) :
    residueFieldRingEquiv A F p x (Y.residue (projection A F p x) a) =
      (scheme A F p).residue x (stalkEquiv A F p x a) := rfl

omit [IsDedekindDomain A] in
theorem stalkEquiv_isUnit_iff (x : scheme A F p)
    (a : Y.presheaf.stalk (projection A F p x)) :
    IsUnit (stalkEquiv A F p x a) ↔ IsUnit a :=
  isUnit_map_iff (stalkEquiv A F p x) a

omit [IsDedekindDomain A] in
theorem stalkEquiv_irreducible_iff (x : scheme A F p)
    (a : Y.presheaf.stalk (projection A F p x)) :
    Irreducible (stalkEquiv A F p x a) ↔ Irreducible a :=
  MulEquiv.irreducible_iff (stalkEquiv A F p x)

/-- The structural fraction-field map at an actual residue-field point of the generic fibre. -/
def fibreResidueConstants (x : scheme A F p) : F →+* (scheme A F p).residueField x :=
  (Spec.preimage ((scheme A F p).fromSpecResidueField x ≫ pullback.snd p (baseMap A F))).hom

theorem residueFieldRingEquiv_constants (x : scheme A F p) :
    (residueFieldRingEquiv A F p x).toRingHom.comp
        (horizontalResidueConstants A F p (projection A F p x)
          (projection_over_genericPoint A F p x)) =
      fibreResidueConstants A F p x := by
  rw [residueFieldRingEquiv_toRingHom]
  let := baseMap_preimmersion A F
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  rw [Spec.map_preimage]
  change Spec.map (CommRingCat.ofHom (horizontalResidueConstants A F p
      (projection A F p x) (projection_over_genericPoint A F p x)) ≫
      (projection A F p).residueFieldMap x) =
    (scheme A F p).fromSpecResidueField x ≫ pullback.snd p (baseMap A F)
  rw [Spec.map_comp]
  apply (cancel_mono (baseMap A F)).mp
  rw [Category.assoc, ← horizontalResidue_triangle, ← Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun f => (scheme A F p).fromSpecResidueField x ≫ f)
    (pullback.condition (f := p) (g := baseMap A F))

section Integral
variable [IsIntegral Y] [IsDominant p] [IsIntegral (scheme A F p)]

/-- The actual projection's stalk maps commute with its canonical function-field equivalence. -/
theorem functionFieldRingEquiv_toFunctionField (x : CodimensionOnePoint (scheme A F p))
    (a : (codimensionOneProjection A F p x).localRing) :
    FunctionField.DedekindGenericFiber.functionFieldRingEquiv A F p
        ((codimensionOneProjection A F p x).toFunctionField a) =
      x.toFunctionField (stalkEquiv A F p x.1 a) := by
  rw [FunctionField.DedekindGenericFiber.functionFieldRingEquiv_apply]
  exact functionFieldMap_stalk (projection A F p) x.1 a

end Integral
end AlgebraicGeometry.Scheme.LocalRing.GenericFiber
