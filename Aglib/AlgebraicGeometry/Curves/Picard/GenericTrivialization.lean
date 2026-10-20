/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.RationalTrivialization
public import Aglib.AlgebraicGeometry.Modules.Pullback.TensorAdjunction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.UnitPower
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorTensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.FieldMaps
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.RationalFunctions

/-!
# Regular-curve Picard supplier

Source: `R5Lab.AlgebraicGeometry.Curves.Picard.GenericTrivialization`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`26aa8666042d91066817b703ad7559ff891c5eaf37dae8a2826808342c415956`.
Actual divisors, quotient relations, fractional inclusions, tensor comparisons,
equality transports and principal trivializations are preserved. The original
regularity, level and product-formula premises remain explicit. General native
line-bundle, tensor, descent and cohomology suppliers are reused.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.Torsion
open _root_.AlgebraicGeometry.Scheme.Modules.RationalFunctions
open _root_.AlgebraicGeometry.Scheme.Modules.Pullback.Tensor

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (pullbackLineBundle )
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap pullbackTensorMap_adjoint pushforwardTensorMap
      pushforwardTensorMap_naturality pushforwardTensorMap_tmul
    tensorSheafLeftUnit tensorSheafLeftUnit_tmul tensorSheafMap tensorSheafMap_comp
        tensorSheafMap_tmul
    tensorSheafUnit)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Canonical generic trivializations of actual divisor line bundles

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`, C4/C5's
actual divisor-pair generic representative.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

On an integral Noetherian scheme with the displayed closed-stalk DVR hypotheses,
O(D) is the previously constructed actual fractional subsheaf of the generic
pushforward. Its inclusion has a nonzero local rational section. Its actual
pullback adjoint is therefore a nonzero map of lines over the function field,
and hence an isomorphism when the dimension is at most one. This constructs
the canonical generic trivialization without choosing a new rational basis.

We prove that this literal map preserves fractional tensor multiplication and
that principal trivialization is multiplication by the given function f.
The proofs retain the correct zero section module on empty opens. The map on
field units uses the actual Gamma-Spec isomorphism. There is no new standard
theorem family, no H1 comparison, and no assumed representative identity here.
The tensor-power/pair consequence is in the separate GenericPower application.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.GenericTrivialization
open DivisorClass
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]

private theorem fieldUnit_restrict_value (U : X.Opens) [Nonempty U] (g : X.functionFieldˣ) :
    (rationalSectionIso X U).hom
      ((Spec X.functionField).presheaf.map
        (homOfLE le_top : (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ⟶ ⊤).op
          (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom g).val) = g.val := by
  have aux (V : (Spec X.functionField).Opens) (hV : V = ⊤) :
      (eqToIso (congrArg (fun W => Γ(Spec X.functionField, W)) hV)).hom
        ((Spec X.functionField).presheaf.map (homOfLE le_top : V ⟶ ⊤).op
          (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom g).val) =
        (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom g).val := by
    subst V
    simp
  change (Scheme.ΓSpecIso X.functionField).hom
    ((eqToIso (congrArg (fun W => Γ(Spec X.functionField, W))
      (generic_preimage_eq_top X U))).hom ((Spec X.functionField).presheaf.map
      (homOfLE le_top : (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ⟶ ⊤).op
        (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom g).val)) = _
  rw [aux _ (generic_preimage_eq_top X U)]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso X.functionField).inv_hom_id g.val

variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

/-- The canonical generic map is the actual adjoint of the fractional-subsheaf inclusion. -/
def genericMap (D : Divisor X) :
    (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).obj (divisorSheaf X D) ⟶
      SheafOfModules.unit (Spec X.functionField).ringCatSheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction ((X.fromSpecStalk (genericPoint X)))).homEquiv
      _ _).symm
    (fractionalSubsheaf X D).ι

@[simp] theorem genericMap_adjoint (D : Divisor X) :
    (Scheme.Modules.pullbackPushforwardAdjunction ((X.fromSpecStalk (genericPoint X)))).homEquiv _ _
      (genericMap X D) = (fractionalSubsheaf X D).ι := Equiv.apply_symm_apply _ _

/-- The actual inclusion has a local fractional section with nonzero rational value. -/
theorem inclusion_ne_zero (D : Divisor X) : (fractionalSubsheaf X D).ι ≠ 0 := by
  intro hz
  obtain ⟨U, hx, g, hg⟩ := exists_local_principal_function X D (genericPoint X)
  let : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  let s : (divisorSheaf X D).val.obj (op U) :=
    (explicitSheafSectionsEquiv X D U).symm ⟨g.val, Or.inr (fun x hx => (hg x hx).ge)⟩
  have hs := congrArg (fun q : (show X.Modules from divisorSheaf X D) ⟶ rationalFunctions X =>
    q.val.app (op U) s) hz
  change s.val = 0 at hs
  have hv := congrArg (rationalValue X U) hs
  have hv' := congrArg Subtype.val ((explicitSheafSectionsEquiv X D U).apply_symm_apply
    ⟨g.val, Or.inr (fun x hx => (hg x hx).ge)⟩)
  change rationalValue X U s.val = g.val at hv'
  rw [hv', map_zero] at hv
  exact g.ne_zero hv

theorem genericMap_ne_zero (D : Divisor X) : genericMap X D ≠ 0 := by
  intro hz
  apply inclusion_ne_zero X D
  rw [← genericMap_adjoint, hz]
  simp [Adjunction.homEquiv_apply]


/-- The canonical fractional inclusion induces a nonzero map of actual lines over the function
field. -/
theorem genericMap_isIso (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) :
    IsIso (genericMap X D) :=
  fieldLineBundleMap_isIso_of_ne_zero X.functionField
    (pullbackLineBundle ((X.fromSpecStalk (genericPoint X))) (divisorLineBundle X hdim D))
    (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle (Spec
        X.functionField)) (genericMap X D) (genericMap_ne_zero X D)

/-- The canonical generic trivialization, induced by literal rational inclusion. -/
def genericIso (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) :
    (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).obj (divisorSheaf X D) ≅
      SheafOfModules.unit (Spec X.functionField).ringCatSheaf :=
  letI := genericMap_isIso X hdim D
  asIso (genericMap X D)

@[simp] theorem genericIso_hom (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) :
    (genericIso X hdim D).hom = genericMap X D := rfl

/-- The actual sheafified multiplication has its literal pure-tensor section formula. -/
theorem divisorMultiplication_tmul (D E : Divisor X) (U : X.Opensᵒᵖ)
    (s : (divisorSheaf X D).val.obj U) (t : (divisorSheaf X E).val.obj U) :
    (divisorMultiplicationSheaf X D E).val.app U
      ((tensorSheafUnit X (divisorSheaf X D) (divisorSheaf X E)).app U (s ⊗ₜ t)) =
      divisorMultiplySections X D E U.unop s t := by
  have h := (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (F := divisorSheaf X (D + E))).apply_symm_apply (divisorMultiplicationPresheaf X D E)
  exact congrArg (fun k => k.app U (s ⊗ₜ t)) h

/-- Fractional multiplication is the actual multiplication in the generic pushforward. -/
theorem inclusion_tensor (D E : Divisor X) :
    divisorMultiplicationSheaf X D E ≫ (fractionalSubsheaf X (D + E)).ι =
      tensorSheafMap X (fractionalSubsheaf X D).ι (fractionalSubsheaf X E).ι ≫
        pushforwardTensorMap ((X.fromSpecStalk (genericPoint X)))
          (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)
          (SheafOfModules.unit (Spec X.functionField).ringCatSheaf) ≫
        (Scheme.Modules.pushforward ((X.fromSpecStalk (genericPoint X)))).map
          (tensorSheafLeftUnit (Spec X.functionField)
            (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)).hom := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  by_cases hU : Nonempty U.unop
  · let := hU
    apply (rationalValueEquiv X U.unop).injective
    change rationalValue X U.unop
        ((divisorMultiplicationSheaf X D E).val.app U
          ((tensorSheafUnit X (divisorSheaf X D) (divisorSheaf X E)).app U (s ⊗ₜ t))).val = _
    rw [divisorMultiplication_tmul, divisorMultiplySections_value]
    change rationalValue X U.unop s.val * rationalValue X U.unop t.val =
      rationalValue X U.unop
        ((tensorSheafLeftUnit (Spec X.functionField)
          (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)).hom.val.app
            (op (((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U.unop))
          ((pushforwardTensorMap ((X.fromSpecStalk (genericPoint X)))
            (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)
            (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)).val.app U
              ((tensorSheafMap X (fractionalSubsheaf X D).ι (fractionalSubsheaf X E).ι).val.app U
                ((tensorSheafUnit X (divisorSheaf X D) (divisorSheaf X E)).app U (s ⊗ₜ t)))))
    have ht := tensorSheafMap_tmul X (fractionalSubsheaf X D).ι (fractionalSubsheaf X E).ι U s t
    have hp := pushforwardTensorMap_tmul ((X.fromSpecStalk (genericPoint X)))
      (show (Spec X.functionField).Modules from SheafOfModules.unit (Spec
          X.functionField).ringCatSheaf)
      (show (Spec X.functionField).Modules from SheafOfModules.unit (Spec
          X.functionField).ringCatSheaf)
      U s.val t.val
    have hu := tensorSheafLeftUnit_tmul (Spec X.functionField)
      (show (Spec X.functionField).Modules from SheafOfModules.unit (Spec
          X.functionField).ringCatSheaf)
      (op (((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U.unop)) s.val t.val
    erw [ht, hp, hu]
    exact ((rationalSectionIso X U.unop).hom.hom.map_mul s.val t.val).symm
  · have hzero : U.unop = ⊥ :=
      AlgebraicGeometry.Scheme.Modules.Invertible.RationalTrivialization.eq_bot_of_not_nonempty
      X U.unop hU
    have : Subsingleton ((rationalFunctions X).val.obj U) := by
      change Subsingleton (Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U.unop))
      rw [hzero, Scheme.Hom.preimage_bot]
      infer_instance
    exact @Subsingleton.elim ((rationalFunctions X).val.obj U) inferInstance _ _

/-- The canonical generic maps preserve literal fractional multiplication. -/
theorem genericMap_tensor (D E : Divisor X) :
    (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map
        (divisorMultiplicationSheaf X D E) ≫
      genericMap X (D + E) =
      pullbackTensorMap ((X.fromSpecStalk (genericPoint X))) (divisorSheaf X D) (divisorSheaf X E) ≫
        tensorSheafMap (Spec X.functionField) (genericMap X D) (genericMap X E) ≫
          (tensorSheafLeftUnit (Spec X.functionField)
            (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction ((X.fromSpecStalk (genericPoint
      X)))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, genericMap_adjoint]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right, tensor_adjoint,
    genericMap_adjoint, genericMap_adjoint, Category.assoc]
  exact inclusion_tensor X D E


/-- An actual global fractional trivialization has its prescribed literal generic scalar. -/
theorem genericMap_globalTrivialization (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, X.ord (g : X.functionField) x.val + D x = 0) :
    (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map (globalTrivialization X
        hdim D g hg).hom ≫
      genericMap X D =
    (pullbackUnitIso ((X.fromSpecStalk (genericPoint X)))).hom ≫
      AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap (Spec
          X.functionField) _ ((Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom
          g)) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction ((X.fromSpecStalk (genericPoint
      X)))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, genericMap_adjoint,
    Adjunction.homEquiv_naturality_right,
        AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.unitIso_adjoint]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  by_cases hU : Nonempty U.unop
  · let := hU
    apply (rationalValueEquiv X U.unop).injective
    change rationalValue X U.unop
      (sectionTrivialization X hdim D U.unop g (fun x _ => hg x) a).val =
        (rationalSectionIso X U.unop).hom
          ((Spec X.functionField).presheaf.map
            (homOfLE le_top : ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U.unop ⟶ ⊤).op
                ((Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom g)).val *
              ((X.fromSpecStalk (genericPoint X))).app U.unop a)
    rw [sectionTrivialization_value, map_mul, fieldUnit_restrict_value]
    congr 1
    exact (congrArg (fun q : Γ(X, U.unop) ⟶ X.functionField => q a)
      (generic_app_rationalSectionIso X U.unop)).symm
  · have hzero : U.unop = ⊥ :=
      AlgebraicGeometry.Scheme.Modules.Invertible.RationalTrivialization.eq_bot_of_not_nonempty
      X U.unop hU
    have : Subsingleton ((rationalFunctions X).val.obj U) := by
      change Subsingleton (Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U.unop))
      rw [hzero, Scheme.Hom.preimage_bot]
      infer_instance
    exact @Subsingleton.elim ((rationalFunctions X).val.obj U) inferInstance _ _

/-- The actual principal trivialization is multiplication by f at the generic point. -/
theorem genericMap_principal (hdim : topologicalKrullDim X ≤ 1) (f : X.functionFieldˣ) :
    (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map (principalTrivialization
        X hdim f).hom ≫
      (pullbackUnitIso ((X.fromSpecStalk (genericPoint X)))).hom =
    genericMap X (principal X (Additive.ofMul f)) ≫
      AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap (Spec
          X.functionField) _ ((Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom
          f)) := by
  apply (cancel_epi ((Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map
    (principalTrivialization X hdim f).inv)).mp
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc]
  have hg := genericMap_globalTrivialization X hdim (principal X (Additive.ofMul f)) f⁻¹
    (by intro x; change X.ord ((f⁻¹ : X.functionFieldˣ) : X.functionField) x.val +
      X.ord (f : X.functionField) x.val = 0; rw [order_inv]; exact neg_add_cancel _)
  change (pullbackUnitIso ((X.fromSpecStalk (genericPoint X)))).hom =
    ((Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map
      (globalTrivialization X hdim (principal X (Additive.ofMul f)) f⁻¹ _).hom ≫
        genericMap X (principal X (Additive.ofMul f))) ≫ _
  rw [hg, Category.assoc,
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarMap_mul, _root_.map_inv]
  simp only [Units.inv_mul,
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarMap_one,
      Category.comp_id]

/-- The literal generic map respects equality transport of divisors. -/
theorem genericMap_eqToIso {D E : Divisor X} (h : D = E) :
    (Scheme.Modules.pullback ((X.fromSpecStalk (genericPoint X)))).map
      (eqToIso (congrArg (divisorSheaf X) h)).hom ≫ genericMap X E = genericMap X D := by
  subst E
  simp

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.GenericTrivialization
