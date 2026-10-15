/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Open

/-! # The original tensor comparison on the native Mayer–Vietoris sequence

The original open-cohomology scalar mate gives a map from scalar extension
of the native module Mayer–Vietoris sequence to the original sequence on
inverse-image opens. Every arrow retains its original restriction or native
connecting map. Neither flatness nor quasicoherence is needed to construct
this diagram.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.ComposableArrows
open scoped TensorProduct ChangeOfRings

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
  (p : Y ⟶ X) (σ : R →+* S)
  (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
  (h : p.appTop.hom.comp α = β.comp σ)
  {M : X.Modules} {N : Y.Modules}
  (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)

/-- The original tensor comparison on a native binary biproduct of open-cohomology groups. -/
def moduleMayerVietorisTensorBiprodMap (U V : X.Opens) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u + 1} σ).obj
        ((moduleHPrimePresheaf X α M n).obj (op U) ⊞
          (moduleHPrimePresheaf X α M n).obj (op V)) ⟶
      (moduleHPrimePresheaf Y β N n).obj (op (p ⁻¹ᵁ U)) ⊞
        (moduleHPrimePresheaf Y β N n).obj (op (p ⁻¹ᵁ V)) :=
  ((ModuleCat.extendScalars.{u, u, u + 1} σ).mapBiprod
    ((moduleHPrimePresheaf X α M n).obj (op U))
    ((moduleHPrimePresheaf X α M n).obj (op V))).hom ≫
      biprod.map ((moduleHPrimeTensorMap p σ α β h φ n).app (op U))
        ((moduleHPrimeTensorMap p σ α β h φ n).app (op V))

/-- The binary tensor comparison is invertible whenever its two original components are. -/
theorem moduleMayerVietorisTensorBiprodMap_isIso (U V : X.Opens) (n : ℕ)
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op U))]
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op V))] :
    IsIso (moduleMayerVietorisTensorBiprodMap p σ α β h φ U V n) := by
  change IsIso (((ModuleCat.extendScalars.{u, u, u + 1} σ).mapBiprod
    ((moduleHPrimePresheaf X α M n).obj (op U))
    ((moduleHPrimePresheaf X α M n).obj (op V))).hom ≫
      (biprod.mapIso (asIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op U)))
        (asIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op V)))).hom)
  infer_instance

/-- The original tensor comparison commutes with the native sum of restriction maps. -/
theorem moduleMayerVietorisToBiprod_tensor (U V : X.Opens) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u + 1} σ).map (moduleMayerVietorisToBiprod X α M U V n) ≫
        moduleMayerVietorisTensorBiprodMap p σ α β h φ U V n =
      (moduleHPrimeTensorMap p σ α β h φ n).app (op (U ⊔ V)) ≫
        moduleMayerVietorisToBiprod Y β N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) n := by
  dsimp only [moduleMayerVietorisToBiprod, moduleMayerVietorisTensorBiprodMap]
  rw [← Category.assoc, biprod.map_lift_mapBiprod]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
    exact (moduleHPrimeTensorMap p σ α β h φ n).naturality
      (homOfLE (show U ≤ U ⊔ V from le_sup_left)).op
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
    exact (moduleHPrimeTensorMap p σ α β h φ n).naturality
      (homOfLE (show V ≤ U ⊔ V from le_sup_right)).op

/-- The original tensor comparison commutes with the native restriction-difference map. -/
theorem moduleMayerVietorisFromBiprod_tensor (U V : X.Opens) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u + 1} σ).map (moduleMayerVietorisFromBiprod X α M U V n) ≫
        (moduleHPrimeTensorMap p σ α β h φ n).app (op (U ⊓ V)) =
      moduleMayerVietorisTensorBiprodMap p σ α β h φ U V n ≫
        moduleMayerVietorisFromBiprod Y β N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) n := by
  rw [← cancel_epi ((ModuleCat.extendScalars.{u, u, u + 1} σ).mapBiprod
    ((moduleHPrimePresheaf X α M n).obj (op U))
    ((moduleHPrimePresheaf X α M n).obj (op V))).inv]
  dsimp only [moduleMayerVietorisFromBiprod, moduleMayerVietorisTensorBiprodMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [← Category.assoc, biprod.mapBiprod_inv_map_desc]
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
    exact (moduleHPrimeTensorMap p σ α β h φ n).naturality
      (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op
  · simp only [biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc]
    erw [(ModuleCat.extendScalars.{u, u, u + 1} σ).map_neg]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg]
    exact congrArg Neg.neg ((moduleHPrimeTensorMap p σ α β h φ n).naturality
      (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op)

/-- The original tensor comparison commutes with the native connecting homomorphism. -/
theorem moduleMayerVietorisDelta_tensor (U V : X.Opens) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u + 1} σ).map (moduleMayerVietorisDelta X α M U V n) ≫
        (moduleHPrimeTensorMap p σ α β h φ (n + 1)).app (op (U ⊔ V)) =
      (moduleHPrimeTensorMap p σ α β h φ n).app (op (U ⊓ V)) ≫
        moduleMayerVietorisDelta Y β N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) n := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ
  apply (adj.homEquiv _ _).injective
  conv_lhs => erw [adj.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  erw [moduleHPrimeTensorMap_unit p σ α β h φ (n + 1) (op (U ⊔ V))]
  conv_rhs => erw [(ModuleCat.restrictScalars σ).map_comp, ← Category.assoc]
  erw [moduleHPrimeTensorMap_unit p σ α β h φ n (op (U ⊓ V))]
  apply (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map_injective
  exact mayerVietoris_delta_geometric p U V (moduleAddSheaf X M) (moduleAddSheaf Y N)
    (moduleCoefficientPullback p φ) n

/-- The actual tensor mate on every term of the original native Mayer–Vietoris sequence. -/
def moduleMayerVietorisTensorSequenceMap (U V : X.Opens) (n : ℕ) :
    moduleMayerVietorisSequence X α M U V n ⋙ ModuleCat.extendScalars.{u, u, u + 1} σ ⟶
      moduleMayerVietorisSequence Y β N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) n :=
  homMk₅ ((moduleHPrimeTensorMap p σ α β h φ n).app (op (U ⊔ V)))
    (moduleMayerVietorisTensorBiprodMap p σ α β h φ U V n)
    ((moduleHPrimeTensorMap p σ α β h φ n).app (op (U ⊓ V)))
    ((moduleHPrimeTensorMap p σ α β h φ (n + 1)).app (op (U ⊔ V)))
    (moduleMayerVietorisTensorBiprodMap p σ α β h φ U V (n + 1))
    ((moduleHPrimeTensorMap p σ α β h φ (n + 1)).app (op (U ⊓ V)))
    (moduleMayerVietorisToBiprod_tensor p σ α β h φ U V n)
    (moduleMayerVietorisFromBiprod_tensor p σ α β h φ U V n)
    (moduleMayerVietorisDelta_tensor p σ α β h φ U V n)
    (moduleMayerVietorisToBiprod_tensor p σ α β h φ U V (n + 1))
    (moduleMayerVietorisFromBiprod_tensor p σ α β h φ U V (n + 1))

end AlgebraicGeometry.Scheme.Cohomology
