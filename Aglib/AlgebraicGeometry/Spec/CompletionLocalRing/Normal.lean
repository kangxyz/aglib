/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.CompletionLocalRing
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Sections
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Morphisms.Proper.ConnectedFibres
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Aglib.AlgebraicGeometry.Properties.Normal.GlobalSections
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.RingTheory.RegularLocalRing.Normal

/-!
# Normal completion from a proper regular model with its original section unit

For a proper morphism to a Noetherian local ring, regularity of the source
and bijectivity of the literal structural section map imply that the actual
maximal-ideal completion is an integrally closed domain.

The structural map after completion is proved bijective from the original
flat H0 base-change map and its pure-tensor unit law. Proper completion
regularity supplies normal stalks on the actual pullback. Its global section
ring is local, so it is connected; normality and local Noetherianity then
give integrality before any domain property of the completion is asserted.

There is no dimension, Nagata, excellence, coefficient-field, formal-functions
or vanishing hypothesis. The current consumer is R.N1: its final global
necessity theorem must derive the structural-section bijection from the
actual proper birational normal factor.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct ChangeOfRings

private def scalarTensorGeneratorEquiv
    {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)
    {M : Type v} [AddCommGroup M] [Module A M] (e : A ≃ₗ[A] M) :
    B ≃ₗ[B] (ModuleCat.extendScalars σ).obj (ModuleCat.of A M) := by
  let := σ.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid A B B).symm.trans
    ((e.baseChange A B _ _).trans
      (ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A M)).toLinearEquiv.symm)

private theorem scalarTensorGeneratorEquiv_apply
    {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)
    {M : Type v} [AddCommGroup M] [Module A M] (e : A ≃ₗ[A] M) (b : B) :
    scalarTensorGeneratorEquiv σ e b = b ⊗ₜ[A,σ] e 1 := by
  let := σ.toAlgebra
  change (ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A M)).inv
    ((e.baseChange A B _ _) ((TensorProduct.AlgebraTensorModule.rid A B B).symm b)) = _
  rw [TensorProduct.AlgebraTensorModule.rid_symm_apply, LinearEquiv.baseChange_tmul,
    ModuleCat.extendScalarsAlgebraObjIso_inv_tmul]

private theorem localRing_idempotent_eq_zero_or_one
    {A : Type u} [CommRing A] [IsLocalRing A] (a : A) (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
  · right
    apply hu.mul_left_cancel
    simpa only [mul_one] using ha.eq
  · left
    apply hu.mul_left_cancel
    rw [mul_zero, sub_mul, one_mul, ha.eq, sub_self]

private theorem map_map_id_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (X : C) {Y : E} (a : G.obj (F.obj X) ⟶ Y) :
    G.map (F.map (𝟙 X)) ≫ a = a := by
  rw [F.map_id, G.map_id, Category.id_comp]

@[expose] public section

namespace AlgebraicGeometry.Scheme.LocalRing

/-- The literal structural ring map of a scheme over the specified affine
base, with its original `ΓSpecIso`. -/
abbrev properStructuralSectionsMap {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of A)) : A →+* Γ(Z, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

section FlatSections

variable {A B : Type u} [CommRing A] [CommRing B] {Z : Scheme.{u}}
  (p : Z ⟶ Spec (.of A)) (σ : A →+* B)

/-- The original H0 tensor map with the original structure-unit coefficient
arrow on the actual fibre product. -/
def properStructureH0TensorMap :
    let Z' : Scheme.{u} := pullback p (Spec.map (CommRingCat.ofHom σ))
    let α := properStructuralSectionsMap p
    let β := properStructuralSectionsMap (pullback.snd p (Spec.map (CommRingCat.ofHom σ)))
    let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
    let O' : Z'.Modules := SheafOfModules.unit Z'.ringCatSheaf
    letI := moduleCohomologyModuleOfHom Z α O 0
    letI := moduleCohomologyModuleOfHom Z' β O' 0
    (ModuleCat.extendScalars σ).obj
        (ModuleCat.of A (Sheaf.H.{u + 1} (moduleAddSheaf Z O) 0)) ⟶
      ModuleCat.of B (Sheaf.H.{u + 1} (moduleAddSheaf Z' O') 0) :=
  let a := pullback.fst p (Spec.map (CommRingCat.ofHom σ))
  let b := pullback.snd p (Spec.map (CommRingCat.ofHom σ))
  moduleCohomologyTensorMap a σ (properStructuralSectionsMap p)
    (properStructuralSectionsMap b)
    (moduleSectionsBaseChangeScalars a b p σ pullback.condition)
    (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom) 0

/-- The structure-unit H0 map is invertible by flat base change. The
coefficient comparison is the original `pullbackUnitIso`, with its actual
adjunction-unit equation. -/
theorem properStructureH0TensorMap_isIso [QuasiCompact p] [QuasiSeparated p]
    (hflat : σ.Flat) : IsIso (properStructureH0TensorMap p σ) := by
  let Z' : Scheme.{u} := pullback p (Spec.map (CommRingCat.ofHom σ))
  let a : Z' ⟶ Z := pullback.fst p (Spec.map (CommRingCat.ofHom σ))
  let b : Z' ⟶ Spec (.of B) := pullback.snd p (Spec.map (CommRingCat.ofHom σ))
  let α : A →+* Γ(Z, ⊤) := properStructuralSectionsMap p
  let β : B →+* Γ(Z', ⊤) := properStructuralSectionsMap b
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let O' : Z'.Modules := SheafOfModules.unit Z'.ringCatSheaf
  let η : O ⟶ (pushforward a).obj ((Scheme.Modules.pullback a).obj O) :=
    (pullbackPushforwardAdjunction a).unit.app O
  let φ : O ⟶ (pushforward a).obj O' :=
    SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom
  have hunit : (𝟙 O) ≫ φ = η ≫ (pushforward a).map (pullbackUnitIso a).hom := by
    rw [Category.id_comp]
    exact (pullbackUnitIso_homEquiv a).symm.trans
      ((pullbackPushforwardAdjunction a).homEquiv_unit _ _ (pullbackUnitIso a).hom)
  have hsquare : moduleCohomologyTensorMap a σ α β
      (moduleSectionsBaseChangeScalars a b p σ pullback.condition) φ 0 =
    moduleCohomologyTensorMap a σ α β
      (moduleSectionsBaseChangeScalars a b p σ pullback.condition) η 0 ≫
      (moduleCohomologyFunctorOfHom Z' β 0).map (pullbackUnitIso a).hom := by
    have h := moduleCohomologyTensorMap_naturality a σ α β
        (moduleSectionsBaseChangeScalars a b p σ pullback.condition)
        η φ (𝟙 O) (pullbackUnitIso a).hom hunit 0
    exact (map_map_id_comp (moduleCohomologyFunctorOfHom Z α 0)
      (ModuleCat.extendScalars σ) O
      (moduleCohomologyTensorMap a σ α β
        (moduleSectionsBaseChangeScalars a b p σ pullback.condition) φ 0)).symm.trans h
  let : O.IsFinitePresentation := unit_isFinitePresentation Z
  let : IsIso (moduleCohomologyTensorMap a σ α β
      (moduleSectionsBaseChangeScalars a b p σ pullback.condition) η 0) := by
    exact moduleCohomologyBaseChangeMap_isIso_of_quasiSeparated p σ hflat O 0
  change IsIso (moduleCohomologyTensorMap a σ α β
    (moduleSectionsBaseChangeScalars a b p σ pullback.condition) φ 0)
  rw [hsquare]
  exact (asIso (moduleCohomologyTensorMap a σ α β
      (moduleSectionsBaseChangeScalars a b p σ pullback.condition) η 0) ≪≫
    (moduleCohomologyFunctorOfHom Z' β 0).mapIso (pullbackUnitIso a)).isIso_hom

/-- The pure unit tensor is the original structure-sheaf pullback on H0. -/
theorem properStructureH0TensorMap_one_tmul
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Z (SheafOfModules.unit Z.ringCatSheaf)) 0) :
    letI := moduleCohomologyModuleOfHom Z (properStructuralSectionsMap p)
      (SheafOfModules.unit Z.ringCatSheaf) 0
    properStructureH0TensorMap p σ ((1 : B) ⊗ₜ[A,σ] x) =
      moduleCohomologyMapAlong (pullback.fst p (Spec.map (CommRingCat.ofHom σ)))
        (SheafOfModules.unitToPushforwardObjUnit
          (pullback.fst p (Spec.map (CommRingCat.ofHom σ))).toRingCatSheafHom) 0 x :=
  moduleCohomologyTensorMap_one_tmul _ _ _ _ _ _ 0 x

end FlatSections

/-- A bijective literal structural section map supplies the H0 generator
with the unchanged structural module action. -/
def properStructuralH0Equiv {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of A)) (hα : Function.Bijective (properStructuralSectionsMap p)) :
    letI := moduleCohomologyModuleOfHom Z (properStructuralSectionsMap p)
      (SheafOfModules.unit Z.ringCatSheaf) 0
    A ≃ₗ[A] Sheaf.H.{u + 1}
      (moduleAddSheaf Z (SheafOfModules.unit Z.ringCatSheaf)) 0 := by
  let α : A →+* Γ(Z, ⊤) := properStructuralSectionsMap p
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let := moduleCohomologyModuleOfHom Z α O 0
  letI : Module Γ(Z, ⊤) (O.val.obj (op ⊤)) := (O.val.obj (op ⊤)).isModule
  letI : Module A (O.val.obj (op ⊤)) := Module.compHom _ α
  let c : A →ₗ[A] O.val.obj (op ⊤) :=
    { toFun := α
      map_add' := map_add α
      map_smul' r s := by change α (r * s) = α r * α s; exact map_mul α r s }
  exact (LinearEquiv.ofBijective c hα).trans (moduleH0EquivOfHom Z α O).symm

/-- The H0 generator is normalized by the original structural section. -/
theorem properStructuralH0Equiv_sections {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of A)) (hα : Function.Bijective (properStructuralSectionsMap p)) (r : A) :
    moduleH0EquivOfHom Z (properStructuralSectionsMap p) (SheafOfModules.unit Z.ringCatSheaf)
      (properStructuralH0Equiv p hα r) = properStructuralSectionsMap p r := by
  let α : A →+* Γ(Z, ⊤) := properStructuralSectionsMap p
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let := moduleCohomologyModuleOfHom Z α O 0
  change moduleH0EquivOfHom Z α O ((moduleH0EquivOfHom Z α O).symm (α r)) = α r
  exact (moduleH0EquivOfHom Z α O).apply_symm_apply _

/-- Flat H0 base change preserves bijectivity of the literal structural
ring map. The proof identifies the resulting map on every scalar, not just
an abstract isomorphism of section modules. -/
theorem bijective_structuralSections_of_flat_baseChange
    {A B : Type u} [CommRing A] [CommRing B] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of A)) [QuasiCompact p] [QuasiSeparated p]
    (σ : A →+* B) (hflat : σ.Flat)
    (hα : Function.Bijective (properStructuralSectionsMap p)) :
    Function.Bijective
      (properStructuralSectionsMap (pullback.snd p (Spec.map (CommRingCat.ofHom σ)))) := by
  let Z' : Scheme.{u} := pullback p (Spec.map (CommRingCat.ofHom σ))
  let a : Z' ⟶ Z := pullback.fst p (Spec.map (CommRingCat.ofHom σ))
  let b : Z' ⟶ Spec (.of B) := pullback.snd p (Spec.map (CommRingCat.ofHom σ))
  let α : A →+* Γ(Z, ⊤) := properStructuralSectionsMap p
  let β : B →+* Γ(Z', ⊤) := properStructuralSectionsMap b
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let N : Z'.Modules := (Scheme.Modules.pullback a).obj O
  let := moduleCohomologyModuleOfHom Z α O 0
  let := moduleCohomologyModuleOfHom Z' β N 0
  let : O.IsFinitePresentation := unit_isFinitePresentation Z
  let : IsIso (moduleCohomologyBaseChangeMap p σ O 0) :=
    moduleCohomologyBaseChangeMap_isIso_of_quasiSeparated p σ hflat O 0
  let E : B ≃ Γ(Z', ⊤) :=
    (scalarTensorGeneratorEquiv σ (properStructuralH0Equiv p hα)).toEquiv.trans
      ((asIso (moduleCohomologyBaseChangeMap p σ O 0)).toLinearEquiv.toEquiv.trans
        (Equiv.ofBijective (pullbackUnitSections a) (pullbackUnitSections_bijective a)))
  have hE (s : B) : E s = β s := by
    have hgen := scalarTensorGeneratorEquiv_apply σ (properStructuralH0Equiv p hα) s
    have hmap := congrArg (fun z =>
      pullbackUnitSections a (moduleCohomologyBaseChangeMap p σ O 0 z)) hgen
    have ht := pullbackUnitSections_moduleCohomologyTensorMap_tmul a b p σ
      pullback.condition s (properStructuralH0Equiv p hα 1)
    have hsection : unitSections Z (properStructuralH0Equiv p hα 1) = α 1 :=
      properStructuralH0Equiv_sections p hα 1
    have hvalue : E s = β s * a.appTop (unitSections Z (properStructuralH0Equiv p hα 1)) :=
      hmap.trans ht
    exact hvalue.trans ((congrArg (fun t => β s * a.appTop t) hsection).trans
      (by simp only [map_one, mul_one]))
  constructor
  · intro r s hrs
    apply E.injective
    exact (hE r).trans (hrs.trans (hE s).symm)
  · intro t
    obtain ⟨s, hs⟩ := E.surjective t
    exact ⟨s, (hE s).symm.trans hs⟩

section Completion

variable (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
  {Z : Scheme.{u}} (p : Z ⟶ Spec (.of B)) [IsProper p]
  (hZ : RegularStalks Z) (hβ : Function.Bijective (properStructuralSectionsMap p))

include hβ in
/-- The actual structural map of the original completed pullback is
bijective by the original flat H0 base-change calculation. -/
theorem bijective_completionStructuralSections :
    Function.Bijective (properStructuralSectionsMap (pullback.snd p (completionSpecMap B))) := by
  let S := AdicCompletion (IsLocalRing.maximalIdeal B) B
  exact bijective_structuralSections_of_flat_baseChange p (algebraMap B S)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hβ

/-- The literal completion is the actual global section ring of the
completed pullback, with the original structural homomorphism as forward map. -/
def completionStructuralSectionsEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+*
      Γ(pullback p (completionSpecMap B), ⊤) :=
  RingEquiv.ofBijective (properStructuralSectionsMap (pullback.snd p (completionSpecMap B)))
    (bijective_completionStructuralSections B p hβ)

/-- The structural isomorphism is the original map on every completed scalar. -/
theorem completionStructuralSectionsEquiv_apply
    (s : AdicCompletion (IsLocalRing.maximalIdeal B) B) :
    completionStructuralSectionsEquiv B p hβ s =
      (pullback.snd p (completionSpecMap B)).appTop
        ((Scheme.ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal B) B))).inv s) := rfl

include p hZ hβ in
/-- A proper regular model whose literal structural section map is
bijective forces its base's actual maximal completion to be a normal domain.
Connectedness and integrality of the completed source are proved before any
domain property of the completed ring is used. -/
theorem completion_normal_of_proper_regular_structuralSections :
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal B) B) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal B) B) := by
  let S := AdicCompletion (IsLocalRing.maximalIdeal B) B
  let W : Scheme.{u} := pullback p (completionSpecMap B)
  let q : W ⟶ Spec (.of S) := pullback.snd p (completionSpecMap B)
  let : IsNoetherianRing S := AdicCompletion.isNoetherianRing B (IsLocalRing.maximalIdeal B)
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian q
  let e : S ≃+* Γ(W, ⊤) := completionStructuralSectionsEquiv B p hβ
  let : Nontrivial Γ(W, ⊤) := e.symm.toEquiv.nontrivial
  let : IsLocalRing Γ(W, ⊤) := e.isLocalRing
  have hWreg : RegularStalks W := (regularStalks_completionBaseChange_iff B p).mp hZ
  have hWnormal : NormalStalks W := by
    intro z
    let : IsRegularLocalRing (W.presheaf.stalk z) := hWreg z
    exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
      IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩
  let : Nonempty W := by
    by_contra h
    let : IsEmpty W := not_nonempty_iff.mp h
    have ht : (⊤ : W.Opens) = ⊥ := by ext z; exact isEmptyElim z
    have : Subsingleton Γ(W, ⊤) := by rw [ht]; infer_instance
    exact one_ne_zero (Subsingleton.elim (1 : Γ(W, ⊤)) 0)
  let : ConnectedSpace W := connectedSpace_of_globalSections_idempotents W
    (fun a ha => localRing_idempotent_eq_zero_or_one a ha)
  let : IsIntegral W := isIntegral_of_connected_normalStalks_actual W hWnormal
  let : IsIntegrallyClosed Γ(W, ⊤) :=
    NormalStalks.isIntegrallyClosed_globalSections W hWnormal
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

end Completion

end AlgebraicGeometry.Scheme.LocalRing
