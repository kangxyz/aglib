/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.FieldBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Geometric
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Aglib.Algebra.Homology.ShortComplex.MapHomology
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctor
/-!
# Canonical scalar and geometric comparisons for structure-sheaf Cech cohomology

These components keep the original structureCohomology object and structural
field action. The positive Cech comparison is proved F-linear for the actual
native ModuleCat cohomology. The two genuine augmentation maps give the
geometric comparison square on additive-resolution homology.

The original zariskiCohomologyMap and structureCohomologyBaseChangeMap are
unchanged. The positive-degree geometric Cech comparison is proved to agree with the
original zariskiCohomologyMap, through an actual exact-inverse-image lift and
the original Ext map. The literal
Cech tensor/geometric square on 1 ⊗ sections is proved, and the native finite
affine-cover Cech tensor isomorphism gives a K-linear equivalence of the
original positive cohomology objects. The homology comparison retains the exact value on 1 ⊗ x.
  The resulting
K-linear equivalence is proved to have exactly the existing
structureCohomologyBaseChangeMap as its underlying map. Thus an actual finite
affine cover proves positive canonical base change, without any cohomology
finiteness or supplied theorem-family premise.

Integration entry basis: project 3397a339b6a52fbba586dae127aa729d873b771d,
Lean 4.34.1 / mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 /
Quillen 83629578a3d70787d41ec631f5234af8758716af. CechComparison is frozen at
46802de5083f2ed4fa4c86c1a8fd1c65e4239aaf081f4ba30dcb2b663a12034b;
its joint independent review/replay with the additive total wrapper was
accepted and released by the principal on this exact frozen source basis.
The exact-functor Ext comparison dependency is likewise released at
26498baba5f1b73cb82ac0f8a459f2f3b1832862c44415180626716d2f5b0bf6.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.CanonicalCechBaseChange` at R5Lab
  revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
section Scalars
variable {F : Type u} [Field F] (X : FScheme F) {ι : Type u} (U : ι → X.left.Opens)

theorem structureCechForgetIso_hom_f_π (n : ℕ) (b : Fin (n + 1) → ι) :
    (structureCechForgetIso X U).hom.f n ≫
      Pi.π (fun b : Fin (n + 1) → ι =>
        (structureAddSheaf X.left).obj.obj (op (∏ᶜ fun k => U (b k)))) b =
    (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}).map
      (Pi.π (fun b : Fin (n + 1) → ι =>
        (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k)))) b) := by
  change (𝟙 _ ≫ piComparison (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u})
    (fun b : Fin (n + 1) → ι => (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k))))) ≫
      _ = _
  rw [Category.id_comp]
  exact piComparison_comp_π _ _ b

theorem structureCechForgetIso_scalar (a : F) :
    ((forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}).mapHomologicalComplex _).map
      (a • 𝟙 (structureCechComplex X U)) ≫ (structureCechForgetIso X U).hom =
    (structureCechForgetIso X U).hom ≫
      (cechComplexFunctor U).map (structureScalar X a).hom := by
  ext n : 1
  apply Pi.hom_ext (f := fun b : Fin (n + 1) → ι =>
    (structureAddSheaf X.left).obj.obj (op (∏ᶜ fun k => U (b k))))
  intro b
  simp only [comp_f, Category.assoc]
  rw [structureCechForgetIso_hom_f_π]
  change _ = (structureCechForgetIso X U).hom.f n ≫
    Limits.Pi.map (fun b : Fin (n + 1) → ι =>
      (structureScalar X a).hom.app (op (∏ᶜ fun k => U (b k)))) ≫ _
  rw [Pi.map_π, ← Category.assoc]
  erw [structureCechForgetIso_hom_f_π]
  ext z
  change ↑(∏ᶜ fun b : Fin (n + 1) → ι =>
    (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k)))) at z
  change (Pi.π (fun b : Fin (n + 1) → ι =>
    (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k))))) b (a • z) =
      a • (Pi.π (fun b : Fin (n + 1) → ι =>
        (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k))))) b z
  exact map_smul _ _ _

/-- Forgetting the structural field on homology agrees with the actual additive Cech complex. -/
def structureCechAdditiveHomologyIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}).obj ((structureCechComplex X U).homology n) ≅
      ((cechComplexFunctor U).obj (structureAddSheaf X.left).obj).homology n :=
  (((structureCechComplex X U).sc n).mapHomologyIso
    (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u})).symm ≪≫
      (homologyFunctor AddCommGrpCat.{u} (.up ℕ) n).mapIso (structureCechForgetIso X U)

private theorem moduleHomologyMap_scalar (C : CochainComplex (ModuleCat.{u} F) ℕ)
    (a : F) (n : ℕ) : homologyMap (a • 𝟙 C) n = a • 𝟙 (C.homology n) := by
  change ShortComplex.homologyMap (a • 𝟙 (C.sc n)) = _
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

theorem structureCechAdditiveHomologyIso_scalar (n : ℕ) (a : F)
    (x : (structureCechComplex X U).homology n) :
    (structureCechAdditiveHomologyIso X U n).hom (a • x) =
      homologyMap ((cechComplexFunctor U).map (structureScalar X a).hom) n
        ((structureCechAdditiveHomologyIso X U n).hom x) := by
  let G := forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}
  let C := structureCechComplex X U
  let α := a • 𝟙 C
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor (ModuleCat.{u} F) (.up ℕ) n).map α) G
  have hc := congrArg (fun g => homologyMap g n) (structureCechForgetIso_scalar X U a)
  simp only [homologyMap_comp] at hc
  have h : G.map (homologyMap α n) ≫ (structureCechAdditiveHomologyIso X U n).hom =
      (structureCechAdditiveHomologyIso X U n).hom ≫
        homologyMap ((cechComplexFunctor U).map (structureScalar X a).hom) n := by
    dsimp only [structureCechAdditiveHomologyIso, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc]
    erw [hn]
    rw [Category.assoc]
    exact congrArg (fun k => ((C.sc n).mapHomologyIso G).inv ≫ k) hc
  rw [moduleHomologyMap_scalar] at h
  exact ConcreteCategory.congr_hom h x

local instance structureUnitQuasicoherent (Y : Scheme.{u}) :
    (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent := by
  let e : SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit Y.ringCatSheaf := coproductUniqueIso _
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e (by infer_instance)

variable (hcover : iSup U = ⊤)
variable (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
variable (R : InjectiveResolution (structureAddSheaf X.left))

/-- The positive Cech computation is linear for the original structural field action. -/
def structureCechCohomologyLinearEquiv (n : ℕ) :
    (structureCechComplex X U).homology (n + 1) ≃ₗ[F]
      structureCohomology F X (n + 1) where
  __ := (structureCechAdditiveHomologyIso X U (n + 1)).addCommGroupIsoToAddEquiv.trans
    (moduleCechCohomologyAddEquiv U (SheafOfModules.unit X.left.ringCatSheaf) R hcover haff n)
  map_smul' a x := by
    change moduleCechCohomologyAddEquiv U (SheafOfModules.unit X.left.ringCatSheaf) R hcover haff n
        ((structureCechAdditiveHomologyIso X U (n + 1)).hom (a • x)) = _
    rw [structureCechAdditiveHomologyIso_scalar]
    let φ : InjectiveResolution.Hom R R (moduleScalar X (SheafOfModules.unit
      X.left.ringCatSheaf) a) :=
      ⟨InjectiveResolution.desc (moduleScalar X (SheafOfModules.unit X.left.ringCatSheaf) a) R R,
        by simp⟩
    exact moduleCechCohomologyAddEquiv_scalar X (SheafOfModules.unit X.left.ringCatSheaf)
      R U hcover haff a φ n _

end Scalars


section TensorGeometricMap
open scoped TensorProduct
variable {F : Type u} [Field F] (K : Type u) [Field K] [Algebra F K]

/-- The literal unit m ↦ 1 ⊗ m of field scalar extension, on additive groups. -/
def fieldTensorUnit : forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u} ⟶
    fieldTensorFunctor (F := F) K ⋙ forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u} where
  app M := AddCommGrpCat.ofHom (TensorProduct.mk F K M 1).toAddMonoidHom
  naturality M N g := by
    ext x
    change (1 : K) ⊗ₜ[F] g.hom x = g.hom.baseChange K ((1 : K) ⊗ₜ[F] x)
    simp

variable (X : FScheme F) {ι : Type u} [Finite ι] (U : ι → X.left.Opens)

private theorem tensorCechCoefficientIso_f_π (n : ℕ) (b : Fin (n + 1) → ι) :
    (CategoryTheory.Cech.finiteCechComplexCoefficientIso (fieldTensorFunctor (F := F) K) U
      (structureSectionsPresheaf X)).hom.f n ≫
        Pi.π (fun b : Fin (n + 1) → ι =>
          (fieldTensorFunctor (F := F) K).obj
            ((structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k))))) b =
    (fieldTensorFunctor (F := F) K).map
      (Pi.π (fun b : Fin (n + 1) → ι =>
        (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k)))) b) := by
  change (𝟙 _ ≫ piComparison (fieldTensorFunctor (F := F) K)
    (fun b : Fin (n + 1) → ι => (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k))))) ≫
      _ = _
  rw [Category.id_comp]
  exact piComparison_comp_π _ _ b

/-- The original tensor comparison retains its literal component map on every Cech intersection. -/
theorem structureCechBaseChangeMap_f_π (n : ℕ) (b : Fin (n + 1) → ι) :
    (structureCechBaseChangeMap K X U).f n ≫
      Pi.π (fun b : Fin (n + 1) → ι =>
        (structureSectionsPresheaf (fieldBaseChange K X)).obj
          (op (∏ᶜ fun k => fieldBaseChangeProjection K X ⁻¹ᵁ U (b k)))) b =
    (fieldTensorFunctor (F := F) K).map
      (Pi.π (fun b : Fin (n + 1) → ι =>
        (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k)))) b) ≫
      (structureSectionsTensorComparison K X).app (op (∏ᶜ fun k => U (b k))) ≫
        (structureSectionsPresheaf (fieldBaseChange K X)).map
          (PreservesProduct.iso (Opens.map (fieldBaseChangeProjection K X).base)
            (fun k : Fin (n + 1) => U (b k))).inv.op := by
  change ((CategoryTheory.Cech.finiteCechComplexCoefficientIso (fieldTensorFunctor (F := F) K) U
      (structureSectionsPresheaf X)).hom.f n ≫
    Limits.Pi.map (fun b : Fin (n + 1) → ι =>
      (structureSectionsTensorComparison K X).app (op (∏ᶜ fun k => U (b k)))) ≫
    (Pi.mapIso (fun b : Fin (n + 1) → ι =>
      (structureSectionsPresheaf (fieldBaseChange K X)).mapIso
        (PreservesProduct.iso (Opens.map (fieldBaseChangeProjection K X).base)
          (fun k : Fin (n + 1) => U (b k))).op.symm)).hom) ≫ _ = _
  simp only [Category.assoc]
  erw [Pi.mapIso_hom_π]
  erw [Pi.map_π_assoc]
  rw [← Category.assoc]
  erw [tensorCechCoefficientIso_f_π]
  rfl

/-- The genuine scalar-extension unit on the original Cech complex. -/
def structureCechTensorUnitMap :
    ((forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (structureCechComplex X U) ⟶
      ((forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (((fieldTensorFunctor (F := F) K).mapHomologicalComplex _).obj (structureCechComplex X
          U)) :=
  (NatTrans.mapHomologicalComplex (fieldTensorUnit (F := F) K) _).app (structureCechComplex X U)

omit [Finite ι] in
theorem structureCechTensorUnitMap_f_apply (n : ℕ) (x : (structureCechComplex X U).X n) :
    (structureCechTensorUnitMap K X U).f n x = (1 : K) ⊗ₜ[F] x := rfl

/-- Projection formula for the actual geometric Cech map. -/
theorem additiveCechGeometricMap_f_π {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} (U : ι → Y.Opens)
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback f).obj A ⟶ B) (n : ℕ) (b : Fin (n + 1) → ι) :
    (additiveCechGeometricMap f U A B a).f n ≫
      Pi.π (fun b : Fin (n + 1) → ι => B.obj.obj (op (∏ᶜ fun k => f ⁻¹ᵁ U (b k)))) b =
    Pi.π (fun b : Fin (n + 1) → ι => A.obj.obj (op (∏ᶜ fun k => U (b k)))) b ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _ a).hom.app
        (op (∏ᶜ fun k => U (b k))) ≫
        B.obj.map (PreservesProduct.iso (Opens.map f.base)
          (fun k : Fin (n + 1) => U (b k))).inv.op := by
  change (Limits.Pi.map (fun b : Fin (n + 1) → ι =>
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _ a).hom.app
        (op (∏ᶜ fun k => U (b k)))) ≫
      (Pi.mapIso (fun b : Fin (n + 1) → ι => B.obj.mapIso
        (PreservesProduct.iso (Opens.map f.base) (fun k : Fin (n + 1) => U (b
          k))).op.symm)).hom) ≫ _ = _
  rw [Category.assoc]
  erw [Pi.mapIso_hom_π, Pi.map_π_assoc]
  rfl

/-- The tensor comparison on 1 ⊗ sections is precisely the original geometric Cech map. -/
theorem structureCechTensor_geometric_square :
    structureCechTensorUnitMap K X U ≫
      ((forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (structureCechBaseChangeMap K X U) ≫
      (structureCechForgetIso (fieldBaseChange K X)
        (fun i => fieldBaseChangeProjection K X ⁻¹ᵁ U i)).hom =
    (structureCechForgetIso X U).hom ≫
      additiveCechGeometricMap (fieldBaseChangeProjection K X) U
        (structureAddSheaf X.left) (structureAddSheaf (fieldBaseChange K X).left)
        (structurePullbackMap (fieldBaseChangeProjection K X)) := by
  let G := forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}
  let f := fieldBaseChangeProjection K X
  ext n : 1
  apply Pi.hom_ext (f := fun b : Fin (n + 1) → ι =>
    (structureAddSheaf (fieldBaseChange K X).left).obj.obj (op (∏ᶜ fun k => f ⁻¹ᵁ U (b k))))
  intro b
  simp only [comp_f, Category.assoc]
  erw [structureCechForgetIso_hom_f_π]
  change (structureCechTensorUnitMap K X U).f n ≫ G.map ((structureCechBaseChangeMap K X U).f n) ≫
    G.map (Pi.π (fun b : Fin (n + 1) → ι => (structureSectionsPresheaf (fieldBaseChange K X)).obj
      (op (∏ᶜ fun k => f ⁻¹ᵁ U (b k)))) b) = _
  rw [← G.map_comp]
  erw [structureCechBaseChangeMap_f_π]
  rw [additiveCechGeometricMap_f_π]
  have hadj :
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _
        (structurePullbackMap f) = structurePushforwardMap f :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _
      _).apply_symm_apply _
  rw [hadj]
  conv_rhs => rw [← Category.assoc]
  erw [structureCechForgetIso_hom_f_π]
  ext x
  change ↑((structureCechComplex X U).X n) at x
  simp only [Functor.map_comp, AddCommGrpCat.comp_apply, structureCechTensorUnitMap_f_apply]
  change ((structureSectionsPresheaf (fieldBaseChange K X)).map
      (PreservesProduct.iso (Opens.map f.base) (fun k : Fin (n + 1) => U (b k))).inv.op)
      ((structureSectionsTensorComparison K X).app (op (∏ᶜ fun k => U (b k)))
        (((Pi.π (fun b : Fin (n + 1) → ι =>
          (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (b k)))) b).hom.baseChange K)
            ((1 : K) ⊗ₜ[F] x))) = _
  rw [LinearMap.baseChange_tmul, structureSectionsTensorComparison_app_tmul, one_smul]
  rfl

end TensorGeometricMap

section TransportedTensorIso
open scoped TensorProduct
variable {F : Type u} [Field F]

/-- The actual linear Cech computation for an affine open cover of a separated field scheme. -/
def structureAffineCechCohomologyLinearEquiv (X : FScheme F) [IsSeparated X.hom]
    {ι : Type u} (U : ι → X.left.Opens) (hcover : iSup U = ⊤)
    (haff : ∀ i, IsAffineOpen (U i))
    (R : InjectiveResolution (structureAddSheaf X.left)) (n : ℕ) :
    (structureCechComplex X U).homology (n + 1) ≃ₗ[F]
      structureCohomology F X (n + 1) := by
  let : X.left.IsSeparated := ⟨by rw [← terminal.comp_from X.hom]; infer_instance⟩
  exact structureCechCohomologyLinearEquiv X U hcover (isAffineOpen_cechTuple U haff) R n

variable (K : Type u) [Field K] [Algebra F K]
variable (X : FScheme F) [IsSeparated X.hom]
variable {ι : Type u} [Finite ι] (U : ι → X.left.Opens) (hcover : iSup U = ⊤)
variable (haff : ∀ i, IsAffineOpen (U i))
variable (R : InjectiveResolution (structureAddSheaf X.left))
variable (S : InjectiveResolution (structureAddSheaf (fieldBaseChange K X).left))

local instance fieldBaseChangeSeparated : IsSeparated (fieldBaseChange K X).hom :=
  MorphismProperty.pullback_snd _ _ (inferInstance : IsSeparated X.hom)

include haff in
omit [IsSeparated X.hom] [Finite ι] in
theorem fieldBaseChange_affineCover (i : ι) :
    IsAffineOpen (fieldBaseChangeProjection K X ⁻¹ᵁ U i) := by
  let : IsAffineHom (fieldBaseChangeProjection K X) :=
    MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom
      (Spec.map (CommRingCat.ofHom (algebraMap F K))))
  exact (haff i).preimage _

/-- The actual Cech tensor isomorphism transported to the unchanged structure-cohomology objects.
Its equality with the pre-existing canonical map is proved separately. -/
def structureCechTransportedBaseChangeEquiv (n : ℕ) :
    K ⊗[F] structureCohomology F X (n + 1) ≃ₗ[K]
      structureCohomology K (fieldBaseChange K X) (n + 1) :=
  ((structureAffineCechCohomologyLinearEquiv X U hcover haff R n).symm.baseChange F K _ _).trans
    ((structureCechHomologyBaseChangeIso K X U haff (n + 1)).toLinearEquiv.trans
      (structureAffineCechCohomologyLinearEquiv (fieldBaseChange K X)
        (fun i => fieldBaseChangeProjection K X ⁻¹ᵁ U i)
        ((fieldBaseChangeProjection K X).iSup_preimage_eq_top hcover)
        (fieldBaseChange_affineCover K X U haff) S n))

@[simp]
theorem structureCechTransportedBaseChangeEquiv_tmul (n : ℕ) (k : K)
    (x : structureCohomology F X (n + 1)) :
    structureCechTransportedBaseChangeEquiv K X U hcover haff R S n (k ⊗ₜ[F] x) =
    structureAffineCechCohomologyLinearEquiv (fieldBaseChange K X)
      (fun i => fieldBaseChangeProjection K X ⁻¹ᵁ U i)
      ((fieldBaseChangeProjection K X).iSup_preimage_eq_top hcover)
      (fieldBaseChange_affineCover K X U haff) S n
      ((structureCechHomologyBaseChangeIso K X U haff (n + 1)).hom
        (k ⊗ₜ[F] (structureAffineCechCohomologyLinearEquiv X U hcover haff R n).symm x)) := rfl

end TransportedTensorIso


section CanonicalTensorHomology
section CoefficientCoherence
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [F.PreservesHomology] [G.PreservesHomology]
local instance : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
local instance : PreservesFiniteColimits F := Functor.preservesFiniteColimits_of_preservesHomology F
local instance : PreservesFiniteLimits G := Functor.preservesFiniteLimits_of_preservesHomology G
local instance : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
variable (S : ShortComplex C)

/-- Compatibility alias for the generic identity comparison data. -/
abbrev compositeHomologyDataIdentity :=
  CategoryTheory.ShortComplex.compositeHomologyDataIdentity F G S

/-- Compatibility theorem for the generic composition of canonical homology comparisons. -/
theorem mapHomologyIso_comp_hom :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom :=
  CategoryTheory.ShortComplex.mapHomologyIso_comp_hom F G S

end CoefficientCoherence

section FieldTensorHomology
open HomologicalComplex _root_.AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct
variable {F : Type u} [Field F] (K : Type u) [Field K] [Algebra F K]

theorem fieldTensorUnit_app_apply (M : ModuleCat.{u} F) (x : M) :
    (fieldTensorUnit (F := F) K).app M x = (1 : K) ⊗ₜ[F] x := rfl

local instance : PreservesFiniteColimits (fieldTensorFunctor (F := F) K) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The scalar-extension unit on homology is the actual tensor m ↦ 1 ⊗ m under the canonical
  homology comparisons. -/
@[reassoc]
theorem fieldTensorUnit_homology (C : CochainComplex (ModuleCat.{u} F) ℕ) (n : ℕ) :
    (fieldTensorUnit (F := F) K).app (C.homology n) ≫
      (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}).map
        ((C.sc n).mapHomologyIso (fieldTensorFunctor (F := F) K)).inv =
    ((C.sc n).mapHomologyIso (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u})).inv ≫
      homologyMap ((NatTrans.mapHomologicalComplex (fieldTensorUnit (F := F) K) _).app C) n ≫
        (((((fieldTensorFunctor (F := F) K).mapHomologicalComplex _).obj C).sc n).mapHomologyIso
          (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u})).hom := by
  let T := fieldTensorFunctor (F := F) K
  let G := forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}
  have h := NatTrans.app_homology (fieldTensorUnit (F := F) K) (C.sc n)
  erw [mapHomologyIso_comp_hom T G (C.sc n)] at h
  erw [h]
  simp only [Category.assoc]
  erw [← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]
  rfl

/-- Homology of a scalar-extension unit followed by a genuine complex map. -/
@[reassoc]
theorem fieldTensorUnit_homology_map (C : CochainComplex (ModuleCat.{u} F) ℕ)
    (D : CochainComplex (ModuleCat.{u} K) ℕ)
    (β : ((fieldTensorFunctor (F := F) K).mapHomologicalComplex _).obj C ⟶ D) (n : ℕ) :
    (fieldTensorUnit (F := F) K).app (C.homology n) ≫
      (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}).map
        (((C.sc n).mapHomologyIso (fieldTensorFunctor (F := F) K)).inv ≫ homologyMap β n) ≫
      ((D.sc n).mapHomologyIso (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u})).inv =
    ((C.sc n).mapHomologyIso (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u})).inv ≫
      homologyMap ((NatTrans.mapHomologicalComplex (fieldTensorUnit (F := F) K) _).app C ≫
        ((forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}).mapHomologicalComplex _).map β) n := by
  let G := forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}
  let T := fieldTensorFunctor (F := F) K
  have hn : G.map (homologyMap β n) ≫ ((D.sc n).mapHomologyIso G).inv =
    ((((T.mapHomologicalComplex _).obj C).sc n).mapHomologyIso G).inv ≫
      homologyMap ((G.mapHomologicalComplex _).map β) n :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((shortComplexFunctor (ModuleCat.{u} K) (.up ℕ) n).map β) G
  rw [Functor.map_comp]
  simp only [Category.assoc, homologyMap_comp]
  erw [fieldTensorUnit_homology_assoc]
  erw [hn]
  erw [Iso.hom_inv_id_assoc]

variable (X : FScheme F) {ι : Type u} [Finite ι] (U : ι → X.left.Opens)

/-- The actual homology map obtained from flat tensoring and the original Cech tensor map. -/
def structureCechHomologyBaseChangeMap (n : ℕ) :
    (fieldTensorFunctor (F := F) K).obj ((structureCechComplex X U).homology n) ⟶
      (structureCechComplex (fieldBaseChange K X)
        (fun i => fieldBaseChangeProjection K X ⁻¹ᵁ U i)).homology n :=
  (((structureCechComplex X U).sc n).mapHomologyIso (fieldTensorFunctor (F := F) K)).inv ≫
    homologyMap (structureCechBaseChangeMap K X U) n

@[simp]
theorem structureCechHomologyBaseChangeIso_hom [IsSeparated X.hom]
    (haff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (structureCechHomologyBaseChangeIso K X U haff n).hom =
      structureCechHomologyBaseChangeMap K X U n := rfl

/-- On 1 ⊗ cohomology, the canonical Cech tensor comparison is precisely geometric pullback. -/
theorem structureCechHomologyBaseChangeMap_one_tmul (n : ℕ)
    (x : (structureCechComplex X U).homology n) :
    (structureCechAdditiveHomologyIso (fieldBaseChange K X)
      (fun i => fieldBaseChangeProjection K X ⁻¹ᵁ U i) n).hom
        (structureCechHomologyBaseChangeMap K X U n ((1 : K) ⊗ₜ[F] x)) =
    homologyMap (additiveCechGeometricMap (fieldBaseChangeProjection K X) U
      (structureAddSheaf X.left) (structureAddSheaf (fieldBaseChange K X).left)
      (structurePullbackMap (fieldBaseChangeProjection K X))) n
        ((structureCechAdditiveHomologyIso X U n).hom x) := by
  let G := forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}
  let C := structureCechComplex X U
  let D := structureCechComplex (fieldBaseChange K X)
    (fun i => fieldBaseChangeProjection K X ⁻¹ᵁ U i)
  have ht := congrArg (fun q => q ≫ homologyMap
      (structureCechForgetIso (fieldBaseChange K X)
        (fun i => fieldBaseChangeProjection K X ⁻¹ᵁ U i)).hom n)
    (fieldTensorUnit_homology_map K C D (structureCechBaseChangeMap K X U) n)
  have hc := congrArg (fun g => homologyMap g n) (structureCechTensor_geometric_square K X U)
  simp only [homologyMap_comp, Category.assoc] at ht hc
  have h := ht.trans (congrArg (fun q => ((C.sc n).mapHomologyIso
    (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u})).inv ≫ q) hc)
  change (fieldTensorUnit (F := F) K).app (C.homology n) ≫
      G.map (structureCechHomologyBaseChangeMap K X U n) ≫
        (structureCechAdditiveHomologyIso (fieldBaseChange K X)
          (fun i => fieldBaseChangeProjection K X ⁻¹ᵁ U i) n).hom =
    (structureCechAdditiveHomologyIso X U n).hom ≫
      homologyMap (additiveCechGeometricMap (fieldBaseChangeProjection K X) U
        (structureAddSheaf X.left) (structureAddSheaf (fieldBaseChange K X).left)
        (structurePullbackMap (fieldBaseChangeProjection K X))) n at h
  have hx := ConcreteCategory.congr_hom h x
  simp only [ConcreteCategory.comp_apply, fieldTensorUnit_app_apply] at hx
  exact hx

end FieldTensorHomology

end CanonicalTensorHomology

section OriginalCanonicalTensorMap
open scoped TensorProduct
attribute [local instance] structureUnitQuasicoherent fieldBaseChangeSeparated
variable {F : Type u} [Field F] (K : Type u) [Field K] [Algebra F K]
variable (X : FScheme F) [IsSeparated X.hom]
variable {ι : Type u} [Finite ι] (U : ι → X.left.Opens) (hcover : iSup U = ⊤)
variable (haff : ∀ i, IsAffineOpen (U i))
variable (R : InjectiveResolution (structureAddSheaf X.left))
variable (S : InjectiveResolution (structureAddSheaf (fieldBaseChange K X).left))

/-- The transported actual Cech tensor equivalence agrees with the original cohomology pullback
  on 1 ⊗ x. -/
theorem structureCechTransportedBaseChangeEquiv_one_tmul (n : ℕ)
    (x : structureCohomology F X (n + 1)) :
    structureCechTransportedBaseChangeEquiv K X U hcover haff R S n ((1 : K) ⊗ₜ[F] x) =
      structureCohomologyPullback (fieldBaseChangeProjection K X) (n + 1) x := by
  let : X.left.IsSeparated := ⟨by rw [← terminal.comp_from X.hom]; infer_instance⟩
  let : (fieldBaseChange K X).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (fieldBaseChange K X).hom]
    infer_instance⟩
  let V := fun i => fieldBaseChangeProjection K X ⁻¹ᵁ U i
  let e := structureAffineCechCohomologyLinearEquiv X U hcover haff R n
  rw [structureCechTransportedBaseChangeEquiv_tmul, structureCechHomologyBaseChangeIso_hom]
  change moduleCechCohomologyAddEquiv V
      (SheafOfModules.unit (fieldBaseChange K X).left.ringCatSheaf) S
      ((fieldBaseChangeProjection K X).iSup_preimage_eq_top hcover)
      (isAffineOpen_cechTuple V (fieldBaseChange_affineCover K X U haff)) n
      ((structureCechAdditiveHomologyIso (fieldBaseChange K X) V (n + 1)).hom
        (structureCechHomologyBaseChangeMap K X U (n + 1) ((1 : K) ⊗ₜ[F] e.symm x))) = _
  rw [structureCechHomologyBaseChangeMap_one_tmul]
  erw [moduleCechCohomologyAddEquiv_geometric (fieldBaseChangeProjection K X) U
    (SheafOfModules.unit X.left.ringCatSheaf)
    (SheafOfModules.unit (fieldBaseChange K X).left.ringCatSheaf) R S
    hcover ((fieldBaseChangeProjection K X).iSup_preimage_eq_top hcover)
    (isAffineOpen_cechTuple U haff)
    (isAffineOpen_cechTuple V (fieldBaseChange_affineCover K X U haff))
    (structurePullbackMap (fieldBaseChangeProjection K X))]
  change structureCohomologyPullback (fieldBaseChangeProjection K X) (n + 1) (e (e.symm x)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The actual transported tensor equivalence has exactly the pre-existing canonical base-change
  linear map. -/
theorem structureCechTransportedBaseChangeEquiv_eq (n : ℕ) :
    (structureCechTransportedBaseChangeEquiv K X U hcover haff R S n).toLinearMap =
      structureCohomologyBaseChangeMap K X (n + 1) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul k x =>
    have ht : k ⊗ₜ[F] x = k • ((1 : K) ⊗ₜ[F] x) := TensorProduct.tmul_eq_smul_one_tmul k x
    change structureCechTransportedBaseChangeEquiv K X U hcover haff R S n (k ⊗ₜ[F] x) = _
    rw [ht, map_smul, map_smul, structureCechTransportedBaseChangeEquiv_one_tmul,
      structureCohomologyBaseChangeMap_tmul, one_smul]
    rfl
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

include hcover haff in
/-- Positive canonical structure-sheaf base change from an actual finite affine cover. -/
theorem structureCohomologyBaseChangeMap_bijective_succ_of_finite_affine_cover (n : ℕ) :
    Function.Bijective (structureCohomologyBaseChangeMap K X (n + 1)) := by
  let R := injectiveResolution (structureAddSheaf X.left)
  let S := injectiveResolution (structureAddSheaf (fieldBaseChange K X).left)
  rw [← structureCechTransportedBaseChangeEquiv_eq K X U hcover haff R S n]
  exact (structureCechTransportedBaseChangeEquiv K X U hcover haff R S n).bijective

end OriginalCanonicalTensorMap

end AlgebraicGeometry.Scheme.Cohomology
