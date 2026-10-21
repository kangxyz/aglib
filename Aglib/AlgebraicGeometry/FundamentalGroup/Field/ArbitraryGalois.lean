/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.OverRing
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericRestriction
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Reconstruction from the original Galois ambient field

For an arbitrary algebraic Galois extension Ω/K, coherent evaluation on finite
subfields reconstructs the original K-automorphism of Ω. The resulting
continuous equivalence uses the actual Ω-valued fibre functor. A geometric
interpretation additionally retains algebraic closedness and the explicit
Galois-category and fibre-functor inputs at its consumers.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory FintypeCatDiscrete Topology
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.GroupCohomology.ContinuousH1
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing Algebra.FiniteEtale.TorsorExtension

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.Arbitrary

universe u

/-- An identity-coefficient pullback along a surjective group map is injective
on H1 even when the target action is presented independently. -/
theorem identityPullback_onH1_injective {G J M : Type*}
    [Group G] [TopologicalSpace G] [Group J] [TopologicalSpace J]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction J M] [ContinuousSMul J M]
    (φ : J →ₜ* G) (hφ : Function.Surjective φ)
    (f : PullbackMap (A := M) (B := M) φ) (hid : ∀ m, f m = m) :
    Function.Injective f.onH1 := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := classOf_surjective G M x
  obtain ⟨d, rfl⟩ := classOf_surjective G M y
  rw [_root_.GroupCohomology.ContinuousH1.PullbackMap.onH1_classOf,
    _root_.GroupCohomology.ContinuousH1.PullbackMap.onH1_classOf, classOf_eq_iff] at hxy
  obtain ⟨m, hm⟩ := hxy
  apply (classOf_eq_iff G M c d).mpr
  refine ⟨m, ?_⟩
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro g
  obtain ⟨j, rfl⟩ := hφ g
  have hj := congrArg (fun c : Cocycle J M => c.val j) hm
  change j • m - m = f (c.val (φ j)) - f (d.val (φ j)) at hj
  have hsmul : φ j • m = j • m := by
    simpa only [hid] using f.map_smul j m
  change φ j • m - m = c.val (φ j) - d.val (φ j)
  rw [hsmul]
  simpa only [hid] using hj

section FieldMap
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [hGalois : IsGalois K Ω]

/-- The original K-automorphism, with its ambient field unchanged. -/
abbrev asAutomorphism (σ : Ω ≃ₐ[K] Ω) : Ω ≃ₐ[K] Ω := σ

theorem galoisToFibre_act (σ : Ω ≃ₐ[K] Ω)
    (Y : Scheme.FiniteEtale (Spec (.of K))) (p : Fiber (basePoint K Ω) Y) :
    (galoisToFibre K K Ω σ).hom.app Y p =
      AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing.act K K Ω σ Y p := rfl

section FiniteFields

variable (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Every finite separable extension defines its actual finite etale cover. -/
def finiteFieldCover : Scheme.FiniteEtale (Spec (CommRingCat.of K)) := by
  letI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  letI : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp
    (inferInstance : Algebra.FiniteType K L)
  letI : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  refine ⟨Over.mk (basePoint K L), ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)

/-- A field embedding gives the corresponding actual point lift. -/
def fieldLift (φ : L →ₐ[K] Ω) :
    Fiber (basePoint K Ω) (finiteFieldCover K L) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x)

/-- Recover the embedding from an actual scheme-point lift by full faithfulness of `Spec`. -/
def liftToEmbedding (p : Fiber (basePoint K Ω) (finiteFieldCover K L)) :
    L →ₐ[K] Ω where
  toRingHom := (Spec.preimage p.left).hom
  commutes' x := by
    have h := Over.w p
    change p.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Ω))) at h
    rw [← Spec.map_preimage p.left, ← Spec.map_comp, Spec.map_inj] at h
    exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of (Ω) => f.hom x) h

omit hGalois in
@[simp] theorem liftToEmbedding_fieldLift [_hGalois : IsGalois K Ω] (φ : L →ₐ[K] Ω) :
    liftToEmbedding K Ω L (fieldLift K Ω L φ) = φ := by
  apply AlgHom.ext
  intro x
  change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom x = φ x
  rw [Spec.preimage_map]
  rfl

omit hGalois in
@[simp] theorem fieldLift_liftToEmbedding [_hGalois : IsGalois K Ω]
    (p : Fiber (basePoint K Ω) (finiteFieldCover K L)) :
    fieldLift K Ω L (liftToEmbedding K Ω L p) = p := by
  apply Over.OverMorphism.ext
  exact Spec.map_preimage p.left

/-- The affine field cover fibre is the set of field embeddings, without a classification
  assumption. -/
def fieldFiberEquiv : Fiber (basePoint K Ω) (finiteFieldCover K L) ≃
    (L →ₐ[K] Ω) where
  toFun := liftToEmbedding K Ω L
  invFun := fieldLift K Ω L
  left_inv := fieldLift_liftToEmbedding K Ω L
  right_inv := liftToEmbedding_fieldLift K Ω L

omit hGalois in
@[simp] theorem act_fieldLift [_hGalois : IsGalois K Ω] (σ : (Ω ≃ₐ[K] Ω))
    (φ : L →ₐ[K] Ω) :
    AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing.act K K Ω σ (finiteFieldCover K L)
      (fieldLift K Ω L φ) =
      fieldLift K Ω L ((asAutomorphism K Ω σ).toAlgHom.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {L} {M : Type u} [Field M] [Algebra K M] [FiniteDimensional K M]
  [Algebra.IsSeparable K M]

/-- An algebra homomorphism gives a morphism of the actual finite field covers. -/
def fieldCoverMap (φ : L →ₐ[K] M) : finiteFieldCover K M ⟶ finiteFieldCover K L :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x))

omit hGalois in
@[simp] theorem fieldLift_map [_hGalois : IsGalois K Ω] (φ : L →ₐ[K] M) (ψ : M →ₐ[K] Ω) :
    fieldLift K Ω M ψ ≫ (fieldCoverMap K φ).hom =
      fieldLift K Ω L (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

@[simp] theorem liftToEmbedding_map (φ : L →ₐ[K] M)
    (p : Fiber (basePoint K Ω) (finiteFieldCover K M)) :
    liftToEmbedding K Ω L (p ≫ (fieldCoverMap K φ).hom) =
      (liftToEmbedding K Ω M p).comp φ := by
  rw [← fieldLift_liftToEmbedding K Ω M p, fieldLift_map]
  simp only [liftToEmbedding_fieldLift]

/-- A natural fibre automorphism acts on the embeddings of each finite field. -/
def embeddingAction (a : FiberAutGroup (basePoint K Ω)) (φ : L →ₐ[K] Ω) :
    L →ₐ[K] Ω :=
  liftToEmbedding K Ω L (a.hom.app (finiteFieldCover K L) (fieldLift K Ω L φ))

theorem embeddingAction_comp (a : FiberAutGroup (basePoint K Ω)) (φ : L →ₐ[K] M)
    (ψ : M →ₐ[K] Ω) :
    embeddingAction K Ω a (ψ.comp φ) = (embeddingAction K Ω a ψ).comp φ := by
  have h := congrArg (liftToEmbedding K Ω L)
    (evaluate_naturality (basePoint K Ω) a (fieldCoverMap K φ) (fieldLift K Ω M ψ))
  simpa only [fiberToFinite_map, fieldLift_map, liftToEmbedding_map, embeddingAction] using h.symm

end FiniteFields

section Reconstruction


/-- The image of the inclusion point of a finite subfield. -/
def subfieldEmbedding (a : FiberAutGroup (basePoint K Ω))
    (L : IntermediateField K (Ω)) [FiniteDimensional K L] :
    L →ₐ[K] Ω := embeddingAction K Ω a L.val

theorem subfieldEmbedding_compat (a : FiberAutGroup (basePoint K Ω))
    {L M : IntermediateField K (Ω)}
    [FiniteDimensional K L] [FiniteDimensional K M] (h : L ≤ M) :
    subfieldEmbedding K Ω a L = (subfieldEmbedding K Ω a M).comp (IntermediateField.inclusion h) :=
  embeddingAction_comp K Ω a (IntermediateField.inclusion h) M.val

/-- Reconstruct the value on an element from its finite simple subfield. -/
def reconstructedValue (a : FiberAutGroup (basePoint K Ω)) (x : Ω) :
    Ω :=
  letI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  subfieldEmbedding K Ω a (IntermediateField.adjoin K {x})
    (IntermediateField.AdjoinSimple.gen K x)

theorem reconstructedValue_eq (a : FiberAutGroup (basePoint K Ω))
    (L : IntermediateField K (Ω)) [FiniteDimensional K L] (x : L) :
    reconstructedValue K Ω a x = subfieldEmbedding K Ω a L x := by
  let : FiniteDimensional K (IntermediateField.adjoin K {x.val}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x.val)
  have h : IntermediateField.adjoin K {x.val} ≤ L :=
    IntermediateField.adjoin_simple_le_iff.mpr x.property
  exact congrArg (fun φ : IntermediateField.adjoin K {x.val} →ₐ[K] Ω =>
    φ (IntermediateField.AdjoinSimple.gen K x.val)) (subfieldEmbedding_compat K Ω a h)

/-- The coherent finite-subfield embeddings form an actual algebra endomorphism. -/
def reconstructedEmbedding (a : FiberAutGroup (basePoint K Ω)) :
    Ω →ₐ[K] Ω where
  toFun := reconstructedValue K Ω a
  map_one' := by
    let : FiniteDimensional K (IntermediateField.adjoin K {(1 : Ω)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    change subfieldEmbedding K Ω a (IntermediateField.adjoin K {1}) 1 = 1
    exact map_one _
  map_mul' x y := by
    let L := IntermediateField.adjoin K {x, y}
    let : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin_pair
      (Algebra.IsIntegral.isIntegral x) (Algebra.IsIntegral.isIntegral y)
    have hx : x ∈ L := IntermediateField.subset_adjoin K {x, y} (by simp)
    have hy : y ∈ L := IntermediateField.subset_adjoin K {x, y} (by simp)
    rw [reconstructedValue_eq K Ω a L ⟨x * y, L.mul_mem hx hy⟩,
      reconstructedValue_eq K Ω a L ⟨x, hx⟩, reconstructedValue_eq K Ω a L ⟨y, hy⟩]
    exact map_mul (subfieldEmbedding K Ω a L) (⟨x, hx⟩ : L) (⟨y, hy⟩ : L)
  map_zero' := by
    let : FiniteDimensional K (IntermediateField.adjoin K {(0 : Ω)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    change subfieldEmbedding K Ω a (IntermediateField.adjoin K {0}) 0 = 0
    exact map_zero _
  map_add' x y := by
    let L := IntermediateField.adjoin K {x, y}
    let : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin_pair
      (Algebra.IsIntegral.isIntegral x) (Algebra.IsIntegral.isIntegral y)
    have hx : x ∈ L := IntermediateField.subset_adjoin K {x, y} (by simp)
    have hy : y ∈ L := IntermediateField.subset_adjoin K {x, y} (by simp)
    rw [reconstructedValue_eq K Ω a L ⟨x + y, L.add_mem hx hy⟩,
      reconstructedValue_eq K Ω a L ⟨x, hx⟩, reconstructedValue_eq K Ω a L ⟨y, hy⟩]
    exact map_add (subfieldEmbedding K Ω a L) (⟨x, hx⟩ : L) (⟨y, hy⟩ : L)
  commutes' x := by
    let L := IntermediateField.adjoin K {algebraMap K (Ω) x}
    let : FiniteDimensional K L :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    change subfieldEmbedding K Ω a L (algebraMap K L x) = _
    exact (subfieldEmbedding K Ω a L).commutes x

/-- Normality of the original algebraic Galois field upgrades the reconstructed embedding to an
  automorphism. -/
def fromFundamentalGroup (a : FiberAutGroup (basePoint K Ω)) : (Ω ≃ₐ[K] Ω) :=
  AlgEquiv.ofBijective (reconstructedEmbedding K Ω a)
    ((reconstructedEmbedding K Ω a).normal_bijective K (Ω) (Ω))

theorem fromFundamentalGroup_subfield (a : FiberAutGroup (basePoint K Ω))
    (L : IntermediateField K (Ω)) [FiniteDimensional K L] (x : L) :
    asAutomorphism K Ω (fromFundamentalGroup K Ω a) x = subfieldEmbedding K Ω a L x :=
  reconstructedValue_eq K Ω a L x

omit hGalois in
/-- An Ω-valued point of an affine finite cover is recovered from its coordinates. -/
theorem point_from_coordinates [_hGalois : IsGalois K Ω] (Y : Scheme.FiniteEtale (Spec
  (CommRingCat.of K)))
    (p : Fiber (basePoint K Ω) Y) :
    letI : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
    Spec.map (CommRingCat.ofHom (pointCoordinates K Ω Y p)) ≫ Y.obj.left.isoSpec.inv = p.left := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  apply (cancel_mono Y.obj.left.isoSpec.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map (p.left.appTop ≫ _) = p.left ≫ Y.obj.left.isoSpec.hom
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_hom, Scheme.isoSpec_hom_naturality]

/-- Every point lift factors through the inclusion point of a finite subfield.
The proof takes the image of the finite global-section algebra in the original algebraic Galois
  field. -/
theorem point_factors_finiteSubfield (Y : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (p : Fiber (basePoint K Ω) Y) :
    ∃ (L : IntermediateField K (Ω)) (hL : FiniteDimensional K L),
      letI := hL
      ∃ f : finiteFieldCover K L ⟶ Y,
        (fiberToFinite (basePoint K Ω)).map f (fieldLift K Ω L L.val) = p := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  let A := Γ(Y.obj.left, ⊤)
  let a : K →+* A :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Y.obj.hom.appTop).hom
  let : Algebra K A := a.toAlgebra
  have ha : a.Finite :=
    Y.obj.hom.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  let : Module.Finite K A := ha
  let φ : A →ₐ[K] Ω :=
    { toRingHom := pointCoordinates K Ω Y p
      commutes' := fun x => by
        have he : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Y.obj.hom.appTop) ≫
            (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (Ω))).hom) =
              CommRingCat.ofHom (algebraMap K (Ω)) := by
          rw [Category.assoc, ← Category.assoc Y.obj.hom.appTop p.left.appTop,
            ← Scheme.Hom.comp_appTop, Over.w p]
          change (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
            ((Spec.map (CommRingCat.ofHom (algebraMap K (Ω)))).appTop ≫ _) = _
          rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
        exact congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of (Ω) =>
          h.hom x) he }
  let S := φ.range
  let : FiniteDimensional K S :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  let L := S.toIntermediateField' (@Field.toIsField S (fieldOfFiniteDimensional K S))
  have hL : FiniteDimensional K L := inferInstanceAs (FiniteDimensional K S)
  let : FiniteDimensional K L := hL
  let ψ : A →ₐ[K] L := φ.rangeRestrict
  have hstruct : Y.obj.left.isoSpec.inv ≫ Y.obj.hom =
      Spec.map (CommRingCat.ofHom a) := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  let f : finiteFieldCover K L ⟶ Y := ObjectProperty.homMk
    (Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.obj.left.isoSpec.inv) (by
      change (Spec.map _ ≫ Y.obj.left.isoSpec.inv) ≫ Y.obj.hom = Spec.map _
      rw [Category.assoc, hstruct, ← Spec.map_comp]
      congr 1
      ext x
      exact congrArg (fun z : L => (z : Ω)) (ψ.commutes x)))
  refine ⟨L, hL, f, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ (Spec.map _ ≫ Y.obj.left.isoSpec.inv) = p.left
  rw [← Category.assoc, ← Spec.map_comp]
  exact point_from_coordinates K Ω Y p

/-- The reconstructed Galois element has the prescribed action on every finite cover. -/
theorem galoisToFibre_fromFundamentalGroup (a : FiberAutGroup (basePoint K Ω)) :
    galoisToFibre K K Ω (fromFundamentalGroup K Ω a) = a := by
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro p
  obtain ⟨L, hL, f, hp⟩ := point_factors_finiteSubfield K Ω Y p
  let : FiniteDimensional K L := hL
  have hLact : (galoisToFibre K K Ω (fromFundamentalGroup K Ω a)).hom.app
      (finiteFieldCover K L) (fieldLift K Ω L L.val) =
        a.hom.app (finiteFieldCover K L) (fieldLift K Ω L L.val) := by
    apply (fieldFiberEquiv K Ω L).injective
    change liftToEmbedding K Ω L (AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing.act K K
      Ω _ _ _) = subfieldEmbedding K Ω a L
    rw [act_fieldLift, liftToEmbedding_fieldLift]
    apply AlgHom.ext
    exact fromFundamentalGroup_subfield K Ω a L
  rw [← hp, ← evaluate_naturality (basePoint K Ω), hLact,
    evaluate_naturality (basePoint K Ω)]

/-- Finite subfields detect every element of the actual original Galois group. -/
theorem galoisToFibre_injective : Function.Injective (galoisToFibre K K Ω) := by
  intro σ τ h
  change asAutomorphism K Ω σ = asAutomorphism K Ω τ
  apply AlgEquiv.ext
  intro x
  let L := IntermediateField.adjoin K {x}
  let : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hx : x ∈ L := IntermediateField.subset_adjoin K {x} rfl
  have hp := congrArg (fun a : FiberAutGroup (basePoint K Ω) =>
    a.hom.app (finiteFieldCover K L) (fieldLift K Ω L L.val)) h
  simp only [galoisToFibre_act, act_fieldLift] at hp
  have he := congrArg (liftToEmbedding K Ω L) hp
  simp only [liftToEmbedding_fieldLift] at he
  exact congrArg (fun φ : L →ₐ[K] Ω => φ ⟨x, hx⟩) he

@[simp] theorem fromFundamentalGroup_galoisToFibre (σ : (Ω ≃ₐ[K] Ω)) :
    fromFundamentalGroup K Ω (galoisToFibre K K Ω σ) = σ :=
  galoisToFibre_injective K Ω (galoisToFibre_fromFundamentalGroup K Ω _)

/-- The group isomorphism to natural automorphisms of the Ω-valued finite-etale
fibre functor, obtained from actual finite-subfield reconstruction. A geometric
fibre interpretation additionally uses the original algebraically closed Ω. -/
def fundamentalGroupEquiv : (Ω ≃ₐ[K] Ω) ≃* FiberAutGroup (basePoint K Ω) where
  toFun := galoisToFibre K K Ω
  invFun := fromFundamentalGroup K Ω
  left_inv := fromFundamentalGroup_galoisToFibre K Ω
  right_inv := galoisToFibre_fromFundamentalGroup K Ω
  map_mul' := map_mul (galoisToFibre K K Ω)

/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982, literal local field-map subset.
For the ORIGINAL algebraic Galois Ω/K, the actual galoisToFibre K K Ω is
bijective. IsGalois supplies algebraicity, separability and normality; neither
characteristic zero nor replacement by a chosen algebraic closure is required. -/
theorem galoisToFibre_bijective : Function.Bijective (galoisToFibre K K Ω) :=
  (fundamentalGroupEquiv K Ω).bijective


theorem galoisToFibre_surjective : Function.Surjective (galoisToFibre K K Ω) :=
  (galoisToFibre_bijective K Ω).surjective

/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982, literal local field comparison.
The concrete reconstructed inverse is continuous for the original Krull and
finite-fibre topologies, by compactness and Hausdorffness. -/
def fundamentalGroupContinuousEquiv : (Ω ≃ₐ[K] Ω) ≃ₜ* FiberAutGroup (basePoint K Ω) :=
  { fundamentalGroupEquiv K Ω with
    continuous_toFun := (galoisToFibre K K Ω).continuous
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (fundamentalGroupEquiv K Ω).toEquiv) (galoisToFibre K K Ω).continuous }

@[simp] theorem fundamentalGroupContinuousEquiv_apply (σ : Ω ≃ₐ[K] Ω) :
    fundamentalGroupContinuousEquiv K Ω σ = galoisToFibre K K Ω σ := rfl


/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: arbitrary field fibre-group H1 classes
are distinguished by restriction along the ORIGINAL literal Galois map. -/
theorem galoisRestriction_injective (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction (FiberAutGroup (basePoint K Ω)) M]
    [ContinuousSMul (FiberAutGroup (basePoint K Ω)) M] :
    Function.Injective (restriction M (galoisToFibre K K Ω)) :=
  AlgebraicGeometry.Scheme.FiniteEtale.GenericRestriction.restriction_injective_of_surjective
    (galoisToFibre K K Ω) (galoisToFibre_surjective K Ω)

end Reconstruction
end FieldMap

end AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.Arbitrary
