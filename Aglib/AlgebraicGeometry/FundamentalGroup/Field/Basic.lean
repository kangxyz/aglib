/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Basic
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Topology.Algebra.MulAction

/-!
# Absolute Galois automorphisms acting on finite étale fibres

Construction for `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`, on source bases
`ac804cb2f648f42380e612235b972786506d0b9f` and
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
The accepted scheme fibre and automorphism constructions have SHA256
`593e6b847bd845fa2b13de95a7c0b7991a2cf94b70d27a14ca1d24b5833adaa6` and
`f45f9cb6815524a8b04347d98bd51d0a95dd787e6499cec65af8a8171c31101f`.

The mathematical reference is the Stacks Project, Lemma 58.6.3, tag `0BNE`,
parts (1) and (2), checked at https://stacks.math.columbia.edu/tag/0BNE.
It identifies the field's finite étale fibre with the finite Galois-set
forgetful functor and the resulting profinite groups. Tag `0BND`,
Theorem 58.6.2, is the general fundamental-group theorem.
These references describe the target; no identification is imported as an axiom.

For a characteristic-zero field `F`, the point is the actual scheme morphism
`Spec (AlgebraicClosure F) ⟶ Spec F`. An actual `F`-automorphism `σ` of
`AlgebraicClosure F` acts on a point lift `p` by `Spec.map σ ≫ p`.
The contravariance of `Spec` gives the left-action multiplication convention
`(σ * τ) • p = σ • (τ • p)`.

The forward homomorphism is continuous by embedding each finite fibre into its
global-section coordinate maps and using the open Krull stabilizers of algebraic
elements. For the inverse, a natural fibre automorphism determines compatible
embeddings of finite subfields. They glue to an algebra endomorphism of the
algebraic closure, and normality makes it bijective. Every point lift factors
through the image of its finite coordinate algebra, which is a finite subfield;
naturality along this actual scheme morphism proves the inverse identity on all
covers. Stabilizers of finite-subfield inclusion points prove inverse continuity.

`fundamentalGroupContinuousEquiv` is the resulting topological group isomorphism
in characteristic zero. The forward construction itself uses no characteristic
assumption. No scheme/algebra classification, target-shaped bijectivity premise,
or custom axiom is assumed.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory
open scoped Topology
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois

universe u
variable (F : Type u) [Field F]

/-- The geometric point given by the chosen algebraic closure. -/
abbrev geometricPoint := fieldPoint F (AlgebraicClosure F)

/-- The actual field fundamental group at the algebraic-closure point. -/
abbrev FieldFundamentalGroup := FundamentalGroup (geometricPoint F)

/-- An absolute Galois element as an automorphism of the chosen algebraic closure. -/
abbrev asAutomorphism (σ : Field.absoluteGaloisGroup F) :
    AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ

/-- The scheme endomorphism of the geometric point induced by an actual Galois element. -/
def pointEnd (σ : Field.absoluteGaloisGroup F) :
    Over.mk (geometricPoint F) ⟶ Over.mk (geometricPoint F) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (asAutomorphism F σ).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (asAutomorphism F σ).commutes x)

@[simp] theorem pointEnd_left (σ : Field.absoluteGaloisGroup F) :
    (pointEnd F σ).left = Spec.map (CommRingCat.ofHom (asAutomorphism F σ).toRingHom) := rfl

@[simp] theorem pointEnd_one : pointEnd F 1 = 𝟙 (Over.mk (geometricPoint F)) := by
  apply Over.OverMorphism.ext
  change Spec.map (𝟙 _) = 𝟙 _
  exact Spec.map_id _

/-- `Spec` reverses algebra maps, producing the order needed for precomposition. -/
theorem pointEnd_mul (σ τ : Field.absoluteGaloisGroup F) :
    pointEnd F (σ * τ) = pointEnd F σ ≫ pointEnd F τ := by
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Galois action on an actual lift of the geometric point. -/
def act (σ : Field.absoluteGaloisGroup F) (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F)))
    (p : Fiber (geometricPoint F) Y) : Fiber (geometricPoint F) Y := pointEnd F σ ≫ p

@[simp] theorem act_left (σ : Field.absoluteGaloisGroup F)
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : Fiber (geometricPoint F) Y) :
    (act F σ Y p).left =
      Spec.map (CommRingCat.ofHom (asAutomorphism F σ).toRingHom) ≫ p.left := rfl

@[simp] theorem act_one (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F)))
    (p : Fiber (geometricPoint F) Y) : act F 1 Y p = p := by
  simp [act]

@[simp] theorem act_mul (σ τ : Field.absoluteGaloisGroup F)
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : Fiber (geometricPoint F) Y) :
    act F (σ * τ) Y p = act F σ Y (act F τ Y p) := by
  simp only [act, pointEnd_mul, Category.assoc]

/-- The point action commutes with every morphism of finite étale covers. -/
theorem act_naturality (σ : Field.absoluteGaloisGroup F)
    {Y Z : Scheme.FiniteEtale (Spec (CommRingCat.of F))} (f : Y ⟶ Z)
    (p : Fiber (geometricPoint F) Y) :
    (fiberToFinite (geometricPoint F)).map f (act F σ Y p) =
      act F σ Z ((fiberToFinite (geometricPoint F)).map f p) := by
  change (pointEnd F σ ≫ p) ≫ f.hom = pointEnd F σ ≫ (p ≫ f.hom)
  exact Category.assoc _ _ _

/-- The permutation of each finite fibre induced by a Galois automorphism. -/
def fiberEquiv (σ : Field.absoluteGaloisGroup F)
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) :
    Fiber (geometricPoint F) Y ≃ Fiber (geometricPoint F) Y where
  toFun := act F σ Y
  invFun := act F σ⁻¹ Y
  left_inv p := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv p := by rw [← act_mul, mul_inv_cancel, act_one]

/-- A Galois automorphism determines a natural automorphism of the actual fibre functor. -/
def fiberAut (σ : Field.absoluteGaloisGroup F) : FieldFundamentalGroup F :=
  NatIso.ofComponents (fun Y => FintypeCat.equivEquivIso (fiberEquiv F σ Y)) (by
    intro Y Z f
    apply FintypeCat.hom_ext
    intro p
    exact (act_naturality F σ f p).symm)

@[simp] theorem fiberAut_apply (σ : Field.absoluteGaloisGroup F)
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : Fiber (geometricPoint F) Y) :
    (fiberAut F σ).hom.app Y p = act F σ Y p := rfl

/-- The canonical homomorphism from the absolute Galois group to the actual field fibre group. -/
def toFundamentalGroup : Field.absoluteGaloisGroup F →* FieldFundamentalGroup F where
  toFun := fiberAut F
  map_one' := by
    apply Aut.ext
    apply NatTrans.ext
    funext Y
    apply FintypeCat.hom_ext
    intro p
    exact act_one F Y p
  map_mul' σ τ := by
    apply Aut.ext
    apply NatTrans.ext
    funext Y
    apply FintypeCat.hom_ext
    intro p
    exact act_mul F σ τ Y p

@[simp] theorem toFundamentalGroup_apply (σ : Field.absoluteGaloisGroup F)
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : Fiber (geometricPoint F) Y) :
    (toFundamentalGroup F σ).hom.app Y p = act F σ Y p := rfl

/-- Coordinates of a geometric-point lift, as an actual map on global sections. -/
def coordinates (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F)))
    (p : Fiber (geometricPoint F) Y) :
    Γ(Y.obj.left, ⊤) →+* AlgebraicClosure F :=
  (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure F))).hom).hom

theorem coordinates_injective (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) :
    Function.Injective (coordinates F Y) := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  intro p q h
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure F))).hom).mp
  exact CommRingCat.hom_ext h

/-- On coordinates the action is postcomposition with the field automorphism. -/
theorem coordinates_act (σ : Field.absoluteGaloisGroup F)
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : Fiber (geometricPoint F) Y) :
    coordinates F Y (act F σ Y p) =
      (asAutomorphism F σ).toRingHom.comp (coordinates F Y p) := by
  change ((Spec.map _ ≫ p.left).appTop ≫ _).hom = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

theorem continuous_act (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F)))
    (p : Fiber (geometricPoint F) Y) :
    Continuous (fun σ : Field.absoluteGaloisGroup F =>
      (toFundamentalGroup F σ).hom.app Y p) := by
  let : TopologicalSpace (AlgebraicClosure F) := ⊥
  let : DiscreteTopology (AlgebraicClosure F) := ⟨rfl⟩
  let : ContinuousSMul (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (AlgebraicClosure F) :=
    continuousSMul_iff_stabilizer_isOpen.mpr (fun x => stabilizer_isOpen_of_isIntegral x)
  let c : (fiberToFinite (geometricPoint F)).obj Y →
      (Γ(Y.obj.left, ⊤) → AlgebraicClosure F) := fun p => coordinates F Y p
  have hc : Function.Injective c := by
    intro p q h
    exact coordinates_injective F Y (RingHom.ext (congrFun h))
  have he := (continuous_of_discreteTopology (f := c)).isClosedEmbedding hc
  rw [he.isEmbedding.isInducing.continuous_iff]
  apply continuous_pi
  intro a
  change Continuous (fun σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F =>
    coordinates F Y (act F σ Y p) a)
  simp_rw [coordinates_act]
  exact continuous_id.smul continuous_const

/-- The Galois homomorphism is continuous for the Krull and fibre evaluation topologies. -/
theorem continuous_toFundamentalGroup : Continuous (toFundamentalGroup F) := by
  rw [Topology.IsInducing.continuous_iff
    (PreGaloisCategory.autEmbedding_isClosedEmbedding (fiberToFinite (geometricPoint
      F))).isInducing,
    continuous_pi_iff]
  intro Y
  let c : Aut ((fiberToFinite (geometricPoint F)).obj Y) →
      ((fiberToFinite (geometricPoint F)).obj Y → (fiberToFinite (geometricPoint F)).obj Y) :=
    fun a => a.hom
  have hc : Function.Injective c := by
    intro a b h
    apply Aut.ext
    apply FintypeCat.hom_ext
    exact congrFun h
  have he := (continuous_of_discreteTopology (f := c)).isClosedEmbedding hc
  rw [he.isEmbedding.isInducing.continuous_iff]
  exact continuous_pi (fun p => continuous_act F Y p)

/-- The canonical continuous homomorphism from the absolute Galois group. -/
def continuousToFundamentalGroup : Field.absoluteGaloisGroup F →ₜ* FieldFundamentalGroup F :=
  { toFundamentalGroup F with continuous_toFun := continuous_toFundamentalGroup F }

section FiniteFields

variable [CharZero F]
variable (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L]

/-- Every finite extension of a characteristic-zero field defines a finite étale cover. -/
def finiteFieldCover : Scheme.FiniteEtale (Spec (CommRingCat.of F)) := by
  letI : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  letI : Algebra.FinitePresentation F L := Algebra.FinitePresentation.of_finiteType.mp
    (inferInstance : Algebra.FiniteType F L)
  letI : Algebra.Etale F L := ⟨inferInstance, inferInstance⟩
  refine ⟨Over.mk (fieldPoint F L), ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)

/-- A field embedding gives the corresponding actual point lift. -/
def fieldLift (φ : L →ₐ[F] AlgebraicClosure F) :
    Fiber (geometricPoint F) (finiteFieldCover F L) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x)

/-- Recover the embedding from an actual scheme-point lift by full faithfulness of `Spec`. -/
def liftToEmbedding (p : Fiber (geometricPoint F) (finiteFieldCover F L)) :
    L →ₐ[F] AlgebraicClosure F where
  toRingHom := (Spec.preimage p.left).hom
  commutes' x := by
    have h := Over.w p
    change p.left ≫ Spec.map (CommRingCat.ofHom (algebraMap F L)) =
      Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))) at h
    rw [← Spec.map_preimage p.left, ← Spec.map_comp, Spec.map_inj] at h
    exact congrArg (fun f : CommRingCat.of F ⟶ CommRingCat.of (AlgebraicClosure F) => f.hom x) h

@[simp] theorem liftToEmbedding_fieldLift (φ : L →ₐ[F] AlgebraicClosure F) :
    liftToEmbedding F L (fieldLift F L φ) = φ := by
  apply AlgHom.ext
  intro x
  change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom x = φ x
  rw [Spec.preimage_map]
  rfl

@[simp] theorem fieldLift_liftToEmbedding
    (p : Fiber (geometricPoint F) (finiteFieldCover F L)) :
    fieldLift F L (liftToEmbedding F L p) = p := by
  apply Over.OverMorphism.ext
  exact Spec.map_preimage p.left

/-- The affine field cover fibre is the set of field embeddings, without a classification
assumption. -/
def fieldFiberEquiv : Fiber (geometricPoint F) (finiteFieldCover F L) ≃
    (L →ₐ[F] AlgebraicClosure F) where
  toFun := liftToEmbedding F L
  invFun := fieldLift F L
  left_inv := fieldLift_liftToEmbedding F L
  right_inv := liftToEmbedding_fieldLift F L

@[simp] theorem act_fieldLift (σ : Field.absoluteGaloisGroup F)
    (φ : L →ₐ[F] AlgebraicClosure F) :
    act F σ (finiteFieldCover F L) (fieldLift F L φ) =
      fieldLift F L ((asAutomorphism F σ).toAlgHom.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {L} {M : Type u} [Field M] [Algebra F M] [FiniteDimensional F M]

/-- An algebra homomorphism gives a morphism of the actual finite field covers. -/
def fieldCoverMap (φ : L →ₐ[F] M) : finiteFieldCover F M ⟶ finiteFieldCover F L :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x))

-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem fieldLift_map (φ : L →ₐ[F] M) (ψ : M →ₐ[F] AlgebraicClosure F) :
    (fiberToFinite (geometricPoint F)).map (fieldCoverMap F φ) (fieldLift F M ψ) =
      fieldLift F L (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem liftToEmbedding_map (φ : L →ₐ[F] M)
    (p : Fiber (geometricPoint F) (finiteFieldCover F M)) :
    liftToEmbedding F L ((fiberToFinite (geometricPoint F)).map (fieldCoverMap F φ) p) =
      (liftToEmbedding F M p).comp φ := by
  rw [← fieldLift_liftToEmbedding F M p, fieldLift_map]
  simp only [liftToEmbedding_fieldLift]

/-- A natural fibre automorphism acts on the embeddings of each finite field. -/
def embeddingAction (a : FieldFundamentalGroup F) (φ : L →ₐ[F] AlgebraicClosure F) :
    L →ₐ[F] AlgebraicClosure F :=
  liftToEmbedding F L (a.hom.app (finiteFieldCover F L) (fieldLift F L φ))

theorem embeddingAction_comp (a : FieldFundamentalGroup F) (φ : L →ₐ[F] M)
    (ψ : M →ₐ[F] AlgebraicClosure F) :
    embeddingAction F a (ψ.comp φ) = (embeddingAction F a ψ).comp φ := by
  have h := congrArg (liftToEmbedding F L)
    (evaluate_naturality (geometricPoint F) a (fieldCoverMap F φ) (fieldLift F M ψ))
  simpa only [fieldLift_map, liftToEmbedding_map, embeddingAction] using h.symm

end FiniteFields

section CharacteristicZero

variable [CharZero F]

/-- The image of the inclusion point of a finite subfield. -/
def subfieldEmbedding (a : FieldFundamentalGroup F)
    (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L] :
    L →ₐ[F] AlgebraicClosure F := embeddingAction F a L.val

theorem subfieldEmbedding_compat (a : FieldFundamentalGroup F)
    {L M : IntermediateField F (AlgebraicClosure F)}
    [FiniteDimensional F L] [FiniteDimensional F M] (h : L ≤ M) :
    subfieldEmbedding F a L = (subfieldEmbedding F a M).comp (IntermediateField.inclusion h) :=
  embeddingAction_comp F a (IntermediateField.inclusion h) M.val

/-- Reconstruct the value on an element from its finite simple subfield. -/
def reconstructedValue (a : FieldFundamentalGroup F) (x : AlgebraicClosure F) :
    AlgebraicClosure F :=
  letI : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  subfieldEmbedding F a (IntermediateField.adjoin F {x})
    (IntermediateField.AdjoinSimple.gen F x)

theorem reconstructedValue_eq (a : FieldFundamentalGroup F)
    (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L] (x : L) :
    reconstructedValue F a x = subfieldEmbedding F a L x := by
  let : FiniteDimensional F (IntermediateField.adjoin F {x.val}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x.val)
  have h : IntermediateField.adjoin F {x.val} ≤ L :=
    IntermediateField.adjoin_simple_le_iff.mpr x.property
  exact congrArg (fun φ : IntermediateField.adjoin F {x.val} →ₐ[F] AlgebraicClosure F =>
    φ (IntermediateField.AdjoinSimple.gen F x.val)) (subfieldEmbedding_compat F a h)

/-- The coherent finite-subfield embeddings form an actual algebra endomorphism. -/
def reconstructedEmbedding (a : FieldFundamentalGroup F) :
    AlgebraicClosure F →ₐ[F] AlgebraicClosure F where
  toFun := reconstructedValue F a
  map_one' := by
    let : FiniteDimensional F (IntermediateField.adjoin F {(1 : AlgebraicClosure F)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    change subfieldEmbedding F a (IntermediateField.adjoin F {1}) 1 = 1
    exact map_one _
  map_mul' x y := by
    let L := IntermediateField.adjoin F {x, y}
    let : FiniteDimensional F L := IntermediateField.finiteDimensional_adjoin_pair
      (Algebra.IsIntegral.isIntegral x) (Algebra.IsIntegral.isIntegral y)
    have hx : x ∈ L := IntermediateField.subset_adjoin F {x, y} (by simp)
    have hy : y ∈ L := IntermediateField.subset_adjoin F {x, y} (by simp)
    rw [reconstructedValue_eq F a L ⟨x * y, L.mul_mem hx hy⟩,
      reconstructedValue_eq F a L ⟨x, hx⟩, reconstructedValue_eq F a L ⟨y, hy⟩]
    exact map_mul (subfieldEmbedding F a L) (⟨x, hx⟩ : L) (⟨y, hy⟩ : L)
  map_zero' := by
    let : FiniteDimensional F (IntermediateField.adjoin F {(0 : AlgebraicClosure F)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    change subfieldEmbedding F a (IntermediateField.adjoin F {0}) 0 = 0
    exact map_zero _
  map_add' x y := by
    let L := IntermediateField.adjoin F {x, y}
    let : FiniteDimensional F L := IntermediateField.finiteDimensional_adjoin_pair
      (Algebra.IsIntegral.isIntegral x) (Algebra.IsIntegral.isIntegral y)
    have hx : x ∈ L := IntermediateField.subset_adjoin F {x, y} (by simp)
    have hy : y ∈ L := IntermediateField.subset_adjoin F {x, y} (by simp)
    rw [reconstructedValue_eq F a L ⟨x + y, L.add_mem hx hy⟩,
      reconstructedValue_eq F a L ⟨x, hx⟩, reconstructedValue_eq F a L ⟨y, hy⟩]
    exact map_add (subfieldEmbedding F a L) (⟨x, hx⟩ : L) (⟨y, hy⟩ : L)
  commutes' x := by
    let L := IntermediateField.adjoin F {algebraMap F (AlgebraicClosure F) x}
    let : FiniteDimensional F L :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    change subfieldEmbedding F a L (algebraMap F L x) = _
    exact (subfieldEmbedding F a L).commutes x

/-- Normality of the algebraic closure upgrades the reconstructed embedding to an automorphism. -/
def fromFundamentalGroup (a : FieldFundamentalGroup F) : Field.absoluteGaloisGroup F :=
  AlgEquiv.ofBijective (reconstructedEmbedding F a)
    ((reconstructedEmbedding F a).normal_bijective F (AlgebraicClosure F) (AlgebraicClosure F))

theorem fromFundamentalGroup_subfield (a : FieldFundamentalGroup F)
    (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L] (x : L) :
    asAutomorphism F (fromFundamentalGroup F a) x = subfieldEmbedding F a L x :=
  reconstructedValue_eq F a L x

omit [CharZero F] in
/-- A geometric point of an affine finite cover is recovered from its coordinates. -/
theorem point_from_coordinates (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F)))
    (p : Fiber (geometricPoint F) Y) :
    letI : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
    Spec.map (CommRingCat.ofHom (coordinates F Y p)) ≫ Y.obj.left.isoSpec.inv = p.left := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  apply (cancel_mono Y.obj.left.isoSpec.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map (p.left.appTop ≫ _) = p.left ≫ Y.obj.left.isoSpec.hom
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_hom, Scheme.isoSpec_hom_naturality]

/-- Every point lift factors through the inclusion point of a finite subfield.
The proof takes the image of the finite global-section algebra in the algebraic closure. -/
theorem point_factors_finiteSubfield (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F)))
    (p : Fiber (geometricPoint F) Y) :
    ∃ (L : IntermediateField F (AlgebraicClosure F)) (hL : FiniteDimensional F L),
      letI := hL
      ∃ f : finiteFieldCover F L ⟶ Y,
        (fiberToFinite (geometricPoint F)).map f (fieldLift F L L.val) = p := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  let A := Γ(Y.obj.left, ⊤)
  let a : F →+* A :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ Y.obj.hom.appTop).hom
  let : Algebra F A := a.toAlgebra
  have ha : a.Finite :=
    Y.obj.hom.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2)
  let : Module.Finite F A := ha
  let φ : A →ₐ[F] AlgebraicClosure F :=
    { toRingHom := coordinates F Y p
      commutes' := fun x => by
        have he : ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ Y.obj.hom.appTop) ≫
            (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure F))).hom) =
              CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)) := by
          rw [Category.assoc, ← Category.assoc Y.obj.hom.appTop p.left.appTop,
            ← Scheme.Hom.comp_appTop, Over.w p]
          change (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
            ((Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))).appTop ≫ _) = _
          rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
        exact congrArg (fun h : CommRingCat.of F ⟶ CommRingCat.of (AlgebraicClosure F) =>
          h.hom x) he }
  let S := φ.range
  let : FiniteDimensional F S :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  let L := S.toIntermediateField' (@Field.toIsField S (fieldOfFiniteDimensional F S))
  have hL : FiniteDimensional F L := inferInstanceAs (FiniteDimensional F S)
  let : FiniteDimensional F L := hL
  let ψ : A →ₐ[F] L := φ.rangeRestrict
  have hstruct : Y.obj.left.isoSpec.inv ≫ Y.obj.hom =
      Spec.map (CommRingCat.ofHom a) := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  let f : finiteFieldCover F L ⟶ Y := ObjectProperty.homMk
    (Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.obj.left.isoSpec.inv) (by
      change (Spec.map _ ≫ Y.obj.left.isoSpec.inv) ≫ Y.obj.hom = Spec.map _
      rw [Category.assoc, hstruct, ← Spec.map_comp]
      congr 1
      ext x
      exact congrArg (fun z : L => (z : AlgebraicClosure F)) (ψ.commutes x)))
  refine ⟨L, hL, f, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ (Spec.map _ ≫ Y.obj.left.isoSpec.inv) = p.left
  rw [← Category.assoc, ← Spec.map_comp]
  exact point_from_coordinates F Y p

/-- The reconstructed Galois element has the prescribed action on every finite cover. -/
theorem toFundamentalGroup_fromFundamentalGroup (a : FieldFundamentalGroup F) :
    toFundamentalGroup F (fromFundamentalGroup F a) = a := by
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro p
  obtain ⟨L, hL, f, hp⟩ := point_factors_finiteSubfield F Y p
  let : FiniteDimensional F L := hL
  have hLact : (toFundamentalGroup F (fromFundamentalGroup F a)).hom.app
      (finiteFieldCover F L) (fieldLift F L L.val) =
        a.hom.app (finiteFieldCover F L) (fieldLift F L L.val) := by
    apply (fieldFiberEquiv F L).injective
    change liftToEmbedding F L (act F _ _ _) = subfieldEmbedding F a L
    rw [act_fieldLift, liftToEmbedding_fieldLift]
    apply AlgHom.ext
    exact fromFundamentalGroup_subfield F a L
  rw [← hp, ← evaluate_naturality (geometricPoint F), hLact,
    evaluate_naturality (geometricPoint F)]

/-- Finite subfields detect every element of the actual absolute Galois group. -/
theorem toFundamentalGroup_injective : Function.Injective (toFundamentalGroup F) := by
  intro σ τ h
  change asAutomorphism F σ = asAutomorphism F τ
  apply AlgEquiv.ext
  intro x
  let L := IntermediateField.adjoin F {x}
  let : FiniteDimensional F L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hx : x ∈ L := IntermediateField.subset_adjoin F {x} rfl
  have hp := congrArg (fun a : FieldFundamentalGroup F =>
    a.hom.app (finiteFieldCover F L) (fieldLift F L L.val)) h
  simp only [toFundamentalGroup_apply, act_fieldLift] at hp
  have he := congrArg (liftToEmbedding F L) hp
  simp only [liftToEmbedding_fieldLift] at he
  exact congrArg (fun φ : L →ₐ[F] AlgebraicClosure F => φ ⟨x, hx⟩) he

@[simp] theorem fromFundamentalGroup_toFundamentalGroup (σ : Field.absoluteGaloisGroup F) :
    fromFundamentalGroup F (toFundamentalGroup F σ) = σ :=
  toFundamentalGroup_injective F (toFundamentalGroup_fromFundamentalGroup F _)

/-- The canonical group isomorphism, obtained from actual finite-subfield reconstruction. -/
def fundamentalGroupEquiv : Field.absoluteGaloisGroup F ≃* FieldFundamentalGroup F where
  toFun := toFundamentalGroup F
  invFun := fromFundamentalGroup F
  left_inv := fromFundamentalGroup_toFundamentalGroup F
  right_inv := toFundamentalGroup_fromFundamentalGroup F
  map_mul' := map_mul (toFundamentalGroup F)

theorem toFundamentalGroup_bijective : Function.Bijective (toFundamentalGroup F) :=
  (fundamentalGroupEquiv F).bijective

/-- Finite-subfield point stabilizers prove continuity of the reconstructed inverse. -/
theorem continuous_fromFundamentalGroup : Continuous (fromFundamentalGroup F) := by
  let f : FieldFundamentalGroup F →* Field.absoluteGaloisGroup F :=
    (fundamentalGroupEquiv F).symm.toMonoidHom
  change Continuous f
  apply continuous_of_continuousAt_one f
  apply continuousAt_def.mpr
  intro N hN
  rw [map_one] at hN
  change N ∈ 𝓝 (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) at hN
  obtain ⟨L, hL, hLN⟩ := (krullTopology_mem_nhds_one_iff F (AlgebraicClosure F) N).mp hN
  let : FiniteDimensional F L := hL
  let p : (fiberToFinite (geometricPoint F)).obj (finiteFieldCover F L) := fieldLift F L L.val
  let ev : FieldFundamentalGroup F → (fiberToFinite (geometricPoint F)).obj
      (finiteFieldCover F L) := fun a => a.hom.app (finiteFieldCover F L) p
  have hcoord : Continuous (fun a : FieldFundamentalGroup F =>
      PreGaloisCategory.autEmbedding (fiberToFinite (geometricPoint F)) a
        (finiteFieldCover F L)) :=
    (continuous_apply (finiteFieldCover F L)).comp continuous_induced_dom
  have hev : Continuous ev :=
    (continuous_of_discreteTopology (f := fun b : Aut
      ((fiberToFinite (geometricPoint F)).obj (finiteFieldCover F L)) => b.hom p)).comp hcoord
  have hV : {a : FieldFundamentalGroup F | ev a = p} ∈ 𝓝 1 :=
    ((isOpen_discrete {p}).preimage hev).mem_nhds (by rfl)
  filter_upwards [hV] with a ha
  apply hLN
  change asAutomorphism F (f a) ∈ L.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change asAutomorphism F (fromFundamentalGroup F a) x = x
  rw [fromFundamentalGroup_subfield F a L ⟨x, hx⟩]
  have he := congrArg (liftToEmbedding F L) ha
  change subfieldEmbedding F a L = liftToEmbedding F L (fieldLift F L L.val) at he
  rw [liftToEmbedding_fieldLift] at he
  exact congrArg (fun φ : L →ₐ[F] AlgebraicClosure F => φ ⟨x, hx⟩) he

/-- Stacks `0BNE`, Lemma 58.6.3(2), in characteristic zero: the canonical topological
group isomorphism between the absolute Galois group and the actual finite étale fibre group. -/
def fundamentalGroupContinuousEquiv :
    Field.absoluteGaloisGroup F ≃ₜ* FieldFundamentalGroup F :=
  { fundamentalGroupEquiv F with
    continuous_toFun := continuous_toFundamentalGroup F
    continuous_invFun := continuous_fromFundamentalGroup F }

@[simp] theorem fundamentalGroupContinuousEquiv_apply (σ : Field.absoluteGaloisGroup F)
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : Fiber (geometricPoint F) Y) :
    (fundamentalGroupContinuousEquiv F σ).hom.app Y p = act F σ Y p := rfl

end CharacteristicZero

end AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 129483d91d1b6b95156735a14eefebe912715cafc2e186ce4b55d66272d3d8e6.
Definitions, hypotheses and universes are retained modulo native names. -/
