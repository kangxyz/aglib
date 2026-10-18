/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.SchemeTorsorClassification
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorSum

/-!
# Contracted-sum additivity of the actual torsor/fundamental-group comparison

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Addition of affine coordinates
is descended to an actual scheme map. Its section map is equivariant for
coefficient addition, so the canonical extension class proves additivity
for the already constructed geometric contracted sum. No additive group
structure or cohomology operation is transported through an arbitrary bijection.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open AlgebraicGeometry.Scheme.FiniteEtale.TorsorDescent
namespace AlgebraicGeometry.Scheme.EtaleH1.TorsorComparisonAdditivity
open ContinuousTorsors SchemeTorsorClassification
open GroupCohomology.ContinuousH1
open GroupCohomology.ContinuousH1.AffineTorsors
universe u w
attribute [local instance] Over.cartesianMonoidalCategory coverCartesian
  AddCommGrpCat.cartesianMonoidalCategory hasSheafifyLarge
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

section BinaryDescent
variable (A : Grp (Over X)) [IsFinite A.X.hom] [Etale A.X.hom]
variable {Y Z W : Scheme.FiniteEtale X}
variable (τ : TorsorAction A (toUnit Y.obj)) (σ : TorsorAction A (toUnit Z.obj))
variable (ν : TorsorAction A (toUnit W.obj))
variable (f : Fiber s Y → Fiber s Z → Fiber s W)
variable (hf : ∀ (γ : FiberAutGroup s) (x : Fiber s Y) (y : Fiber s Z),
  f (γ.hom.app Y x) (γ.hom.app Z y) = γ.hom.app W (f x y))
variable (ha : ∀ (a b : Over.mk s ⟶ A.X) (x : Fiber s Y) (y : Fiber s Z),
  f (τ.act a x) (σ.act b y) = ν.act (a * b) (f x y))

include ha in
/-- Translation compatibility of a binary fibre map descends to every
scheme-valued test, using faithfulness on the genuine finite product. -/
theorem descendFiberBimap_equivariant {T : Over X}
    (a b : T ⟶ A.X) (x : T ⟶ Y.obj) (y : T ⟶ Z.obj) :
    lift (τ.act a x) (σ.act b y) ≫ descendFiberBimap s f hf =
      ν.act (a * b) (lift x y ≫ descendFiberBimap s f hf) := by
  let D : Scheme.FiniteEtale X := (coefficientCover A ⊗ coefficientCover A) ⊗ (Y ⊗ Z)
  let a₀ : D.obj ⟶ A.X := fst _ _ ≫ fst _ _
  let b₀ : D.obj ⟶ A.X := fst _ _ ≫ snd _ _
  let x₀ : D.obj ⟶ Y.obj := snd _ _ ≫ fst _ _
  let y₀ : D.obj ⟶ Z.obj := snd _ _ ≫ snd _ _
  have h : lift (τ.act a₀ x₀) (σ.act b₀ y₀) ≫ descendFiberBimap s f hf =
      ν.act (a₀ * b₀) (lift x₀ y₀ ≫ descendFiberBimap s f hf) := by
    apply finiteEtale_hom_ext s
    intro p
    simp only [comp_lift_assoc, τ.naturality, σ.naturality,
      descendFiberBimap_fiber, ν.naturality, MonObj.comp_mul]
    exact ha _ _ _ _
  let k : T ⟶ D.obj := lift (lift a b) (lift x y)
  have hka : k ≫ a₀ = a := by
    change lift (lift a b) (lift x y) ≫ (fst (A.X ⊗ A.X) (Y.obj ⊗ Z.obj) ≫ fst A.X A.X) = a
    simp only [lift_fst_assoc, lift_fst]
  have hkb : k ≫ b₀ = b := by
    change lift (lift a b) (lift x y) ≫ (fst (A.X ⊗ A.X) (Y.obj ⊗ Z.obj) ≫ snd A.X A.X) = b
    simp only [lift_fst_assoc, lift_snd]
  have hkx : k ≫ x₀ = x := by
    change lift (lift a b) (lift x y) ≫ (snd (A.X ⊗ A.X) (Y.obj ⊗ Z.obj) ≫ fst Y.obj Z.obj) = x
    simp only [lift_snd_assoc, lift_fst]
  have hky : k ≫ y₀ = y := by
    change lift (lift a b) (lift x y) ≫ (snd (A.X ⊗ A.X) (Y.obj ⊗ Z.obj) ≫ snd Y.obj Z.obj) = y
    simp only [lift_snd_assoc, lift_snd]
  have hh := congrArg (fun m => k ≫ m) h
  simpa only [comp_lift_assoc, τ.naturality, σ.naturality, ν.naturality,
    MonObj.comp_mul, hka, hkb, hkx, hky] using hh

end BinaryDescent

section AffineAddition
variable (M : Type u) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (c d : Cocycle (FiberAutGroup s) M)

/-- Addition of affine coordinates gives a literal map of actual geometric fibres. -/
def affineSumFiber (x : Fiber s (cocycleCover s c)) (y : Fiber s (cocycleCover s d)) :
    Fiber s (cocycleCover s (c + d)) :=
  (cocycleFiberEquiv s (c + d)).symm
    ⟨(cocycleFiberEquiv s c x).val + (cocycleFiberEquiv s d y).val⟩

/-- The cocycle addition law is precisely monodromy equivariance of this map. -/
theorem affineSumFiber_monodromy (γ : FiberAutGroup s)
    (x : Fiber s (cocycleCover s c)) (y : Fiber s (cocycleCover s d)) :
    affineSumFiber s M c d (γ.hom.app _ x) (γ.hom.app _ y) =
      γ.hom.app _ (affineSumFiber s M c d x y) := by
  apply (cocycleFiberEquiv s (c + d)).injective
  apply AffinePoint.ext (c + d)
  change (torsorFiberEquiv s (AffinePoint (c + d))
    ((torsorFiberEquiv s (AffinePoint (c + d))).symm _)).val =
      (torsorFiberEquiv s (AffinePoint (c + d)) (γ.hom.app _ _)).val
  rw [Equiv.apply_symm_apply, torsorFiber_action]
  change (torsorFiberEquiv s (AffinePoint c) (γ.hom.app _ x)).val +
      (torsorFiberEquiv s (AffinePoint d) (γ.hom.app _ y)).val = _
  rw [torsorFiber_action, torsorFiber_action]
  change (γ • (cocycleFiberEquiv s c x)).val + (γ • (cocycleFiberEquiv s d y)).val =
    (γ • ((cocycleFiberEquiv s (c + d)) ((cocycleFiberEquiv s (c + d)).symm
      ⟨(cocycleFiberEquiv s c x).val + (cocycleFiberEquiv s d y).val⟩))).val
  rw [Equiv.apply_symm_apply]
  simp only [AffinePoint.smul_val, Cocycle.add_apply, smul_add]
  exact add_add_add_comm _ _ _ _

/-- The actual finite scheme map descended from affine addition. -/
def affineSumSchemeMap : (cocycleCover s c).obj ⊗ (cocycleCover s d).obj ⟶
    (cocycleCover s (c + d)).obj :=
  descendFiberBimap s (affineSumFiber s M c d) (affineSumFiber_monodromy s M c d)

/-- On actual fibres affine addition adds the two translation coefficients. -/
theorem affineSumFiber_translation (a b : Over.mk s ⟶ (moduleScheme s M).X)
    (x : Fiber s (cocycleCover s c)) (y : Fiber s (cocycleCover s d)) :
    affineSumFiber s M c d ((cocycleSchemeAction s c).act a x) ((cocycleSchemeAction s d).act b y) =
      (cocycleSchemeAction s (c + d)).act (a * b) (affineSumFiber s M c d x y) := by
  apply (cocycleFiberEquiv s (c + d)).injective
  apply AffinePoint.ext (c + d)
  change (cocycleFiberEquiv s (c + d) ((cocycleFiberEquiv s (c + d)).symm _)).val = _
  rw [Equiv.apply_symm_apply, cocycleSchemeAction_fiber s (c + d)]
  change (cocycleFiberEquiv s c ((cocycleSchemeAction s c).act a x)).val +
    (cocycleFiberEquiv s d ((cocycleSchemeAction s d).act b y)).val = _
  rw [cocycleSchemeAction_fiber, cocycleSchemeAction_fiber, map_mul]
  change (moduleFiberMulEquiv s M a).toAdd + (cocycleFiberEquiv s c x).val +
    ((moduleFiberMulEquiv s M b).toAdd + (cocycleFiberEquiv s d y).val) =
    ((moduleFiberMulEquiv s M a).toAdd + (moduleFiberMulEquiv s M b).toAdd) +
      (cocycleFiberEquiv s (c + d) ((cocycleFiberEquiv s (c + d)).symm _)).val
  rw [Equiv.apply_symm_apply]
  exact add_add_add_comm _ _ _ _

/-- The actual scheme map is equivariant on all tests for coefficient addition. -/
theorem affineSumSchemeMap_equivariant {T : Over X}
    (a b : T ⟶ (moduleScheme s M).X)
    (x : T ⟶ (cocycleCover s c).obj) (y : T ⟶ (cocycleCover s d).obj) :
    lift ((cocycleSchemeAction s c).act a x) ((cocycleSchemeAction s d).act b y) ≫
        affineSumSchemeMap s M c d =
      (cocycleSchemeAction s (c + d)).act (a * b) (lift x y ≫ affineSumSchemeMap s M c d) :=
  descendFiberBimap_equivariant s (moduleScheme s M) _ _ _
    (affineSumFiber s M c d) (affineSumFiber_monodromy s M c d)
    (affineSumFiber_translation s M c d) a b x y

variable [PreconnectedSpace X]

/-- The actual affine-addition scheme map gives a natural map of torsor sheaves. -/
def affineSumSheafMap :
    (cocycleSheafTorsor s M c).carrier ⊗ (cocycleSheafTorsor s M d).carrier ⟶
      (cocycleSheafTorsor s M (c + d)).carrier :=
  ⟨{ app U := TypeCat.ofHom (fun t => ULift.up (lift t.1.down t.2.down ≫ affineSumSchemeMap s M c
    d))
     naturality {U V} g := by
       ext t
       apply ULift.ext
       exact (comp_lift_assoc ((Scheme.Etale.forget X).map g.unop) t.1.down t.2.down
         (affineSumSchemeMap s M c d)).symm }⟩

/-- The actual sheaf pairing is equivariant for the addition coefficient map. -/
def affineSumTorsorHom :
    Torsor.Hom (torsorCoefficientAdd (moduleSheaf s M))
      (torsorProduct (cocycleSheafTorsor s M c) (cocycleSheafTorsor s M d))
      (cocycleSheafTorsor s M (c + d)) where
  map := affineSumSheafMap s M c d
  equivariant _U a t := congrArg ULift.up
    (affineSumSchemeMap_equivariant s M c d a.1.down.toMul a.2.down.toMul t.1.down t.2.down)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The explicit affine-addition map identifies the canonical extension class
of c+d with the sum of the two actual sheaf-torsor extension classes. -/
theorem torsorExtClass_cocycle_add :
    torsorExtClass (cocycleSheafTorsor s M (c + d)) =
      torsorExtClass (cocycleSheafTorsor s M c) + torsorExtClass (cocycleSheafTorsor s M d) := by
  have h := torsorExtClass_naturality (affineSumTorsorHom s M c d)
  calc
    _ = coefficientMap (torsorCoefficientAdd (moduleSheaf s M))
        (torsorExtClass (torsorProduct (cocycleSheafTorsor s M c) (cocycleSheafTorsor s M d))) :=
          h.symm
    _ = torsorExtClass (torsorSum (cocycleSheafTorsor s M c) (cocycleSheafTorsor s M d)) :=
      (torsorExtClass_pushout _ _).symm
    _ = _ := torsorExtClass_sum _ _

/-- On actual isomorphism classes, the affine construction carries cocycle
addition to the previously constructed geometric contracted sum. -/
theorem torsorClass_cocycle_add (hA : Stacks03AJ.{u, w} X) :
    Quotient.mk (Torsor.isomorphicSetoid (moduleSheaf s M)) (cocycleSheafTorsor s M (c + d)) =
      torsorClassSum hA (Quotient.mk _ (cocycleSheafTorsor s M c))
        (Quotient.mk _ (cocycleSheafTorsor s M d)) := by
  apply (hA.bijective (moduleSheaf s M)).injective
  rw [torsorClassToH1_sum]
  exact torsorExtClass_cocycle_add s M c d

end AffineAddition

section AdditiveComparison
variable (M : Type u) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)

/-- The canonical actual torsor-class/common-H¹ bijection is additive for the
geometric contracted-sum operation, as proved by literal affine addition. -/
def moduleTorsorClassAddEquiv :
    letI := torsorClassAddCommGroup hA (moduleSheaf s M)
    TorsorClass (moduleSheaf s M) ≃+ H1 (FiberAutGroup s) M := by
  letI := torsorClassAddCommGroup hA (moduleSheaf s M)
  refine { moduleTorsorClassEquiv s M hR with map_add' := ?_ }
  intro a b
  obtain ⟨c, hc⟩ := classOf_surjective (FiberAutGroup s) M (moduleTorsorClassEquiv s M hR a)
  obtain ⟨d, hd⟩ := classOf_surjective (FiberAutGroup s) M (moduleTorsorClassEquiv s M hR b)
  have ha : a = Quotient.mk _ (cocycleSheafTorsor s M c) := by
    apply (moduleTorsorClassEquiv s M hR).injective
    exact hc.symm.trans (moduleTorsorClassEquiv_cocycle s M hR c).symm
  have hb : b = Quotient.mk _ (cocycleSheafTorsor s M d) := by
    apply (moduleTorsorClassEquiv s M hR).injective
    exact hd.symm.trans (moduleTorsorClassEquiv_cocycle s M hR d).symm
  rw [ha, hb]
  change moduleTorsorClassEquiv s M hR (torsorClassSum hA _ _) =
    moduleTorsorClassEquiv s M hR (Quotient.mk _ (cocycleSheafTorsor s M c)) +
      moduleTorsorClassEquiv s M hR (Quotient.mk _ (cocycleSheafTorsor s M d))
  rw [← torsorClass_cocycle_add s M c d hA, moduleTorsorClassEquiv_cocycle,
    moduleTorsorClassEquiv_cocycle, moduleTorsorClassEquiv_cocycle, map_add]

/-- The actual finite-coefficient Ext-H¹/common-continuous-H¹ additive
comparison for a descended finite module sheaf. The displayed coefficient
scope retains positivity, annihilation and level invertibility on X. -/
def moduleH1AddEquiv (_hcoeff : FiniteCoefficient (moduleSheaf s M)) :
    H1Etale X (moduleSheaf s M) ≃+ H1 (FiberAutGroup s) M := by
  letI := torsorClassAddCommGroup hA (moduleSheaf s M)
  exact (torsorClassAddEquiv hA (moduleSheaf s M)).symm.trans (moduleTorsorClassAddEquiv s M hA hR)

/-- The additive comparison is the actual torsor-representative construction,
not an unspecified automorphism of either cohomology group. -/
theorem moduleH1AddEquiv_torsor (hcoeff : FiniteCoefficient (moduleSheaf s M))
    (P : Torsor (moduleSheaf s M)) :
    moduleH1AddEquiv s M hA hR hcoeff (torsorExtClass P) =
      representedTorsorClass s (moduleScheme s M) (moduleFiberMulEquiv s M)
        (moduleFiber_action s M) hR (moduleSheaf_isFiniteLocallyConstant (s := s) M) P := by
  let := torsorClassAddCommGroup hA (moduleSheaf s M)
  change moduleTorsorClassEquiv s M hR
    ((torsorClassAddEquiv hA (moduleSheaf s M)).symm (torsorExtClass P)) = _
  rw [show (torsorExtClass P) = (torsorClassAddEquiv hA (moduleSheaf s M)) (Quotient.mk _ P) from
    rfl,
    AddEquiv.symm_apply_apply, moduleTorsorClassEquiv_mk]

/-- Every original common cocycle has the explicitly descended affine torsor
as its inverse image under the actual Ext comparison. -/
theorem moduleH1AddEquiv_symm_classOf (hcoeff : FiniteCoefficient (moduleSheaf s M))
    (c : Cocycle (FiberAutGroup s) M) :
    (moduleH1AddEquiv s M hA hR hcoeff).symm (classOf (FiberAutGroup s) M c) =
      torsorExtClass (cocycleSheafTorsor s M c) := by
  apply (moduleH1AddEquiv s M hA hR hcoeff).injective
  rw [AddEquiv.apply_symm_apply, moduleH1AddEquiv_torsor, representedTorsorClass_cocycle]

end AdditiveComparison

end AlgebraicGeometry.Scheme.EtaleH1.TorsorComparisonAdditivity

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 641408b90e9a1feb85d09180d01655ff6e0a8cb3837abaa6bf7073e90f79ebad.
Definitions, hypotheses and universes are retained modulo native names. -/
