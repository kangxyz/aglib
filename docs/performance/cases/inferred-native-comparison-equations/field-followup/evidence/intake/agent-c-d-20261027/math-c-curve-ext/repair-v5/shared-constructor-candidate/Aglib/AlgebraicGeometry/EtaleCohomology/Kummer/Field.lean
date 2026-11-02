/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootStalk
public import Aglib.GroupCohomology.Kummer.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FundamentalGroupComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootCover

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.Kummer.Field` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5436c5257f51bdb4d7f075e23a2a4c431ec1a2cad7673c39be471e5f461f5a3f`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
/- Current interface migration: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Original mathematical and construction provenance is retained below.
Previous validation is historical; new-interface validation is pending. -/
/-!
# The actual etale root torsor and the existing field Kummer class

C4/C5 field support, `K2-018#lem:k2018-geometric-exact-order` and
`K2-018#prop:k2018-arithmetic-characters`. Mathematical basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For a characteristic-zero field and positive level, the actual represented
mu_n coefficient has its genuine finite locally constant structure. Its
point marking is literal root evaluation through Gamma(Spec). The action is
transported through the existing proved field fundamental-group equivalence,
and the marking's evaluation formula is proved on actual scheme points.
A's actual Ext-H1 comparison and restriction along that equivalence give an
additive equivalence with the existing common continuous H1 of Mu. The inverse
is proved on the same public cocycle quotient, with no new H1 model.

The only retained comparison inputs are A's precise 03AJ/03RV families and
its actual Galois-category/fibre-functor classes, plus the displayed Ext-size
instance. The actual Kummer power-surjectivity family is supplied by the
constructive generic RootCover theorem, rather than retained here.

The positive root torsor is identified with the genuine polynomial cover.
An actual geometric fibre point evaluates to a root a with a^n=f. Its scheme
transport is q/p, and actual Galois point precomposition evaluates to sigma(a).
Consequently its comparison cocycle is literally the existing sigma(a)/a
Kummer cocycle, proving comparison_rootClass, not assuming it.

The higher weight-two map composes this actual H1 comparison with the existing
RootCup coefficient map. The existing primitive-root tensor equivalence gives
its additive equivalence, and the root torsor computes RootCup.cupKummer.
Neither a Milnor-symbol definition nor a Bockstein normalization assertion is
used to define any comparison. Curve-pair descent, geometric restriction and
the final Bockstein square remain separate applications.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Group
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open _root_.GroupCohomology.ContinuousH1
namespace GroupCohomology.Kummer.Field
universe u w
variable (K : Type u) [Field K] [CharZero K] (n : ℕ) [NeZero n]
/-- A field unit as the actual global unit on its spectrum. -/
def globalUnit (f : Kˣ) : Γ(Spec (.of K), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of K)).inv.hom.toMonoidHom f

omit [CharZero K] in
/-- Evaluation of its pullback at the actual algebraic-closure point is the
existing field-unit embedding, with no chosen scalar map. -/
theorem globalUnit_geometric (f : Kˣ) :
    Units.map (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom.toMonoidHom
      (Units.map (geometricPoint K).appTop.hom.toMonoidHom (globalUnit K f)) =
      GroupCohomology.Kummer.baseUnits K f := by
  apply Units.ext
  change (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom
    ((geometricPoint K).appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom (f : K))) =
    algebraMap K (AlgebraicClosure K) (f : K)
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
    ((Scheme.ΓSpecIso (.of K)).inv.hom (f : K))
  change _ = (algebraMap K (AlgebraicClosure K))
    ((Scheme.ΓSpecIso (.of K)).hom.hom ((Scheme.ΓSpecIso (.of K)).inv.hom (f : K))) at h
  exact h.trans (congrArg (algebraMap K (AlgebraicClosure K))
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of K)).inv_hom_id (f : K)))

/-- The commutative group structure on the scheme of `n`th roots of unity over `Spec K`. -/
local instance : CommGrpObj (MultiplicativeGroup.rootsScheme (Spec (.of K)) n) :=
  MultiplicativeGroup.rootsCommGroup (Spec (.of K)) n
local instance : IsFinite (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n).X.hom :=
  RootsFiniteEtale.rootsScheme_finite _ n (NeZero.pos n)
local instance : Etale (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n).X.hom :=
  RootsFiniteEtale.rootsScheme_etale _ n (NeZero.pos n)
      (GroupCohomology.Kummer.RootStalk.levelInvertible K n)


/-- The continuous map from the absolute Galois group to the field fundamental group. -/
def fieldGroupHom : ContinuousMonoidHom (Field.absoluteGaloisGroup K) (FieldFundamentalGroup K) :=
  { (fundamentalGroupContinuousEquiv K).toMulEquiv.toMonoidHom with
    continuous_toFun := (fundamentalGroupContinuousEquiv K).continuous }
/-- The continuous inverse map from the field fundamental group to the absolute Galois group. -/
def absoluteGroupHom : ContinuousMonoidHom (FieldFundamentalGroup K) (Field.absoluteGaloisGroup
    K) :=
  { (fundamentalGroupContinuousEquiv K).symm.toMulEquiv.toMonoidHom with
    continuous_toFun := (fundamentalGroupContinuousEquiv K).symm.continuous }

/-- The fundamental-group action on roots of unity transported from the absolute Galois action. -/
@[instance_reducible] def fundamentalRootAction :
    DistribMulAction (FieldFundamentalGroup K) (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) :=
  restrictedAction (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (absoluteGroupHom K)

/-- The transported fundamental-group action on the root coefficient group. -/
local instance : DistribMulAction (FieldFundamentalGroup K)
    (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) :=
    fundamentalRootAction K n
local instance : ContinuousSMul (FieldFundamentalGroup K)
    (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) :=
  restrictedAction_continuous (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (absoluteGroupHom K)

/-- The multiplicative marking of geometric root-scheme points by roots in the algebraic closure. -/
def pointMark : (Over.mk (geometricPoint K) ⟶ MultiplicativeGroup.rootsScheme (Spec (.of K)) n) ≃*
    Multiplicative (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) where
  toFun p := Multiplicative.ofAdd
      (GroupCohomology.Kummer.RootStalk.sectionRootsEquiv K n (ULift.up
      (Additive.ofMul p)))
  invFun a := ((GroupCohomology.Kummer.RootStalk.sectionRootsEquiv K n).symm
      a.toAdd).down.toMul
  left_inv _p := congrArg (fun z => z.down.toMul)
      ((GroupCohomology.Kummer.RootStalk.sectionRootsEquiv K n).symm_apply_apply _)
  right_inv a := congrArg Multiplicative.ofAdd
      ((GroupCohomology.Kummer.RootStalk.sectionRootsEquiv K
      n).apply_symm_apply a.toAdd)
  map_mul' a b := congrArg Multiplicative.ofAdd
      ((GroupCohomology.Kummer.RootStalk.sectionRootsEquiv K n).map_add
    (ULift.up (Additive.ofMul a)) (ULift.up (Additive.ofMul b)))

theorem pointMark_equivariant (γ : FieldFundamentalGroup K)
    (p : Over.mk (geometricPoint K) ⟶ MultiplicativeGroup.rootsScheme (Spec (.of K)) n) :
    pointMark K n (γ.hom.app (GroupCohomology.Kummer.RootStalk.rootsCover K n) p) =
      Multiplicative.ofAdd (γ • (pointMark K n p).toAdd) := by
  let σ := (fundamentalGroupContinuousEquiv K).symm γ
  have he : γ.hom.app (GroupCohomology.Kummer.RootStalk.rootsCover K n) p =
      pointEnd K σ ≫ p := by
    have h := fundamentalGroupContinuousEquiv_apply K σ
        (GroupCohomology.Kummer.RootStalk.rootsCover K n) p
    simpa only [σ, ContinuousMulEquiv.apply_symm_apply, act] using h
  change Multiplicative.ofAdd
      (GroupCohomology.Kummer.RootStalk.sectionRootsEquiv K n
    (ULift.up (Additive.ofMul (γ.hom.app
        (GroupCohomology.Kummer.RootStalk.rootsCover K n) p)))) =
    Multiplicative.ofAdd (σ •
        GroupCohomology.Kummer.RootStalk.sectionRootsEquiv K n (ULift.up
        (Additive.ofMul p)))
  exact congrArg Multiplicative.ofAdd ((congrArg (fun q =>
      GroupCohomology.Kummer.RootStalk.sectionRootsEquiv K n
    (ULift.up (Additive.ofMul q))) he).trans
        (GroupCohomology.Kummer.RootStalk.sectionRootsEquiv_galois K n σ p))

/-- The finite etale cover adjoining an `n`th root of the field unit `f`. -/
abbrev rootCover (f : Kˣ) : Scheme.FiniteEtale (Spec (.of K)) :=
  AlgebraicGeometry.Scheme.Group.RootCover.cover (Spec (.of K)) n (NeZero.pos n)
    (GroupCohomology.Kummer.RootStalk.levelInvertible K n) (globalUnit K f)

local instance (f : Kˣ) : Surjective (rootCover K n f).obj.hom :=
  AlgebraicGeometry.Scheme.Group.RootCover.cover_surjective _ _ _ _ _

/-- The roots-of-unity torsor action on the cover adjoining an `n`th root of `f`. -/
def rootAction (f : Kˣ) :=
  AlgebraicGeometry.Scheme.Group.RootCover.coverTorsorAction (Spec (.of K)) n
    (NeZero.pos n) (GroupCohomology.Kummer.RootStalk.levelInvertible K n)
        (globalUnit K f)

/-- The root in the algebraic closure obtained by evaluating a geometric point of the root cover. -/
def rootValue (f : Kˣ) (t : Fiber (geometricPoint K) (rootCover K n f)) : (AlgebraicClosure K)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom.toMonoidHom
    (AlgebraicGeometry.Scheme.Group.RootCover.sectionsEquiv (Spec (.of K)) n
      (globalUnit K f) (Over.mk (geometricPoint K)) t).val

theorem rootValue_pow (f : Kˣ) (t : Fiber (geometricPoint K) (rootCover K n f)) :
    rootValue K n f t ^ n = GroupCohomology.Kummer.baseUnits K f := by
  rw [rootValue, ← map_pow]
  exact (congrArg (Units.map (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom.toMonoidHom)
    (AlgebraicGeometry.Scheme.Group.RootCover.sectionsEquiv (Spec (.of K)) n
      (globalUnit K f) (Over.mk (geometricPoint K)) t).property).trans (globalUnit_geometric K f)

omit [CharZero K] in
theorem units_galois (σ : Field.absoluteGaloisGroup K) (b : Γ(Spec (.of (AlgebraicClosure K)),
    ⊤)ˣ) :
    Units.map (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom.toMonoidHom
      (Units.map (pointEnd K σ).left.appTop.hom.toMonoidHom b) =
    GroupCohomology.Kummer.unitAction K σ (Units.map (Scheme.ΓSpecIso (.of (AlgebraicClosure
        K))).hom.hom.toMonoidHom b) := by
  apply Units.ext
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (asAutomorphism K σ).toRingHom)) b.val

theorem rootValue_galois (f : Kˣ) (t : Fiber (geometricPoint K) (rootCover K n f))
    (σ : Field.absoluteGaloisGroup K) :
    rootValue K n f (pointEnd K σ ≫ t) = GroupCohomology.Kummer.unitAction K σ (rootValue K n f
        t) := by
  unfold rootValue
  rw [AlgebraicGeometry.Scheme.Group.RootCover.sectionsEquiv_naturality]
  exact units_galois K σ _


variable [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]

/-- The finite locally constant root coefficient at nonzero level over a characteristic-zero
field. -/
def finiteCoefficient : FiniteCoefficient
    (GroupCohomology.Kummer.Coefficients.mu (Spec (.of K)) n) where
  level := n
  positive := NeZero.pos n
  killed := GroupCohomology.Kummer.Coefficients.mu_killedBy _ n
  invertible := GroupCohomology.Kummer.RootStalk.levelInvertible K n
  locally_constant := representedSheaf_isFiniteLocallyConstant (s := geometricPoint K) _

/-- Restriction along the proved field fundamental-group equivalence, on the
existing coefficient group with its actual Galois action. -/
def galoisRestriction : PullbackMap (A := Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (B :=
    Field.absoluteGaloisGroup.RootsOfUnity.Mu K n)
    (fieldGroupHom K) where
  toFun := id
  map_zero' := rfl
  map_add' _ _ := rfl
  continuous_toFun := continuous_id
  map_smul' σ a := by
    change (fundamentalGroupContinuousEquiv K).symm (fundamentalGroupContinuousEquiv K σ) • a =
        σ • a
    rw [ContinuousMulEquiv.symm_apply_apply]

/-- The identity coefficient map for restriction from the Galois group to the fundamental group. -/
def fundamentalRestriction : PullbackMap (A := Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (B :=
    Field.absoluteGaloisGroup.RootsOfUnity.Mu K n)
    (absoluteGroupHom K) where
  toFun := id
  map_zero' := rfl
  map_add' _ _ := rfl
  continuous_toFun := continuous_id
  map_smul' _ _ := rfl

/-- The additive equivalence on continuous first cohomology induced by the field group
equivalence. -/
def galoisRestrictionEquiv : H1 (FieldFundamentalGroup K)
    (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) ≃+
    H1 (Field.absoluteGaloisGroup K) (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) where
  toFun := (galoisRestriction K n).onH1
  invFun := (fundamentalRestriction K n).onH1
  left_inv x := by
    obtain ⟨c, rfl⟩ := classOf_surjective (FieldFundamentalGroup K)
        (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) x
    change classOf _ _ ((fundamentalRestriction K n).onCocycles ((galoisRestriction K
        n).onCocycles c)) = classOf _ _ c
    congr 1
    apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
    intro γ
    change c.val ((fundamentalGroupContinuousEquiv K) ((fundamentalGroupContinuousEquiv K).symm
        γ)) = c.val γ
    rw [ContinuousMulEquiv.apply_symm_apply]
  right_inv x := by
    obtain ⟨c, rfl⟩ := classOf_surjective (Field.absoluteGaloisGroup K)
        (Field.absoluteGaloisGroup.RootsOfUnity.Mu
        K n) x
    change classOf _ _ ((galoisRestriction K n).onCocycles ((fundamentalRestriction K
        n).onCocycles c)) = classOf _ _ c
    congr 1
    apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
    intro σ
    change c.val ((fundamentalGroupContinuousEquiv K).symm ((fundamentalGroupContinuousEquiv K)
        σ)) = c.val σ
    rw [ContinuousMulEquiv.symm_apply_apply]
  map_add' := map_add _

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]

/-- The existing field marking supplies the represented comparison once. -/
private def fieldRepresentedH1AddEquiv
    (hA : Stacks03AJ.{u, w} (Spec (.of K))) (hR : Stacks03RV (Spec (.of K))) :=
  Scheme.EtaleCohomology.FundamentalGroupComparison.representedH1AddEquiv
    (geometricPoint K) (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) hA hR
    (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (pointMark K n)
    (pointMark_equivariant K n) (finiteCoefficient K n)

/-- The etale-to-Galois first-cohomology map using the supplied `Stacks03AJ` and `Stacks03RV`
inputs. -/
def comparison (hA : Stacks03AJ.{u, w} (Spec (.of K))) (hR : Stacks03RV (Spec (.of K))) :
    H1Etale (Spec (.of K)) (GroupCohomology.Kummer.Coefficients.mu (Spec (.of
        K)) n) →+
      H1 (Field.absoluteGaloisGroup K) (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) :=
  (galoisRestriction K n).onH1.comp
    (fieldRepresentedH1AddEquiv K n hA hR).toAddMonoidHom


/-- The additive etale-to-Galois first-cohomology equivalence using the supplied comparison
inputs. -/
def comparisonEquiv (hA : Stacks03AJ.{u, w} (Spec (.of K))) (hR : Stacks03RV (Spec (.of K))) :
    H1Etale (Spec (.of K)) (GroupCohomology.Kummer.Coefficients.mu (Spec (.of
        K)) n) ≃+
      H1 (Field.absoluteGaloisGroup K) (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) :=
  (fieldRepresentedH1AddEquiv K n hA hR).trans (galoisRestrictionEquiv K n)

private theorem comparison_original
    (hA : Stacks03AJ.{u, w} (Spec (.of K))) (hR : Stacks03RV (Spec (.of K))) :
    comparison K n hA hR = (galoisRestriction K n).onH1.comp
      (Scheme.EtaleCohomology.FundamentalGroupComparison.representedH1AddEquiv
    (geometricPoint K) (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) hA hR
    (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (pointMark K n)
    (pointMark_equivariant K n) (finiteCoefficient K n)).toAddMonoidHom := rfl

private theorem comparisonEquiv_original
    (hA : Stacks03AJ.{u, w} (Spec (.of K))) (hR : Stacks03RV (Spec (.of K))) :
    comparisonEquiv K n hA hR =
      (Scheme.EtaleCohomology.FundamentalGroupComparison.representedH1AddEquiv
    (geometricPoint K) (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) hA hR
    (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (pointMark K n)
    (pointMark_equivariant K n) (finiteCoefficient K n)).trans (galoisRestrictionEquiv K n) := rfl

@[simp] theorem comparisonEquiv_apply (hA : Stacks03AJ.{u, w} (Spec (.of K)))
    (hR : Stacks03RV (Spec (.of K)))
    (x : H1Etale (Spec (.of K)) (GroupCohomology.Kummer.Coefficients.mu (Spec
        (.of K)) n)) :
    comparisonEquiv K n hA hR x = comparison K n hA hR x := rfl


/-- The continuous Galois cocycle obtained from a based finite etale roots-of-unity torsor. -/
def fieldCocycle (Y : Scheme.FiniteEtale (Spec (.of K)))
    (τ : _root_.CategoryTheory.TorsorAction
      (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n)
          (CategoryTheory.CartesianMonoidalCategory.toUnit Y.obj))
    (t : Fiber (geometricPoint K) Y) :
    Cocycle (Field.absoluteGaloisGroup K) (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) :=
  (galoisRestriction K n).onCocycles
    (Scheme.EtaleCohomology.FundamentalGroupComparison.markedBasedCocycle
        (geometricPoint K)
      (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n)
      (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (pointMark K n) (pointMark_equivariant K
          n) Y τ t)

theorem fieldCocycle_value (Y : Scheme.FiniteEtale (Spec (.of K)))
    (τ : _root_.CategoryTheory.TorsorAction
      (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n)
          (CategoryTheory.CartesianMonoidalCategory.toUnit Y.obj))
    (t : Fiber (geometricPoint K) Y) (σ : Field.absoluteGaloisGroup K) :
    (fieldCocycle K n Y τ t).val σ =
      (pointMark K n (Scheme.FiniteEtale.FiberTorsorActions.transport
        (geometricPoint K) (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n)
        Y τ t (pointEnd K σ ≫ t))).toAdd := by
  exact Scheme.EtaleCohomology.FundamentalGroupComparison.markedBasedCocycle_apply (geometricPoint
    K)
    (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n)
    (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (pointMark K n) (pointMark_equivariant K n)
    Y τ t (fundamentalGroupContinuousEquiv K σ)

private theorem fieldRepresentedH1AddEquiv_torsor_representative
    (hA : Stacks03AJ.{u, w} (Spec (.of K))) (hR : Stacks03RV (Spec (.of K)))
    (P : Torsor (GroupCohomology.Kummer.Coefficients.mu (Spec (.of K)) n))
    (Y : Scheme.FiniteEtale (Spec (.of K))) (e : finiteRepresentedSetSheaf Y ≅ P.carrier)
    (t : Fiber (geometricPoint K) Y) :
    fieldRepresentedH1AddEquiv K n hA hR (torsorExtClass P) =
      classOf (Scheme.EtaleFundamentalGroups.FiberAutGroup (geometricPoint K))
        (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n)
        (Scheme.EtaleCohomology.FundamentalGroupComparison.markedBasedCocycle
          (geometricPoint K) (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n)
          (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (pointMark K n)
          (pointMark_equivariant K n) Y
          (P.representedSchemeAction
            (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) Y e) t) := by
  unfold fieldRepresentedH1AddEquiv
  exact
    Scheme.EtaleCohomology.FundamentalGroupComparison.representedH1AddEquiv_torsor_representative
    (geometricPoint K) (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) hA hR
    (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (pointMark K n)
    (pointMark_equivariant K n) (finiteCoefficient K n) P Y e t

theorem comparison_torsor_representative
    (hA : Stacks03AJ.{u, w} (Spec (.of K))) (hR : Stacks03RV (Spec (.of K)))
    (P : Torsor (GroupCohomology.Kummer.Coefficients.mu (Spec (.of K)) n))
    (Y : Scheme.FiniteEtale (Spec (.of K))) (e : finiteRepresentedSetSheaf Y ≅ P.carrier)
    (t : Fiber (geometricPoint K) Y) :
    comparison K n hA hR (torsorExtClass P) =
      classOf (Field.absoluteGaloisGroup K) (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n)
        (fieldCocycle K n Y
          (P.representedSchemeAction (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) Y
              e) t) := by
  have h := fieldRepresentedH1AddEquiv_torsor_representative K n hA hR P Y e t
  have hmap := congrArg ((galoisRestriction K n).onH1) h
  have hclass :=
    _root_.GroupCohomology.ContinuousH1.PullbackMap.onH1_classOf (galoisRestriction K n)
      (Scheme.EtaleCohomology.FundamentalGroupComparison.markedBasedCocycle
        (geometricPoint K) (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n)
        (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n) (pointMark K n)
        (pointMark_equivariant K n) Y
        (P.representedSchemeAction (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) Y e) t)
  have hvalue := comparisonEquiv_apply K n hA hR (torsorExtClass P)
  refine hvalue.symm.trans ?_
  simpa only [comparisonEquiv, AddEquiv.trans_apply, galoisRestrictionEquiv,
    fieldCocycle] using hmap.trans hclass




theorem root_fieldCocycle (f : Kˣ) (t : Fiber (geometricPoint K) (rootCover K n f)) :
    fieldCocycle K n (rootCover K n f) (rootAction K n f) t =
      GroupCohomology.Kummer.cocycle K n (rootValue K n f t) (rootValue_pow K n f t) := by
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro σ
  rw [fieldCocycle_value]
  let z := Scheme.FiniteEtale.FiberTorsorActions.transport
      (geometricPoint K)
    (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) (rootCover K n f)
    (rootAction K n f) t (pointEnd K σ ≫ t)
  have hz := Scheme.FiniteEtale.FiberTorsorActions.transport_act
      (geometricPoint K)
    (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) (rootCover K n f)
    (rootAction K n f) t (pointEnd K σ ≫ t)
  have hr := AlgebraicGeometry.Scheme.Group.RootCover.torsorAction_transport_ratio
    (Spec (.of K)) n (globalUnit K f) (Over.mk (geometricPoint K)) z t (pointEnd K σ ≫ t) hz
  apply Additive.toMul.injective
  apply Subtype.ext
  change Units.map (Scheme.ΓSpecIso (.of (AlgebraicClosure K))).hom.hom.toMonoidHom
    (MultiplicativeGroup.rootsHomEquiv (Spec (.of K)) n (Over.mk (geometricPoint K)) z).val =
      GroupCohomology.Kummer.unitAction K σ (rootValue K n f t) / rootValue K n f t
  calc
    _ = rootValue K n f (pointEnd K σ ≫ t) / rootValue K n f t := by
      rw [hr, map_div]
      rfl
    _ = _ := by rw [rootValue_galois]

/-- The actual positive root torsor maps to the existing positive field Kummer
class; the equality follows from actual transport σ(a)/a. -/
theorem comparison_rootClass (hA : Stacks03AJ.{u, w} (Spec (.of K)))
    (hR : Stacks03RV (Spec (.of K))) (f : Kˣ) :
    comparison K n hA hR
      (GroupCohomology.Kummer.Torsor.rootClass
        GroupCohomology.Kummer.RootCover.etalePowerSurjectivity (Spec (.of K)) n
        (NeZero.pos n) (GroupCohomology.Kummer.RootStalk.levelInvertible K n)
            (globalUnit K f)) =
      GroupCohomology.Kummer.kummer K n (NeZero.pos n) f := by
  obtain ⟨t⟩ :=
      Scheme.EtaleCohomology.SchemeTorsorClassification.nonempty_fiber_of_surjective
        (geometricPoint K)
          (rootCover K n f)
  rw [GroupCohomology.Kummer.RootCover.rootClass_eq_scheme]
  rw [comparison_torsor_representative K n hA hR _ (rootCover K n f) (Iso.refl _) t]
  rw [torsorOfSchemeAction_representedSchemeAction]
  change classOf (Field.absoluteGaloisGroup K) (Field.absoluteGaloisGroup.RootsOfUnity.Mu K n)
    (fieldCocycle K n (rootCover K n f) (rootAction K n f) t) = _
  rw [root_fieldCocycle]
  exact (GroupCohomology.Kummer.kummer_eq_class K n (rootValue K n f t) (rootValue_pow K n f t)
      (NeZero.pos n)).symm


end GroupCohomology.Kummer.Field
