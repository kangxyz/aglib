/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FundamentalGroupComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.Group.MultiplicativeBaseChange
public import Aglib.GroupCohomology.H1.SplitExtension
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.GeometricCoefficients` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`2f9d8c871aa0d3b7171ee4ae1e6accd9afe7fb408e6a4968f29164ee471f851a`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual constant-root marking and the geometric-character injection

C4/C5 support for `K2-018#lem:k2018-geometric-exact-order` and
`K2-018#prop:k2018-arithmetic-characters`. Mathematical basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

An actual root of unity in the geometric base field gives a global root
section, whose restriction at the rational point is proved by Gamma(Spec)
and the structure-morphism identity. Every geometric root point is of this
form, so actual finite-fibre monodromy is trivial by naturality against the
terminal cover. A specified primitive root supplies the positive ZMod
coordinate; no arbitrary cyclic isomorphism or trivial-action hypothesis
is substituted for this calculation.

The actual represented finite coefficient and A's Ext/torsor comparison
then identify its etale H1 with the common continuous H1. Restricting an
equivariant character along a displayed continuous geometric group
isomorphism gives an injective common-H1 map: the only principal cocycle
for the proved trivial action is zero. Composing with the inverse actual
etale comparison yields the needed injection into actual mu_n H1.

Only A's precise 03AJ/03RV families, actual Galois-category/fibre-functor
classes and displayed Ext-size instances are retained. The higher curve
application supplies the existing actual 0BTX kernel isomorphism. This
module neither assumes a Picard comparison nor identifies equivariant
characters with the entire Picard torsion group.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open CartesianMonoidalCategory
open _root_.AlgebraicGeometry.Scheme.EtaleCohomology.FundamentalGroupComparison
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open AlgebraicGeometry.Scheme.Group
namespace GroupCohomology.Kummer.GeometricCoefficients
universe u w
variable (C : Type u) [Field C] {X : Scheme.{u}} (p : X ⟶ Spec (.of C))
  (x : Spec (.of C) ⟶ X) (h : x ≫ p = 𝟙 _) (n : ℕ)
attribute [local instance] Over.cartesianMonoidalCategory

/-- The group scheme of nth roots of unity over the given scheme. -/
abbrev groupScheme := MultiplicativeGroup.rootsGroupScheme X n
/-- The native commutative group law on the represented roots-of-unity scheme. -/
local instance : CommGrpObj (MultiplicativeGroup.rootsScheme X n) :=
  MultiplicativeGroup.rootsCommGroup X n

/-- Actual root coordinates at the rational geometric point. -/
def pointRoots : (Over.mk x ⟶ (groupScheme (X := X) n).X) ≃* rootsOfUnity n C :=
  (GroupCohomology.Kummer.Coefficients.rootsMulEquiv X n (Over.mk x)).trans
    ((Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv.toMulEquiv.restrictRootsOfUnity n)

/-- The given geometric point as a morphism to the identity cover. -/
def pointToIdentity : Over.mk x ⟶ Over.mk (𝟙 X) := Over.homMk x (by simp)

/-- An actual constant root supplies a global section of the roots scheme. -/
def constantSection (a : rootsOfUnity n C) : Over.mk (𝟙 X) ⟶ (groupScheme (X := X) n).X :=
  (MultiplicativeGroup.rootsHomEquiv X n (Over.mk (𝟙 X))).symm
    (restrictRootsOfUnity (((Scheme.ΓSpecIso (.of C)).inv ≫ p.appTop).hom) n a)

include h in
/-- Restricting this actual global section recovers its specified field root. -/
theorem constantSection_point (a : rootsOfUnity n C) :
    pointRoots C x n (pointToIdentity C x ≫ constantSection C p n a) = a := by
  apply Subtype.ext
  apply Units.ext
  have hh := (MultiplicativeGroup.rootsRepresentable X n).homEquiv_comp
    (pointToIdentity C x) (constantSection C p n a)
  have hh' := congrArg (fun z : rootsOfUnity n Γ(Spec (.of C), ⊤) =>
    (Scheme.ΓSpecIso (.of C)).hom.hom z.val.val) hh
  change (Scheme.ΓSpecIso (.of C)).hom.hom
    (MultiplicativeGroup.rootsHomEquiv X n (Over.mk x)
      (pointToIdentity C x ≫ constantSection C p n a)).val.val = a.val.val
  calc
    _ = (Scheme.ΓSpecIso (.of C)).hom.hom (x.appTop.hom
        (MultiplicativeGroup.rootsHomEquiv X n (Over.mk (𝟙 X)) (constantSection C p n
            a)).val.val) := hh'
    _ = (Scheme.ΓSpecIso (.of C)).hom.hom (x.appTop.hom
        (p.appTop.hom ((Scheme.ΓSpecIso (.of C)).inv.hom a.val.val))) := by
      rw [constantSection, Equiv.apply_symm_apply]
      rfl
    _ = a.val.val := by
      have hc := congrArg (fun f : Spec (.of C) ⟶ Spec (.of C) => f.appTop) h
      have hv := ConcreteCategory.congr_hom hc ((Scheme.ΓSpecIso (.of C)).inv.hom a.val.val)
      change x.appTop.hom (p.appTop.hom _) = _ at hv
      rw [hv]
      exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of C)).inv_hom_id a.val.val

include h in
/-- Every actual root point is the restriction of a constant global section. -/
theorem point_eq_constant (a : Over.mk x ⟶ (groupScheme (X := X) n).X) :
    pointToIdentity C x ≫ constantSection C p n (pointRoots C x n a) = a :=
  (pointRoots C x n).injective (constantSection_point C p x h n _)

variable [CharZero C] [NeZero n]

include p in
theorem levelInvertible : LevelInvertible X n := by
  have hn : IsUnit (n : C) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  simpa only [LevelInvertible, map_natCast] using
    (hn.map (Scheme.ΓSpecIso (.of C)).inv.hom).map p.appTop.hom

local instance : IsFinite (groupScheme (X := X) n).X.hom :=
  RootsFiniteEtale.rootsScheme_finite X n (NeZero.pos n)
section RootAction
variable [Etale (groupScheme (X := X) n).X.hom]

include p h in
omit [CharZero C] in
/-- Global constant roots force literal finite-fibre monodromy to be trivial. -/
-- Retain the characteristic-zero guard of the original geometric coefficient interface.
@[nolint unusedArguments]
theorem point_action_trivial [CharZero C] (γ : FiberAutGroup x)
    (a : Over.mk x ⟶ (groupScheme (X := X) n).X) :
    γ.hom.app (coefficientCover (groupScheme (X := X) n)) a = a := by
  let Z : Scheme.FiniteEtale X := Scheme.FiniteEtale.mk (𝟙 X)
  have he : γ.hom.app Z (pointToIdentity C x) = pointToIdentity C x := by
    apply Over.OverMorphism.ext
    have hh := Over.w (γ.hom.app Z (pointToIdentity C x))
    change _ ≫ 𝟙 X = x at hh
    change (γ.hom.app Z (pointToIdentity C x)).left = x
    simpa only [Category.comp_id] using hh
  rw [← point_eq_constant C p x h n a]
  have hn := evaluation_naturality x γ (Z := Z)
    (W := coefficientCover (groupScheme (X := X) n))
    (constantSection C p n (pointRoots C x n a)) (pointToIdentity C x)
  exact hn.trans (congrArg (fun t => t ≫ constantSection C p n (pointRoots C x n a)) he)

/-- The specified primitive root fixes the positive cyclic coordinate. -/
def rootCoordinate (ζ : rootsOfUnity n C) (hζ : IsPrimitiveRoot (ζ : Cˣ) n) :
    ZMod n ≃+ Additive (rootsOfUnity n C) :=
  hζ.zmodEquivZPowers.trans (MulEquiv.subgroupCongr hζ.zpowers_eq).toAdditive

omit [CharZero C] in
-- Retain the original characteristic-zero primitive-root marking interface.
@[nolint unusedArguments, simp] theorem rootCoordinate_one [CharZero C] (ζ : rootsOfUnity n C)
    (hζ : IsPrimitiveRoot (ζ : Cˣ) n) : rootCoordinate C n ζ hζ 1 = Additive.ofMul ζ := by
  unfold rootCoordinate
  rw [AddEquiv.trans_apply]
  have hh := hζ.zmodEquivZPowers_apply_coe_nat 1
  simp only [Nat.cast_one, pow_one] at hh
  rw [hh]
  rfl

/-- The geometric fibre marking is evaluation followed by this fixed coordinate. -/
def pointMark (ζ : rootsOfUnity n C) (hζ : IsPrimitiveRoot (ζ : Cˣ) n) :
    (Over.mk x ⟶ (groupScheme (X := X) n).X) ≃* Multiplicative (ZMod n) :=
  (pointRoots C x n).trans (rootCoordinate C n ζ hζ).symm.toMultiplicative

omit [Etale (groupScheme (X := X) n).X.hom] in
-- Retain etaleness of the actual represented coefficient group in the public point-marking API.
@[nolint unusedArguments]
theorem pointMark_root [Etale (groupScheme (X := X) n).X.hom]
    (ζ : rootsOfUnity n C) (hζ : IsPrimitiveRoot (ζ : Cˣ) n)
    (a : Over.mk x ⟶ (groupScheme (X := X) n).X) (ha : pointRoots C x n a = ζ) :
    pointMark C x n ζ hζ a = Multiplicative.ofAdd 1 := by
  change (rootCoordinate C n ζ hζ).symm (Additive.ofMul (pointRoots C x n a)) = 1
  apply (rootCoordinate C n ζ hζ).injective
  rw [AddEquiv.apply_symm_apply, rootCoordinate_one, ha]

/-- The action of fibre automorphisms on the root-coordinate group that fixes every element. -/
@[instance_reducible] def trivialRootAction : DistribMulAction (FiberAutGroup x) (ZMod n) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- Use the trivial root-coordinate action when checking finite-fibre equivariance. -/
local instance : DistribMulAction (FiberAutGroup x) (ZMod n) := trivialRootAction C x n
local instance : ContinuousSMul (FiberAutGroup x) (ZMod n) := ⟨continuous_snd⟩

include p h in
theorem pointMark_equivariant (ζ : rootsOfUnity n C)
    (hζ : IsPrimitiveRoot (ζ : Cˣ) n) (γ : FiberAutGroup x)
    (a : Over.mk x ⟶ (groupScheme (X := X) n).X) :
    pointMark C x n ζ hζ (γ.hom.app (coefficientCover (groupScheme (X := X) n)) a) =
      Multiplicative.ofAdd (γ • (pointMark C x n ζ hζ a).toAdd) := by
  rw [point_action_trivial C p x h n]
  rfl

end RootAction
/-- Use the trivial root-coordinate action for the geometric coefficient comparison. -/
local instance : DistribMulAction (FiberAutGroup x) (ZMod n) := trivialRootAction C x n
local instance : ContinuousSMul (FiberAutGroup x) (ZMod n) := ⟨continuous_snd⟩

variable [IsAlgClosed C] [PreconnectedSpace X]
  [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite x)]

/-- The roots sheaf as a finite locally constant coefficient of positive invertible level. -/
def finiteCoefficient : FiniteCoefficient
    (GroupCohomology.Kummer.Coefficients.mu X n) := by
  letI : Etale (MultiplicativeGroup.rootsGroupScheme X n).X.hom :=
    RootsFiniteEtale.rootsScheme_etale X n (NeZero.pos n) (levelInvertible C p n)
  exact { level := n
          positive := NeZero.pos n
          killed := GroupCohomology.Kummer.Coefficients.mu_killedBy X n
          invertible := levelInvertible C p n
          locally_constant := representedSheaf_isFiniteLocallyConstant (s := x) _ }

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Compare etale roots classes with continuous fibre-group cohomology using the chosen primitive
root and the supplied torsor and locally constant comparison inputs. -/
def comparison (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
    (ζ : rootsOfUnity n C) (hζ : IsPrimitiveRoot (ζ : Cˣ) n) :
    H1Etale X (GroupCohomology.Kummer.Coefficients.mu X n) ≃+
        _root_.GroupCohomology.ContinuousH1.H1 (FiberAutGroup x) (ZMod n) := by
  letI := trivialRootAction C x n
  letI : ContinuousSMul (FiberAutGroup x) (ZMod n) := ⟨continuous_snd⟩
  letI : Etale (MultiplicativeGroup.rootsGroupScheme X n).X.hom :=
    RootsFiniteEtale.rootsScheme_etale X n (NeZero.pos n) (levelInvertible C p n)
  exact representedH1AddEquiv x (groupScheme (X := X) n) hA hR (ZMod n)
    (pointMark C x n ζ hζ) (pointMark_equivariant C p x h n ζ hζ)
    (finiteCoefficient C p x n)

section Characters
/-- Use the trivial root-coordinate action for the equivariant-character constructions. -/
local instance : DistribMulAction (FiberAutGroup x) (ZMod n) := trivialRootAction C x n
local instance : ContinuousSMul (FiberAutGroup x) (ZMod n) := ⟨continuous_snd⟩
open _root_.GroupCohomology _root_.TopologicalGroup
variable {G N : Type*} [Group G] [Group N]
  [TopologicalSpace G] [TopologicalSpace N] [MulDistribMulAction G N]
  [DistribMulAction G (ZMod n)]
variable (e : FiberAutGroup x ≃ₜ* N)

/-- Pull the equivariant character back along the specified fibre-group isomorphism to a
continuous cocycle. -/
def characterCocycle (c : _root_.GroupCohomology.PointedCohomology.EquivariantCharacter G N
    (ZMod n)) :
    _root_.GroupCohomology.ContinuousH1.Cocycle (FiberAutGroup x) (ZMod n) :=
  ⟨⟨fun g => c.toFun (e g), c.continuous_toFun.comp e.continuous⟩,
    fun g k => by
      change c.toFun (e (g * k)) = c.toFun (e g) + c.toFun (e k)
      rw [map_mul]
      exact c.map_mul (e g) (e k)⟩

/-- Send an equivariant character to the continuous cohomology class of its pulled-back cocycle. -/
def characterH1 : _root_.GroupCohomology.PointedCohomology.EquivariantCharacter G N (ZMod n) →+
    _root_.GroupCohomology.ContinuousH1.H1 (FiberAutGroup x) (ZMod n) where
  toFun c := _root_.GroupCohomology.ContinuousH1.classOf _ _ (characterCocycle C x n e c)
  map_zero' := by
    change _root_.GroupCohomology.ContinuousH1.classOf _ _ 0 = 0
    exact map_zero _
  map_add' c d := by
    change _root_.GroupCohomology.ContinuousH1.classOf _ _ (characterCocycle C x n e c +
        characterCocycle C x n e d) = _
    exact map_add _ _ _

omit [CharZero C] [NeZero n] [IsAlgClosed C] [PreconnectedSpace X]
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite x)] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [TopologicalSpace G] in
-- Retain the original geometric, Galois, Ext-size and topological character-comparison inputs.
@[nolint unusedArguments]
theorem characterH1_injective [CharZero C] [NeZero n] [IsAlgClosed C] [PreconnectedSpace X]
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite x)] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [TopologicalSpace G] : Function.Injective (characterH1 C x n (G := G) e) := by
  intro c d hcd
  obtain ⟨a, ha⟩ := (_root_.GroupCohomology.ContinuousH1.classOf_eq_iff _ _ _ _).mp hcd
  apply _root_.GroupCohomology.PointedCohomology.EquivariantCharacter.ext
  intro k
  obtain ⟨g, rfl⟩ := e.surjective k
  have hh := congrArg (fun z : _root_.GroupCohomology.ContinuousH1.Cocycle (FiberAutGroup x)
      (ZMod n) => z.val g) ha
  change a - a = c.toFun (e g) - d.toFun (e g) at hh
  exact sub_eq_zero.mp ((sub_self a).symm.trans hh).symm

/-- The actual marked etale comparison sends this class to the given character. -/
def characterEtale (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
    (ζ : rootsOfUnity n C) (hζ : IsPrimitiveRoot (ζ : Cˣ) n) :
    _root_.GroupCohomology.PointedCohomology.EquivariantCharacter G N (ZMod n) →+ H1Etale X
        (GroupCohomology.Kummer.Coefficients.mu X n) :=
  (comparison C p x h n hA hR ζ hζ).symm.toAddMonoidHom.comp (characterH1 C x n e)

omit [IsAlgClosed C] [TopologicalSpace G] in
-- Retain the original algebraically closed coefficient and topological character context.
@[nolint unusedArguments, simp]
theorem comparison_characterEtale [IsAlgClosed C] [TopologicalSpace G] (hA :
    Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
    (ζ : rootsOfUnity n C) (hζ : IsPrimitiveRoot (ζ : Cˣ) n)
    (c : _root_.GroupCohomology.PointedCohomology.EquivariantCharacter G N (ZMod n)) :
    comparison C p x h n hA hR ζ hζ (characterEtale C p x h n e hA hR ζ hζ c) =
      characterH1 C x n e c :=
  (comparison C p x h n hA hR ζ hζ).apply_symm_apply _

theorem characterEtale_injective (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
    (ζ : rootsOfUnity n C) (hζ : IsPrimitiveRoot (ζ : Cˣ) n) :
    Function.Injective (characterEtale C p x h n (G := G) e hA hR ζ hζ) :=
  (comparison C p x h n hA hR ζ hζ).symm.injective.comp (characterH1_injective C x n e)
end Characters
end GroupCohomology.Kummer.GeometricCoefficients
