/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Canonical pullback on actual Zariski cohomology

Exact inverse image, constant-sheaf transport and the actual structural sheaf
map induce the cohomology maps. Coefficient naturality, F-linearity and
semilinearity for actual structural field-change squares are proved.

Original application provenance: K2-018#prop:k2018-arithmetic-characters, expose.tex lines341–445,
mathematical source e73d98b1b5c1e5abcdebf7d058e436d792b87982;
engineering basis7f86e4a1763cc4ec35e9b0a8acd659750355a0de,
Lean4.34.1/mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
No new general theorem premise occurs in this module.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.Pullback` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Inverse image of Zariski sheaves of abelian groups along `f`. -/
abbrev zariskiPullback :
    Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base
/-- Direct image of Zariski sheaves of abelian groups along `f`. -/
abbrev zariskiPushforward :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base

instance zariskiPullback_leftAdjoint : (zariskiPullback f).IsLeftAdjoint :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).isLeftAdjoint
instance opensMapFlat : RepresentablyFlat (Opens.map f.base) :=
  flat_of_preservesFiniteLimits _
attribute [local instance] reflectsLimits_of_reflectsIsomorphisms
instance : PreservesFiniteLimits (zariskiPullback f) := by
  change PreservesFiniteLimits ((Opens.map f.base).sheafPullback AddCommGrpCat.{u} _ _)
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits
instance : (zariskiPullback f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Global sections of a direct image, identified with global sections on `X`. -/
def pushforwardSectionsIso :
    zariskiPushforward f ⋙ (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (op ⊤) ≅
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun S ↦ S.obj.mapIso (eqToIso (by simp))) (by
    intro S T g
    dsimp
    simp)

/-- The canonical isomorphism between inverse image of a constant abelian sheaf and the constant
sheaf on `X`. -/
def constantPullbackIso :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙ zariskiPullback f ≅
      constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base)).ofNatIsoRight
        (pushforwardSectionsIso f)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)

/-- The structural map from the additive structure sheaf of `Y` to the direct image of that of
`X`. -/
def structurePushforwardMap : structureAddSheaf Y ⟶ (zariskiPushforward f).obj
  (structureAddSheaf X) where
  hom := Functor.whiskerRight f.c
    ((forget₂ CommRingCat RingCat.{u}) ⋙ forget₂ RingCat AddCommGrpCat.{u})

/-- The map from the inverse image of the additive structure sheaf of `Y` to that of `X`, adjoint
to `structurePushforwardMap f`. -/
def structurePullbackMap : (zariskiPullback f).obj (structureAddSheaf Y) ⟶ structureAddSheaf X :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _).symm
    (structurePushforwardMap f)

/-- Pullback on actual Zariski structure-sheaf cohomology along any scheme
morphism: exact inverse image, the canonical constant-sheaf isomorphism,
and the structural sheaf map. No cohomology map is supplied as an input. -/
def zariskiCohomologyMap
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback f).obj A ⟶ B) (n : ℕ) :
    Sheaf.H.{u + 1} A n →+ Sheaf.H.{u + 1} B n :=
  ((Abelian.Ext.mk₀ a).postcomp
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) (Nat.add_zero n)).comp
    (((Abelian.Ext.mk₀ ((constantPullbackIso f).inv.app
        (AddCommGrpCat.of (ULift.{u} ℤ)))).precomp
      ((zariskiPullback f).obj A) (Nat.zero_add n)).comp
      ((zariskiPullback f).mapExtAddHom
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) A n))
/-- Pullback on degree-`n` cohomology of the additive structure sheaf along `f`. -/
def structureCohomologyPullback (n : ℕ) :
    Sheaf.H.{u + 1} (structureAddSheaf Y) n →+ Sheaf.H.{u + 1} (structureAddSheaf X) n :=
  zariskiCohomologyMap f _ _ (structurePullbackMap f) n

/-- The actual inverse-image cohomology map is natural in its coefficient sheaves: a commuting
coefficient square gives a commuting square on cohomology. -/
theorem zariskiCohomologyMap_map
    {A A' : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {B B' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : (zariskiPullback f).obj A ⟶ B) (a' : (zariskiPullback f).obj A' ⟶ B')
    (α : A ⟶ A') (β : B ⟶ B') (h : (zariskiPullback f).map α ≫ a' = a ≫ β)
    (n : ℕ) (x : Sheaf.H.{u + 1} A n) :
    zariskiCohomologyMap f A' B' a' n (Sheaf.H.map α n x) =
      Sheaf.H.map β n (zariskiCohomologyMap f A B a n x) := by
  change ((Abelian.Ext.mk₀ _).comp
      ((x.comp (Abelian.Ext.mk₀ α) (Nat.add_zero n)).mapExactFunctor (zariskiPullback f))
        (Nat.zero_add n)).comp (Abelian.Ext.mk₀ a') (Nat.add_zero n) =
    (((Abelian.Ext.mk₀ _).comp (x.mapExactFunctor (zariskiPullback f)) (Nat.zero_add n)).comp
      (Abelian.Ext.mk₀ a) (Nat.add_zero n)).comp (Abelian.Ext.mk₀ β) (Nat.add_zero n)
  simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, h]

/-- Naturality in the coefficient morphisms of the actual inverse-image map; the endomorphism
case of `zariskiCohomologyMap_map`. -/
theorem zariskiCohomologyMap_naturality
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback f).obj A ⟶ B) (α : A ⟶ A) (β : B ⟶ B)
    (h : (zariskiPullback f).map α ≫ a = a ≫ β)
    (n : ℕ) (x : Sheaf.H.{u + 1} A n) :
    zariskiCohomologyMap f A B a n (Sheaf.H.map α n x) =
      Sheaf.H.map β n (zariskiCohomologyMap f A B a n x) :=
  zariskiCohomologyMap_map f a a α β h n x
end AlgebraicGeometry.Scheme.Cohomology
namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.OverField
universe u
variable {F : Type u} [Field F] {X Y : FScheme F} (f : X ⟶ Y)

theorem map_constants (a : F) :
    f.left.appTop (constants Y a) = constants X a := by
  change (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ Y.hom.appTop) ≫ f.left.appTop).hom a =
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ X.hom.appTop).hom a
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, Over.w f]

theorem app_constantSection (U : Y.left.Opens) (a : F) :
    f.left.app U (constantSection Y U a) =
      constantSection X (f.left ⁻¹ᵁ U) a := by
  have hn := congrArg
    (fun q : Γ(Y.left, ⊤) ⟶ Γ(X.left, f.left ⁻¹ᵁ U) ↦ q.hom (constants Y a))
    (f.left.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change f.left.app U (constantSection Y U a) =
    X.left.presheaf.map _ (f.left.appTop (constants Y a)) at hn
  rw [map_constants] at hn
  exact hn

theorem structurePushforward_scalar (a : F) :
    structureScalar Y a ≫ structurePushforwardMap f.left =
      structurePushforwardMap f.left ≫ (zariskiPushforward f.left).map (structureScalar X a) := by
  ext U x
  change Γ(Y.left, U.unop) at x
  change f.left.app U.unop (constantSection Y U.unop a * x) =
    constantSection X (f.left ⁻¹ᵁ U.unop) a * f.left.app U.unop x
  rw [map_mul, app_constantSection]

theorem structurePullback_scalar (a : F) :
    (zariskiPullback f.left).map (structureScalar Y a) ≫ structurePullbackMap f.left =
      structurePullbackMap f.left ≫ structureScalar X a := by
  have hn := congrArg
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.left.base).homEquiv _ _).symm)
      (structurePushforward_scalar f a)
  dsimp only [zariskiPushforward] at hn
  rw [Adjunction.homEquiv_naturality_right_symm] at hn
  simpa only [Adjunction.homEquiv_naturality_left_symm, structurePullbackMap, zariskiPullback]
    using hn

/-- Actual F-linear pullback map, proved from the structural equation of an
F-scheme morphism and naturality of the constructed cohomology map. -/
def structureCohomologyPullbackLinear (n : ℕ) :
    structureCohomology F Y n →ₗ[F] structureCohomology F X n where
  __ := structureCohomologyPullback f.left n
  map_smul' a x :=
    zariskiCohomologyMap_naturality f.left _ _ (structurePullbackMap f.left)
      (structureScalar Y a) (structureScalar X a) (structurePullback_scalar f a) n x
end AlgebraicGeometry.Scheme.Cohomology
namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.OverField
universe u
variable {F K : Type u} [Field F] [Field K]
variable (σ : F →+* K) (X : FScheme K) (Y : FScheme F)
variable (f : X.left ⟶ Y.left)
variable (hf : f ≫ Y.hom = X.hom ≫ Spec.map (CommRingCat.ofHom σ))
include hf

/-- Constants commute with an actual structural field-change square. -/
theorem map_constants_of_baseMap (a : F) :
    f.appTop (constants Y a) = constants X (σ a) := by
  change (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ Y.hom.appTop) ≫ f.appTop).hom a =
    ((CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv) ≫ X.hom.appTop).hom a
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, hf, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]

theorem app_constantSection_of_baseMap (U : Y.left.Opens) (a : F) :
    f.app U (constantSection Y U a) = constantSection X (f ⁻¹ᵁ U) (σ a) := by
  have hn := congrArg
    (fun q : Γ(Y.left, ⊤) ⟶ Γ(X.left, f ⁻¹ᵁ U) ↦ q.hom (constants Y a))
    (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change f.app U (constantSection Y U a) =
    X.left.presheaf.map _ (f.appTop (constants Y a)) at hn
  rw [map_constants_of_baseMap σ X Y f hf] at hn
  exact hn

theorem structurePushforward_scalar_of_baseMap (a : F) :
    structureScalar Y a ≫ structurePushforwardMap f =
      structurePushforwardMap f ≫ (zariskiPushforward f).map (structureScalar X (σ a)) := by
  ext U x
  change Γ(Y.left, U.unop) at x
  change f.app U.unop (constantSection Y U.unop a * x) =
    constantSection X (f ⁻¹ᵁ U.unop) (σ a) * f.app U.unop x
  rw [map_mul, app_constantSection_of_baseMap σ X Y f hf]

theorem structurePullback_scalar_of_baseMap (a : F) :
    (zariskiPullback f).map (structureScalar Y a) ≫ structurePullbackMap f =
      structurePullbackMap f ≫ structureScalar X (σ a) := by
  have hn := congrArg
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _).symm)
      (structurePushforward_scalar_of_baseMap σ X Y f hf a)
  dsimp only [zariskiPushforward] at hn
  rw [Adjunction.homEquiv_naturality_right_symm] at hn
  simpa only [Adjunction.homEquiv_naturality_left_symm, structurePullbackMap, zariskiPullback]
    using hn

/-- Semilinear cohomology pullback constructed from the actual field-change square. -/
def structureCohomologyPullbackSemilinear (n : ℕ) :
    structureCohomology F Y n →ₛₗ[σ] structureCohomology K X n where
  __ := structureCohomologyPullback f n
  map_smul' a x :=
    zariskiCohomologyMap_naturality f _ _ (structurePullbackMap f)
      (structureScalar Y a) (structureScalar X (σ a))
      (structurePullback_scalar_of_baseMap σ X Y f hf a) n x
end AlgebraicGeometry.Scheme.Cohomology

