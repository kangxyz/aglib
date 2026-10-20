/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Fibres
public import Aglib.AlgebraicGeometry.FunctionField.BaseChange
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.FunctionField` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`61817d2cdc80b7f9b5aa7a6d525d70bb5d208aaf3f88c5c47bacf1b8aff8a9c8`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules
  (AffineModuleBaseChange  moduleFibre moduleFibre_finite
    moduleFibre_finrank_eq_sheafRank pushforwardStructureSheaf)

open _root_.AlgebraicGeometry.Scheme.Modules
  (IsFiniteLocallyFree isFiniteLocallyFree_iff_exists_localBasis)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Actual function-field degree of finite locally free morphisms

The canonical generic-fibre map is built from C's actual generic-point stalk
map and its proved naturality square. `FiniteDominantGenericFibre` retains the
general assertion that this map is an isomorphism for finite dominant maps
between integral schemes, with no curve or genus condition. It is a derived
corollary of Stacks 02NX and 054Z, not either literal statement: the generic
fibre is reduced and supported at the generic point, hence its finite algebra
is the actual function field. The corrected affine-localization proof and
2019 correction in 054Z were inspected 2026-10-09.

The induced field-linear equivalence, finite dimensionality, and equality with
the actual locally free rank are constructed/proved below.
Application K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982; engineering7f86e4a with frozen pins.
Incoming C source hashes: FunctionField
b3e77cd8ddf5ae3a1a0dce63dd7a7387b17dc3e609fd4d3920893303d70a9ba7;
BaseChange 1edd31d57df6f885709926ffabdd23f416664f5bee3998a90080e054c715d2e5.
-/
/-!
Provenance: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`; frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Mathematical-source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Hom.FiniteFlat
open AlgebraicGeometry.Scheme
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f]

/-- The generic fibre of the dominant morphism `f`, viewed over the target function field. -/
abbrev genericFibreScheme : Over (Spec Y.functionField) :=
  Over.mk (pullback.snd f ((Y.fromSpecStalk (genericPoint Y))))

attribute [local instance] coordinateAlgebra

/-- Evaluation of generic-fibre global sections in the source function field,
as an algebra map over the target function field. -/
def genericFibreCoordinates :
    letI := Scheme.functionFieldMapAlgebra f
    letI := coordinateAlgebra Y.functionField (genericFibreScheme f)
    Γ((genericFibreScheme f).left, ⊤) →ₐ[Y.functionField] X.functionField := by
  letI := Scheme.functionFieldMapAlgebra f
  letI := coordinateAlgebra Y.functionField (genericFibreScheme f)
  refine {
    toRingHom := ((genericFibreMap f).appTop ≫ (Scheme.ΓSpecIso X.functionField).hom).hom
    commutes' := ?_ }
  intro a
  have he : (Scheme.ΓSpecIso Y.functionField).inv ≫
      (genericFibreScheme f).hom.appTop ≫
      (genericFibreMap f).appTop ≫ (Scheme.ΓSpecIso X.functionField).hom =
      CommRingCat.ofHom (Scheme.functionFieldMap f) := by
    rw [← Category.assoc (genericFibreScheme f).hom.appTop,
      ← Scheme.Hom.comp_appTop]
    change (Scheme.ΓSpecIso Y.functionField).inv ≫
      (genericFibreMap f ≫ pullback.snd f ((Y.fromSpecStalk (genericPoint Y)))).appTop ≫ _ = _
    rw [genericFibreMap, pullback.lift_snd, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun q : Y.functionField ⟶ X.functionField ↦ q.hom a) he

/-- The theorem-family input identifying the generic fibre of a finite dominant morphism
of integral schemes with the spectrum of its source function field. -/
def FiniteDominantGenericFibre : Prop :=
  ∀ (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f], IsFinite f → IsIso (genericFibreMap f)

/-- The canonical finite-dominant generic-fibre theorem supplies the original family. -/
theorem finiteDominantGenericFibre : FiniteDominantGenericFibre.{u} := by
  intro X Y _ _ f _ hf
  letI := hf
  exact Scheme.genericFibreMap_isIso f

/-- The generic-fibre coordinate-algebra equivalence for a finite dominant morphism,
using the supplied generic-fibre input. -/
def genericFibreCoordinatesEquiv (hgen : FiniteDominantGenericFibre.{u}) [IsFinite f] :
    letI := Scheme.functionFieldMapAlgebra f
    letI := coordinateAlgebra Y.functionField (genericFibreScheme f)
    Γ((genericFibreScheme f).left, ⊤) ≃ₐ[Y.functionField] X.functionField := by
  letI := Scheme.functionFieldMapAlgebra f
  letI := coordinateAlgebra Y.functionField (genericFibreScheme f)
  letI := hgen X Y f inferInstance
  apply AlgEquiv.ofBijective (genericFibreCoordinates f)
  exact ConcreteCategory.bijective_of_isIso
    ((genericFibreMap f).appTop ≫ (Scheme.ΓSpecIso X.functionField).hom)
end AlgebraicGeometry.Scheme.Hom.FiniteFlat

namespace AlgebraicGeometry.Scheme.Hom.FiniteFlat
open AlgebraicGeometry.Scheme
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f]

/-- The generic fibre of the pushed-forward structure module as the source function field,
using the supplied affine module base-change and finite-dominant generic-fibre inputs. -/
def moduleFibreFunctionFieldEquiv
    (hbase : AffineModuleBaseChange.{u}) (hgen : FiniteDominantGenericFibre.{u}) [IsFinite f] :
    letI := Scheme.functionFieldMapAlgebra f
    moduleFibre Y.functionField (pushforwardStructureSheaf f) ((Y.fromSpecStalk (genericPoint
        Y))) ≃ₗ[Y.functionField]
      X.functionField := by
  letI := Scheme.functionFieldMapAlgebra f
  letI : Algebra Y.functionField Γ(pullback f ((Y.fromSpecStalk (genericPoint Y))), ⊤) :=
    coordinateAlgebra Y.functionField (genericFibreScheme f)
  letI : Algebra Y.functionField Γ((genericFibreScheme f).left, ⊤) :=
    coordinateAlgebra Y.functionField (genericFibreScheme f)
  exact (moduleFibreStructureEquiv Y.functionField f hbase ((Y.fromSpecStalk (genericPoint
      Y)))).trans
    (genericFibreCoordinatesEquiv f hgen).toLinearEquiv

/-- The degree of the independently constructed actual function-field embedding. -/
def functionFieldDegree : ℕ :=
  letI := Scheme.functionFieldMapAlgebra f
  Module.finrank Y.functionField X.functionField

theorem functionField_finite
    (hbase : AffineModuleBaseChange.{u})
    (hgen : FiniteDominantGenericFibre.{u}) [IsFinite f] (hf : FiniteLocallyFree f) :
    letI := Scheme.functionFieldMapAlgebra f
    Module.Finite Y.functionField X.functionField := by
  letI : IsFiniteLocallyFree _ (pushforwardStructureSheaf f) :=
    (isFiniteLocallyFree_iff_exists_localBasis _).mpr hf.2
  letI := Scheme.functionFieldMapAlgebra f
  let e := moduleFibreFunctionFieldEquiv f hbase hgen
  letI := moduleFibre_finite (pushforwardStructureSheaf f) Y.functionField ((Y.fromSpecStalk
      (genericPoint Y)))
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

theorem functionFieldDegree_eq_rank_generic
    (hbase : AffineModuleBaseChange.{u})
    (hgen : FiniteDominantGenericFibre.{u}) [IsFinite f] (hf : FiniteLocallyFree f) :
    functionFieldDegree f = locallyFreeRank f (genericPoint Y) := by
  letI : IsFiniteLocallyFree _ (pushforwardStructureSheaf f) :=
    (isFiniteLocallyFree_iff_exists_localBasis _).mpr hf.2
  letI := Scheme.functionFieldMapAlgebra f
  have hp : ((Y.fromSpecStalk (genericPoint Y))) (default : Spec (CommRingCat.of
      Y.functionField)) = genericPoint Y := by
    exact (congrArg ((Y.fromSpecStalk (genericPoint Y)))
      (Subsingleton.elim (default : Spec (CommRingCat.of Y.functionField))
        (IsLocalRing.closedPoint Y.functionField))).trans
        (Y.fromSpecStalk_closedPoint)
  exact (moduleFibreFunctionFieldEquiv f hbase hgen).finrank_eq.symm.trans
    ((moduleFibre_finrank_eq_sheafRank (pushforwardStructureSheaf f) Y.functionField
        ((Y.fromSpecStalk (genericPoint Y)))).trans
      (congrArg (locallyFreeRank f) hp))

theorem functionFieldDegree_eq_of_hasLocallyFreeRank
    (hbase : AffineModuleBaseChange.{u})
    (hgen : FiniteDominantGenericFibre.{u}) [IsFinite f] (n : ℕ) (hf : HasLocallyFreeRank f n) :
    functionFieldDegree f = n :=
  (functionFieldDegree_eq_rank_generic f hbase hgen hf.finiteLocallyFree).trans
    ((hasLocallyFreeRank_iff_rank_eq f hf.finiteLocallyFree n).mp hf _)
end AlgebraicGeometry.Scheme.Hom.FiniteFlat
