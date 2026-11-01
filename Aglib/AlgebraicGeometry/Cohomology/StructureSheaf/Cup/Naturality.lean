/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Graded
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Pullback
public import Mathlib.RingTheory.GradedAlgebra.AlgHom

/-!
# Flat geometric pullback preserves the original coherent cup product

The existing exact module-pullback comparison is normalized by its actual
unit-module isomorphism. Conjugating the original exact-functor Ext map by
that isomorphism preserves Yoneda composition. Thus the original geometric
cohomology maps preserve the already constructed cup product and assemble
into an algebra homomorphism of the same native direct sums.

Flatness is retained precisely for exact module pullback. This theorem is
not applied to an arbitrary unit section; its unit/H0 normalization uses
the separate unrestricted theorem in `Cup`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open TopologicalSpace
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem directSumToAlgebra_lof {R : Type*} [CommRing R]
    (M : ℕ → Type*) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    [DirectSum.GRing M] [DirectSum.GAlgebra R M]
    {B : Type*} [Ring B] [Algebra R B]
    (g : ∀ n, M n →ₗ[R] B) (h1 : g 0 GradedMonoid.GOne.one = 1)
    (hm : ∀ {i j} (x : M i) (y : M j),
      g (i + j) (GradedMonoid.GMul.mul x y) = g i x * g j y)
    (n : ℕ) (x : M n) :
    DirectSum.toAlgebra R M g h1 hm (DirectSum.lof R ℕ M n x) = g n x := by
  change DirectSum.toAlgebra R M g h1 hm (DirectSum.of M n x) = _
  rw [DirectSum.toAlgebra_apply, DirectSum.toSemiring_of]
  rfl

/-- Postcomposing the original coefficient arrow gives the original
map on cohomology, for every geometric morphism and all additive sheaves. -/
theorem zariskiCohomologyMap_postcomp {U V : Scheme.{u}} (p : U ⟶ V)
    (A : Sheaf (Opens.grothendieckTopology V) AddCommGrpCat.{u})
    (B C : Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B) (b : B ⟶ C) (n : ℕ)
    (x : Sheaf.H.{u + 1} A n) :
    zariskiCohomologyMap p A C (a ≫ b) n x =
      Sheaf.H.map b n (zariskiCohomologyMap p A B a n x) := by
  have hs : (zariskiPullback p).map (𝟙 A) ≫ (a ≫ b) = a ≫ b :=
    (congrArg (fun t => t ≫ (a ≫ b)) ((zariskiPullback p).map_id A)).trans
      (Category.id_comp _)
  have h := zariskiCohomologyMap_map p a (a ≫ b) (𝟙 A) b hs n x
  exact (congrArg (zariskiCohomologyMap p A C (a ≫ b) n)
    (Sheaf.H.map_id_apply x)).symm.trans h

/-- The whole original structure-module Ext comparison commutes with
flat geometric pullback, with its original unit isomorphism. -/
theorem moduleUnitExtCohomologyMap_pullback {U V : Scheme.{u}} (p : U ⟶ V) [Flat p]
    (n : ℕ)
    (x : Ext.{u + 1} (C := V.Modules) (SheafOfModules.unit V.ringCatSheaf)
      (SheafOfModules.unit V.ringCatSheaf) n) :
    structureCohomologyPullback p n
        (moduleExtCohomologyMap V (SheafOfModules.unit V.ringCatSheaf) n x) =
      moduleExtCohomologyMap U (SheafOfModules.unit U.ringCatSheaf) n
        (((Ext.mk₀ (Scheme.Modules.pullbackUnitIso p).inv).comp
          (x.mapExactFunctor (Scheme.Modules.pullback p)) (Nat.zero_add n)).comp
            (Ext.mk₀ (Scheme.Modules.pullbackUnitIso p).hom) (Nat.add_zero n)) := by
  have hnorm := congrArg
    (fun t => zariskiCohomologyMap p (structureAddSheaf V) (structureAddSheaf U) t n
      (moduleExtCohomologyMap V (SheafOfModules.unit V.ringCatSheaf) n x))
    (modulePullbackAdditiveComparison_unit p)
  have hcomp := zariskiCohomologyMap_postcomp p _ _ _
    ((modulePullbackAdditiveComparison p).app (SheafOfModules.unit V.ringCatSheaf))
    ((SheafOfModules.toSheaf.{u} U.ringCatSheaf).map
      (Scheme.Modules.pullbackUnitIso p).hom) n
    (moduleExtCohomologyMap V (SheafOfModules.unit V.ringCatSheaf) n x)
  have hbase := moduleExtCohomologyMap_pullback p
    (SheafOfModules.unit V.ringCatSheaf) n x
  have hpost := moduleExtCohomologyMap_naturality U
    (Scheme.Modules.pullbackUnitIso p).hom n
    ((Ext.mk₀ (Scheme.Modules.pullbackUnitIso p).inv).comp
      (x.mapExactFunctor (Scheme.Modules.pullback p)) (Nat.zero_add n))
  exact hnorm.symm.trans (hcomp.trans ((congrArg
    (Sheaf.H.map ((SheafOfModules.toSheaf.{u} U.ringCatSheaf).map
      (Scheme.Modules.pullbackUnitIso p).hom) n) hbase).trans hpost.symm))

variable {k : Type u} [Field k] {X Y : FScheme k} (f : X ⟶ Y) [Flat f.left]

/-- The field-linear specialization retains the same original
geometric map, Ext comparison, and unit-module isomorphism. -/
theorem structureExtLinearEquiv_pullback_of_flat (n : ℕ)
    (x : Ext.{u + 1} (C := Y.left.Modules) (SheafOfModules.unit Y.left.ringCatSheaf)
      (SheafOfModules.unit Y.left.ringCatSheaf) n) :
    let e := Scheme.Modules.pullbackUnitIso f.left
    structureCohomologyPullbackLinear f n (structureExtLinearEquiv Y n x) =
      structureExtLinearEquiv X n
        (((Ext.mk₀ e.inv).comp (x.mapExactFunctor (Scheme.Modules.pullback f.left))
          (Nat.zero_add n)).comp (Ext.mk₀ e.hom) (Nat.add_zero n)) :=
  moduleUnitExtCohomologyMap_pullback f.left n x

/-- Flat geometric pullback preserves the original Yoneda cup product,
with the actual original cohomology map on each degree. -/
theorem structureCup_pullback_of_flat {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k Y p) (y : structureCohomology k Y q) :
    structureCohomologyPullbackLinear f n (structureCup Y h x y) =
      structureCup X h (structureCohomologyPullbackLinear f p x)
        (structureCohomologyPullbackLinear f q y) := by
  obtain ⟨α, rfl⟩ := (structureExtLinearEquiv Y p).surjective x
  obtain ⟨β, rfl⟩ := (structureExtLinearEquiv Y q).surjective y
  apply (structureExtLinearEquiv X n).symm.injective
  simp only [structureCup_apply, LinearEquiv.symm_apply_apply,
    structureExtLinearEquiv_pullback_of_flat, Ext.mapExactFunctor_comp]
  let e := Scheme.Modules.pullbackUnitIso f.left
  let a := α.mapExactFunctor (Scheme.Modules.pullback f.left)
  let b := β.mapExactFunctor (Scheme.Modules.pullback f.left)
  have hcancel : (Ext.mk₀ e.hom).comp
      (((Ext.mk₀ e.inv).comp b (Nat.zero_add q)).comp (Ext.mk₀ e.hom) (Nat.add_zero q))
        (Nat.zero_add q) = b.comp (Ext.mk₀ e.hom) (Nat.add_zero q) := by
    rw [← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.mk₀_id_comp]
  change ((Ext.mk₀ e.inv).comp (a.comp b h) (Nat.zero_add n)).comp (Ext.mk₀ e.hom)
      (Nat.add_zero n) =
    (((Ext.mk₀ e.inv).comp a (Nat.zero_add p)).comp (Ext.mk₀ e.hom) (Nat.add_zero p)).comp
      (((Ext.mk₀ e.inv).comp b (Nat.zero_add q)).comp (Ext.mk₀ e.hom) (Nat.add_zero q)) h
  symm
  rw [Ext.comp_assoc_of_second_deg_zero, hcancel, ← Ext.comp_assoc_of_third_deg_zero]
  exact congrArg (fun z : Ext.{u + 1} (C := X.left.Modules)
      (SheafOfModules.unit X.left.ringCatSheaf)
      ((Scheme.Modules.pullback f.left).obj (SheafOfModules.unit Y.left.ringCatSheaf)) n =>
      z.comp (Ext.mk₀ e.hom) (Nat.add_zero n))
    (Ext.comp_assoc (Ext.mk₀ e.inv) a b (Nat.zero_add p) h (by omega))

omit [Flat f.left] in
/-- The original degreewise geometric pullbacks, assembled by the
native direct-sum linear map. -/
def structureCohomologyAlgebraPullbackLinear :
    structureCohomologyAlgebra Y →ₗ[k] structureCohomologyAlgebra X :=
  DirectSum.lmap (fun n => structureCohomologyPullbackLinear f n)

omit [Flat f.left] in
@[simp]
theorem structureCohomologyAlgebraPullbackLinear_inclusion (n : ℕ)
    (x : structureCohomology k Y n) :
    structureCohomologyAlgebraPullbackLinear f (structureCohomologyInclusion Y n x) =
      structureCohomologyInclusion X n (structureCohomologyPullbackLinear f n x) :=
  DirectSum.lmap_lof _ _ _

omit [Flat f.left] in
/-- The original homogeneous components of the geometric pullback. -/
def structureCohomologyPullbackFamily (n : ℕ) :
    structureCohomology k Y n →ₗ[k] structureCohomologyAlgebra X :=
  structureCohomologyInclusion X n ∘ₗ structureCohomologyPullbackLinear f n

omit [Flat f.left] in
@[simp]
theorem structureCohomologyPullbackFamily_apply (n : ℕ)
    (x : structureCohomology k Y n) :
    structureCohomologyPullbackFamily f n x =
      structureCohomologyInclusion X n (structureCohomologyPullbackLinear f n x) := rfl

omit [Flat f.left] in
/-- The original homogeneous pullback family preserves the original unit. -/
theorem structureCohomologyPullbackFamily_one :
    structureCohomologyPullbackFamily f 0 GradedMonoid.GOne.one = 1 := by
  change structureCohomologyInclusion X 0
    (structureCohomologyPullbackLinear f 0 (structureCupUnit Y)) = 1
  rw [structureCohomologyPullbackLinear_cupUnit]
  rfl

/-- The original homogeneous pullback family preserves original cup
multiplication under its actual flatness hypothesis. -/
theorem structureCohomologyPullbackFamily_mul {p q : ℕ}
    (x : structureCohomology k Y p) (y : structureCohomology k Y q) :
    structureCohomologyPullbackFamily f (p + q) (GradedMonoid.GMul.mul x y) =
      structureCohomologyPullbackFamily f p x * structureCohomologyPullbackFamily f q y := by
  change structureCohomologyInclusion X (p + q)
      (structureCohomologyPullbackLinear f (p + q)
        (structureCup Y (p := p) (q := q) rfl x y)) = _
  rw [structureCup_pullback_of_flat]
  exact (structureCohomologyInclusion_mul X _ _).symm

/-- The original geometric pullback is an algebra homomorphism of the
native coherent-cohomology direct sums for a flat morphism. -/
def structureCohomologyAlgebraPullback :
    structureCohomologyAlgebra Y →ₐ[k] structureCohomologyAlgebra X :=
  DirectSum.toAlgebra k (structureCohomology k Y) (structureCohomologyPullbackFamily f)
    (structureCohomologyPullbackFamily_one f)
    (fun {p q} x y => structureCohomologyPullbackFamily_mul f (p := p) (q := q) x y)

@[simp]
theorem structureCohomologyAlgebraPullback_inclusion (n : ℕ)
    (x : structureCohomology k Y n) :
    structureCohomologyAlgebraPullback f (structureCohomologyInclusion Y n x) =
      structureCohomologyInclusion X n (structureCohomologyPullbackLinear f n x) :=
  directSumToAlgebra_lof (structureCohomology k Y) (structureCohomologyPullbackFamily f)
    (structureCohomologyPullbackFamily_one f)
    (fun {p q} x y => structureCohomologyPullbackFamily_mul f (p := p) (q := q) x y) n x

/-- The algebra homomorphism has exactly the original direct-sum map
as its underlying linear map. -/
theorem structureCohomologyAlgebraPullback_toLinearMap :
    (structureCohomologyAlgebraPullback f).toLinearMap =
      structureCohomologyAlgebraPullbackLinear f := by
  apply DirectSum.linearMap_ext k
  intro n
  apply LinearMap.ext
  intro x
  change structureCohomologyAlgebraPullback f (structureCohomologyInclusion Y n x) =
    structureCohomologyAlgebraPullbackLinear f (structureCohomologyInclusion Y n x)
  rw [structureCohomologyAlgebraPullback_inclusion,
    structureCohomologyAlgebraPullbackLinear_inclusion]

/-- The same original pullback algebra map preserves the actual
homogeneous submodules, so it is a native graded algebra homomorphism. -/
def structureCohomologyGradedPullback :
    structureCohomologyGrade Y →ₐᵍ[k] structureCohomologyGrade X :=
  ⟨structureCohomologyAlgebraPullback f, by
    intro n x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨structureCohomologyPullbackLinear f n a,
      (structureCohomologyAlgebraPullback_inclusion f n a).symm⟩⟩

@[simp]
theorem structureCohomologyGradedPullback_toAlgHom :
    (structureCohomologyGradedPullback f).toAlgHom =
      structureCohomologyAlgebraPullback f := rfl

end AlgebraicGeometry.Scheme.Cohomology
