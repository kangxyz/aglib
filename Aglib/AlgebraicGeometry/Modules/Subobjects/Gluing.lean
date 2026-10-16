/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap
public import Aglib.AlgebraicGeometry.Modules.Restriction.ZeroMorphisms
public import Aglib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Gluing module subobjects on two opens

A cokernel map and the restriction/direct-image adjunction define the obstruction to extending a
subobject. Compatible monomorphisms on two opens glue by the kernel of their paired
obstructions. The two opens need not cover the scheme.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/GluingSubobjects.lean`.
SHA-256: `d6329afc8058687c07b626f0cf1a82a708d6ed99bcdda9d8fc260402bd0c28a9`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules

/-- The global map whose kernel extends a given open subobject. -/
def subobjectObstruction
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} {A : U.Modules} (i : A ⟶ M.restrict j) :
    M ⟶ (pushforward j).obj (cokernel i) :=
  (restrictAdjunction j).homEquiv M (cokernel i) (cokernel.π i)

/-- Restricting the obstruction and applying its counit gives the original cokernel map. -/
@[reassoc (attr := simp)]
lemma subobjectObstruction_counit
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} {A : U.Modules} (i : A ⟶ M.restrict j) :
    (restrictFunctor j).map (subobjectObstruction j i) ≫
        (restrictAdjunction j).counit.app (cokernel i) = cokernel.π i := by
  simpa only [subobjectObstruction, Adjunction.homEquiv_counit] using
    ((restrictAdjunction j).homEquiv M (cokernel i)).symm_apply_apply (cokernel.π i)

/-- The original open subobject kills its restricted obstruction map. -/
@[reassoc (attr := simp)]
lemma subobjectObstruction_local_zero
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} {A : U.Modules} (i : A ⟶ M.restrict j) :
    i ≫ (restrictFunctor j).map (subobjectObstruction j i) = 0 := by
  apply (cancel_mono ((restrictAdjunction j).counit.app (cokernel i))).mp
  simp

/-- The given local subobject is the kernel of its restricted global
obstruction map. -/
def subobjectObstructionKernelIsLimit
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} {A : U.Modules} (i : A ⟶ M.restrict j) [Mono i] :
    IsLimit (KernelFork.ofι i (subobjectObstruction_local_zero j i)) := by
  let h := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  exact KernelFork.IsLimit.lift' h k (by
    change k ≫ cokernel.π i = 0
    rw [← subobjectObstruction_counit j i, ← Category.assoc, hk]
    simp)

/-- Matching overlap subobjects kill each other's global obstruction maps.
This is the geometric compatibility needed by the paired-kernel construction. -/
theorem overlapCompatible_obstruction_zero
    {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a]
    {M : X.Modules} {A : U.Modules} {B : V.Modules}
    (i : A ⟶ M.restrict j) (k : B ⟶ M.restrict a)
    (e : A.restrict (pullback.fst j a) ≅ B.restrict (pullback.snd j a))
    (he : (restrictFunctor (pullback.fst j a)).map i ≫
        (overlapRestrictIso j a).hom.app M =
      e.hom ≫ (restrictFunctor (pullback.snd j a)).map k) :
    (i ≫ (restrictFunctor j).map (subobjectObstruction a k) = 0) ∧
      (k ≫ (restrictFunctor a).map (subobjectObstruction j i) = 0) := by
  let p := pullback.fst j a
  let q := pullback.snd j a
  let E := overlapRestrictIso j a
  constructor
  · apply eq_zero_of_restrict_map_eq_zero p _
      ⟨(cokernel k).restrict q, ⟨((Scheme.Modules.cartesianOpenBaseChange (pullback.snd j a)
        (pullback.fst j a) a j (IsPullback.of_hasPullback j a).flip)).app (cokernel k)⟩⟩
    apply (cancel_mono (E.hom.app ((pushforward a).obj (cokernel k)))).mp
    change ((restrictFunctor p).map i ≫
        (restrictFunctor j ⋙ restrictFunctor p).map (subobjectObstruction a k)) ≫ _ = 0 ≫ _
    rw [Category.assoc, E.hom.naturality, ← Category.assoc, he]
    simp only [p, Category.assoc, Functor.comp_map, ← Functor.map_comp,
      subobjectObstruction_local_zero, Functor.map_zero, comp_zero, zero_comp]
  · have he' : (restrictFunctor q).map k ≫ E.inv.app M =
        e.inv ≫ (restrictFunctor p).map i := by
      apply (cancel_mono (E.hom.app M)).mp
      simp only [Category.assoc, Iso.inv_hom_id_app]
      rw [he, Iso.inv_hom_id_assoc]
      simp [q]
    apply eq_zero_of_restrict_map_eq_zero q _
      ⟨(cokernel i).restrict p, ⟨(openBaseChange j a).app (cokernel i)⟩⟩
    apply (cancel_mono (E.inv.app ((pushforward j).obj (cokernel i)))).mp
    change ((restrictFunctor q).map k ≫
        (restrictFunctor a ⋙ restrictFunctor q).map (subobjectObstruction j i)) ≫ _ = 0 ≫ _
    rw [Category.assoc, E.inv.naturality, ← Category.assoc, he']
    simp only [p, q, Category.assoc, Functor.comp_map, ← Functor.map_comp,
      subobjectObstruction_local_zero, Functor.map_zero, comp_zero, zero_comp]

/-- The actual glued subobject, with comparison isomorphisms commuting
with the two given inclusions. This assertion is valid for arbitrary module
sheaves; coherence follows separately from locality on a covering pair. -/
theorem exists_glued_subobject
    {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a]
    {M : X.Modules} {A : U.Modules} {B : V.Modules}
    (i : A ⟶ M.restrict j) (k : B ⟶ M.restrict a) [Mono i] [Mono k]
    (e : A.restrict (pullback.fst j a) ≅ B.restrict (pullback.snd j a))
    (he : (restrictFunctor (pullback.fst j a)).map i ≫
        (overlapRestrictIso j a).hom.app M =
      e.hom ≫ (restrictFunctor (pullback.snd j a)).map k) :
    ∃ (N : X.Modules) (s : N ⟶ M), Mono s ∧
      ∃ (eU : N.restrict j ≅ A) (eV : N.restrict a ≅ B),
        (restrictFunctor j).map s = eU.hom ≫ i ∧
        (restrictFunctor a).map s = eV.hom ≫ k := by
  let f := subobjectObstruction j i
  let g := subobjectObstruction a k
  let l := prod.lift f g
  obtain ⟨hij, hka⟩ := overlapCompatible_obstruction_zero j a i k e he
  have hU : i ≫ (restrictFunctor j).map l = 0 :=
    map_prod_lift_comp_eq_zero (restrictFunctor j) i f g
      (subobjectObstruction_local_zero j i) hij
  have hV : k ≫ (restrictFunctor a).map l = 0 :=
    map_prod_lift_comp_eq_zero (restrictFunctor a) k f g
      hka (subobjectObstruction_local_zero a k)
  let hUl := isKernelOfComp ((restrictFunctor j).map prod.fst)
    ((restrictFunctor j).map f) (subobjectObstructionKernelIsLimit j i) hU
    (by rw [← Functor.map_comp, prod.lift_fst])
  let hVl := isKernelOfComp ((restrictFunctor a).map prod.snd)
    ((restrictFunctor a).map g) (subobjectObstructionKernelIsLimit a k) hV
    (by rw [← Functor.map_comp, prod.lift_snd])
  let hU₀ := KernelFork.mapIsLimit _ (kernelIsKernel l) (restrictFunctor j)
  let hV₀ := KernelFork.mapIsLimit _ (kernelIsKernel l) (restrictFunctor a)
  let eU := hU₀.conePointUniqueUpToIso hUl
  let eV := hV₀.conePointUniqueUpToIso hVl
  refine ⟨kernel l, kernel.ι l, inferInstance, eU, eV, ?_, ?_⟩
  · exact (hU₀.conePointUniqueUpToIso_hom_comp hUl WalkingParallelPair.zero).symm
  · exact (hV₀.conePointUniqueUpToIso_hom_comp hVl WalkingParallelPair.zero).symm

end AlgebraicGeometry.Scheme.Modules
