/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Subobjects.Gluing
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsGlobal

/-!
# Gluing quasicoherent subobjects

The paired-obstruction kernel glues compatible quasicoherent subobjects along quasi-compact
open immersions inside a quasicoherent ambient sheaf. The immersions need not form a cover.
The locally Noetherian specialization delegates to the general construction.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/GluingQuasicoherent.lean`.
SHA-256: `2b804ce3706bf3bc9e71c88f3ac8316a3da0f6c29057e424dee7a07c1468257f`.
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
namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Compatible quasicoherent subobjects glue to a global quasicoherent
subobject. The quasi-compact open immersions need not cover the target.
No Noetherian hypothesis or finite-type hypothesis on the sheaves is needed. -/
theorem exists_quasicoherent_glued_subobject_of_quasiCompact
    {U V X : Scheme.{u}}
    (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a]
    [QuasiCompact j] [QuasiCompact a]
    {M : X.Modules} {A : U.Modules} {B : V.Modules}
    [M.IsQuasicoherent] [A.IsQuasicoherent] [B.IsQuasicoherent]
    (i : A ⟶ M.restrict j) (k : B ⟶ M.restrict a) [Mono i] [Mono k]
    (e : A.restrict (pullback.fst j a) ≅ B.restrict (pullback.snd j a))
    (he : (restrictFunctor (pullback.fst j a)).map i ≫
        (overlapRestrictIso j a).hom.app M =
      e.hom ≫ (restrictFunctor (pullback.snd j a)).map k) :
    ∃ (N : X.Modules) (s : N ⟶ M), N.IsQuasicoherent ∧ Mono s ∧
      ∃ (eU : N.restrict j ≅ A) (eV : N.restrict a ≅ B),
        (restrictFunctor j).map s = eU.hom ≫ i ∧
        (restrictFunctor a).map s = eV.hom ≫ k := by
  let f := subobjectObstruction j i
  let g := subobjectObstruction a k
  let l := prod.lift f g
  have : (cokernel i).IsQuasicoherent := quasicoherent_cokernel i
  have : (cokernel k).IsQuasicoherent := quasicoherent_cokernel k
  have : ((pushforward j).obj (cokernel i)).IsQuasicoherent :=
    quasicoherent_pushforward_open j (cokernel i)
  have : ((pushforward a).obj (cokernel k)).IsQuasicoherent :=
    quasicoherent_pushforward_open a (cokernel k)
  have : (((pushforward j).obj (cokernel i)) ⨯
      ((pushforward a).obj (cokernel k))).IsQuasicoherent := (by
      apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit
        (prodIsProd _ _)
      rintro (_ | _) <;> assumption)
  have hN : (kernel l).IsQuasicoherent := quasicoherent_kernel l
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
  refine ⟨kernel l, kernel.ι l, hN, inferInstance, eU, eV, ?_, ?_⟩
  · exact (hU₀.conePointUniqueUpToIso_hom_comp hUl WalkingParallelPair.zero).symm
  · exact (hV₀.conePointUniqueUpToIso_hom_comp hVl WalkingParallelPair.zero).symm


/-- Compatible quasicoherent subobjects glue to a global quasicoherent
subobject. The open immersions need not cover the target. Local noetherianity
is used only for quasicoherence of the actual direct images. -/
theorem exists_quasicoherent_glued_subobject
    {U V X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a]
    {M : X.Modules} {A : U.Modules} {B : V.Modules}
    [M.IsQuasicoherent] [A.IsQuasicoherent] [B.IsQuasicoherent]
    (i : A ⟶ M.restrict j) (k : B ⟶ M.restrict a) [Mono i] [Mono k]
    (e : A.restrict (pullback.fst j a) ≅ B.restrict (pullback.snd j a))
    (he : (restrictFunctor (pullback.fst j a)).map i ≫
        (overlapRestrictIso j a).hom.app M =
      e.hom ≫ (restrictFunctor (pullback.snd j a)).map k) :
    ∃ (N : X.Modules) (s : N ⟶ M), N.IsQuasicoherent ∧ Mono s ∧
      ∃ (eU : N.restrict j ≅ A) (eV : N.restrict a ≅ B),
        (restrictFunctor j).map s = eU.hom ≫ i ∧
        (restrictFunctor a).map s = eV.hom ≫ k := by
  exact exists_quasicoherent_glued_subobject_of_quasiCompact j a i k e he

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
