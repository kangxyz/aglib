/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsGlobal

/-!
# Quasicoherent preimages of open subobjects

For a quasi-compact open immersion, a quasicoherent subobject of the restriction of a
quasicoherent sheaf extends as a quasicoherent subobject, with its original inclusion map.
The locally Noetherian finite-type specialization delegates to this general construction.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/SubobjectPreimage.lean`.
SHA-256: `b3c30a165e1b384f1c2d63f99fd3d62f1cff52d17cd9e35f332843bf829f5724`.
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

/-- The actual quasicoherent preimage kernel of an open subsheaf.
Quasi-compactness replaces Noetherianity; neither module need be finite type. -/
theorem quasicoherent_subobject_preimage_of_quasiCompact
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (M : X.Modules) [M.IsQuasicoherent]
    (A : U.Modules) [A.IsQuasicoherent] (i : A ⟶ M.restrict j) [Mono i] :
    ∃ (K : X.Modules) (s : K ⟶ M), K.IsQuasicoherent ∧ Mono s ∧
      ∃ (e : K.restrict j ≅ A),
        (Scheme.Modules.restrictFunctor j).map s = e.hom ≫ i := by
  let F := Scheme.Modules.restrictFunctor j
  let adj := Scheme.Modules.restrictAdjunction j
  let C := cokernel i
  have : C.IsQuasicoherent := quasicoherent_cokernel i
  have : ((Scheme.Modules.pushforward j).obj C).IsQuasicoherent :=
    quasicoherent_pushforward_open j C
  let k : M ⟶ (Scheme.Modules.pushforward j).obj C := adj.homEquiv M C (cokernel.π i)
  have hk : F.map k ≫ adj.counit.app C = cokernel.π i := by
    simpa only [Adjunction.homEquiv_counit] using
      (adj.homEquiv M C).symm_apply_apply (cokernel.π i)
  let h₁ := isKernelCompMono
    (KernelFork.mapIsLimit _ (kernelIsKernel k) F) (adj.counit.app C) hk.symm
  let h₂ := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)
  refine ⟨kernel k, kernel.ι k, quasicoherent_kernel k, inferInstance,
    h₁.conePointUniqueUpToIso h₂, ?_⟩
  exact (h₁.conePointUniqueUpToIso_hom_comp h₂ WalkingParallelPair.zero).symm


/-- The quasicoherent preimage kernel of an actual coherent open subsheaf.
No finite generation of the ambient module sheaf is assumed. -/
theorem quasicoherent_subobject_preimage
    {U X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (M : X.Modules) [M.IsQuasicoherent]
    (A : FiniteTypeSheaves U) (i : A.obj ⟶ M.restrict j) [Mono i] :
    ∃ (K : X.Modules) (s : K ⟶ M), K.IsQuasicoherent ∧ Mono s ∧
      ∃ (e : K.restrict j ≅ A.obj),
        (Scheme.Modules.restrictFunctor j).map s = e.hom ≫ i := by
  have : A.obj.IsQuasicoherent :=
    quasicoherent_of_affineCharts A.obj (fun R a _ => (A.property R a).1)
  exact quasicoherent_subobject_preimage_of_quasiCompact j M A.obj i

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
