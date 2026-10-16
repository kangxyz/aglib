/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Subobjects
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsGlobal

/-!
# Extension of coherent open subobjects

A finite-type subobject of the restriction of a coherent sheaf extends as a subobject on the
original scheme. The conditional construction records quasicoherence of the specified
pushed-forward cokernel; the locally Noetherian result supplies it.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/SubobjectExtension.lean`.
SHA-256: `c3d895a552379d147cf37e13109c25c3d5f82b4144b50fd96f8e70b5987cdf79`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/Fullness.lean`.
SHA-256: `61afed4d0f4e8a0a3ffbefa660420929f4823a2a75701f5a9115cad7f0bbe9ec`.
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
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual preimage kernel extends a coherent subobject, provided the
pushforward of its quasicoherent cokernel is quasicoherent. -/
theorem affineLocallyFiniteType_subobject_extension_of_quasicoherent_pushforward
    (H : FiniteTypeSheaves X) (A : FiniteTypeSheaves U) (i : A ⟶ (finiteTypeSheavesRestriction
      j).obj H)
    [Mono i]
    [((Scheme.Modules.pushforward j).obj (cokernel i.hom)).IsQuasicoherent] :
    ∃ (H' : FiniteTypeSheaves X) (s : H' ⟶ H), Mono s ∧
      ∃ (e : (finiteTypeSheavesRestriction j).obj H' ≅ A),
        (finiteTypeSheavesRestriction j).map s = e.hom ≫ i := by
  let F := Scheme.Modules.restrictFunctor j
  let adj := Scheme.Modules.restrictAdjunction j
  have : Mono i.hom := (finiteTypeSheavesToModules U).map_mono i
  let C := cokernel i.hom
  let k : H.obj ⟶ (Scheme.Modules.pushforward j).obj C :=
    adj.homEquiv H.obj C (cokernel.π i.hom)
  have hk : F.map k ≫ adj.counit.app C = cokernel.π i.hom := by
    simpa only [Adjunction.homEquiv_counit] using
      (adj.homEquiv H.obj C).symm_apply_apply (cokernel.π i.hom)
  have : (kernel k).IsQuasicoherent := quasicoherent_kernel k
  let H' : FiniteTypeSheaves X :=
    ⟨kernel k, affineLocallyFiniteType_of_quasicoherent_mono (kernel.ι k) H.property⟩
  let s : H' ⟶ H := ObjectProperty.homMk (kernel.ι k)
  have hs : Mono s := by
    apply (finiteTypeSheavesToModules X).mono_of_mono_map
    exact inferInstanceAs (Mono (kernel.ι k))
  let h₁ := isKernelCompMono
    (KernelFork.mapIsLimit _ (kernelIsKernel k) F) (adj.counit.app C) hk.symm
  let h₂ := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i.hom)
  let e : F.obj (kernel k) ≅ A.obj := h₁.conePointUniqueUpToIso h₂
  have he : e.hom ≫ i.hom = F.map (kernel.ι k) :=
    h₁.conePointUniqueUpToIso_hom_comp h₂ WalkingParallelPair.zero
  let e' : (finiteTypeSheavesRestriction j).obj H' ≅ A :=
    (affineLocallyFiniteType U).fullyFaithfulι.preimageIso e
  refine ⟨H', s, hs, e', ?_⟩
  apply (finiteTypeSheavesToModules U).map_injective
  exact he.symm

/-- Every coherent subsheaf on the open extends inside its given coherent
ambient sheaf by the actual quasicoherent preimage kernel. -/
theorem coherent_subobject_extension (H : FiniteTypeSheaves X) (A : FiniteTypeSheaves U)
    (i : A ⟶ (finiteTypeSheavesRestriction j).obj H) [Mono i] :
    ∃ (H' : FiniteTypeSheaves X) (s : H' ⟶ H), Mono s ∧
      ∃ (e : (finiteTypeSheavesRestriction j).obj H' ≅ A),
        (finiteTypeSheavesRestriction j).map s = e.hom ≫ i := by
  have : (cokernel i.hom).IsQuasicoherent := quasicoherent_cokernel i.hom
  have : ((Scheme.Modules.pushforward j).obj (cokernel i.hom)).IsQuasicoherent :=
    quasicoherent_pushforward_open_of_locallyNoetherian j _
  exact affineLocallyFiniteType_subobject_extension_of_quasicoherent_pushforward j H A i

end AlgebraicGeometry.Scheme.Modules.Coherent
