/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback

/-!
# Pullback of the kernel of an epimorphism onto a finite locally free sheaf

Let `g : M ⟶ N` be an epimorphism of module sheaves on a scheme `Y` with `N` finite locally free,
and let `f : X ⟶ Y` be any morphism of schemes. The kernel sequence `0 → ker g → M → N → 0` is
locally split, so its pullback along `f` is short exact (`shortExact_pullback`; no flatness of `f`
is assumed). Hence `f^*(ker g) → f^*M` is a kernel of `f^* g`
(`pullbackKernelIsKernel`), and `pullbackKernelIso f g : f^*(ker g) ≅ ker (f^* g)` commutes with
the inclusions into `f^* M` (`pullbackKernelIso_hom_ι`).

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26
(`K_Y = ker(f_Y) = φ^* ker(f)` for a locally free quotient `f`). Stacks has no lemma for this
statement (checked 2026-10-19); the proof combines right exactness of `f^*` (Stacks, Tag 01AJ) with
the local splitting. Encoded subset:
module sheaves on schemes, an arbitrary morphism `f`, an epimorphism onto a finite locally free
sheaf.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The kernel sequence of an epimorphism is short exact. -/
theorem shortExact_kernelSequence {M N : Y.Modules} (g : M ⟶ N) [Epi g] :
    (ShortComplex.kernelSequence g).ShortExact where
  exact := ShortComplex.kernelSequence_exact g
  epi_g := inferInstanceAs (Epi g)

/-- **Pullback of a kernel.** For an epimorphism `g : M ⟶ N` onto a finite locally free sheaf and
any morphism of schemes `f`, the pullback of `ker g ⟶ M` is a kernel of `f^* g`. No flatness of
`f` is assumed. -/
def pullbackKernelIsKernel (f : X ⟶ Y) {M N : Y.Modules} (g : M ⟶ N) [Epi g]
    [IsFiniteLocallyFree Y N] :
    IsLimit (KernelFork.ofι ((pullback f).map (kernel.ι g))
      (((ShortComplex.kernelSequence g).map (pullback f)).zero)) :=
  have : IsFiniteLocallyFree Y (ShortComplex.kernelSequence g).X₃ := inferInstanceAs
    (IsFiniteLocallyFree Y N)
  (shortExact_pullback f (shortExact_kernelSequence g)).fIsKernel

/-- The pullback of the kernel of an epimorphism onto a finite locally free sheaf is the kernel of
the pullback. -/
def pullbackKernelIso (f : X ⟶ Y) {M N : Y.Modules} (g : M ⟶ N) [Epi g]
    [IsFiniteLocallyFree Y N] :
    (pullback f).obj (kernel g) ≅ kernel ((pullback f).map g) :=
  IsLimit.conePointUniqueUpToIso (pullbackKernelIsKernel f g) (limit.isLimit _)

@[reassoc (attr := simp)]
theorem pullbackKernelIso_hom_ι (f : X ⟶ Y) {M N : Y.Modules} (g : M ⟶ N) [Epi g]
    [IsFiniteLocallyFree Y N] :
    (pullbackKernelIso f g).hom ≫ kernel.ι ((pullback f).map g) = (pullback f).map (kernel.ι g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (pullbackKernelIsKernel f g) (limit.isLimit _)
    WalkingParallelPair.zero

@[reassoc (attr := simp)]
theorem pullbackKernelIso_inv_map_ι (f : X ⟶ Y) {M N : Y.Modules} (g : M ⟶ N) [Epi g]
    [IsFiniteLocallyFree Y N] :
    (pullbackKernelIso f g).inv ≫ (pullback f).map (kernel.ι g) = kernel.ι ((pullback f).map g) :=
  IsLimit.conePointUniqueUpToIso_inv_comp (pullbackKernelIsKernel f g) (limit.isLimit _)
    WalkingParallelPair.zero

end AlgebraicGeometry.Scheme.Modules
