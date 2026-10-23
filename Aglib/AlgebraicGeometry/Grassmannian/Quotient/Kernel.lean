/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.KernelPullback

/-!
# The kernel of a rank-`k` locally free quotient of `O^n`

For `q : LocallyFreeQuotient X k n`, the kernel `q.kernel` of the quotient map `q.π : O_X^n ⟶ Q`
with its inclusion `q.kernelι : q.kernel ⟶ O_X^n` sits in the short exact sequence
`0 → K → O_X^n → Q → 0` (`q.shortExact`), which splits locally because `Q` is finite locally free
(`q.exists_local_splitting`).

Formation of the kernel commutes with pullback along every morphism of schemes `f : Y ⟶ X`, with
no flatness hypothesis: `pullbackKernelIso f q : f^* q.kernel ≅ (q.pullback f).kernel`, and under
it the inclusion of `(q.pullback f).kernel` into `O_Y^n` is the pullback of `q.kernelι` followed by
`pullbackFreeIso f : f^* O_X^n ≅ O_Y^n` (`pullbackKernelIso_hom_kernelι`). Isomorphic quotients
have isomorphic kernels under `O^n` (`IsoUnder.kernelIso`).

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26:
the kernel `v : K → p_G^* E` of the universal quotient and `K_Y = ker(f_Y) = φ^* ker(f)`.
Encoded subset: quotients of `O^n = SheafOfModules.free (ULift (Fin n))` on arbitrary schemes, all
`k` and `n`, arbitrary `f`. Convention: `k` is the rank of the quotient, as in
`Grassmannian.LocallyFreeQuotient`. Finite local freeness of the kernel and its rank `n - k` are in
`Aglib.AlgebraicGeometry.Grassmannian.Quotient.KernelRank`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules

namespace LocallyFreeQuotient

variable {X Y : Scheme.{u}} {k n : ℕ}

instance isFiniteLocallyFree_obj (q : LocallyFreeQuotient X k n) :
    IsFiniteLocallyFree X q.obj :=
  q.hasRank.isFiniteLocallyFree

/-- The kernel `K` of the quotient map `π : O_X^n ⟶ Q`. -/
def kernel (q : LocallyFreeQuotient X k n) : X.Modules :=
  Limits.kernel q.π

/-- The inclusion `K ⟶ O_X^n` of the kernel of a quotient. -/
def kernelι (q : LocallyFreeQuotient X k n) : q.kernel ⟶ freeSheaf X n :=
  Limits.kernel.ι q.π

instance mono_kernelι (q : LocallyFreeQuotient X k n) : Mono q.kernelι :=
  inferInstanceAs (Mono (Limits.kernel.ι q.π))

@[reassoc (attr := simp)]
theorem kernelι_π (q : LocallyFreeQuotient X k n) : q.kernelι ≫ q.π = 0 :=
  Limits.kernel.condition q.π

/-- The inclusion of the kernel is a kernel of the quotient map. -/
def kernelIsKernel (q : LocallyFreeQuotient X k n) :
    IsLimit (KernelFork.ofι q.kernelι q.kernelι_π) :=
  Limits.kernelIsKernel q.π

/-- The sequence `0 → K → O_X^n → Q → 0` of a quotient. -/
@[simps!]
def shortComplex (q : LocallyFreeQuotient X k n) : ShortComplex X.Modules :=
  ShortComplex.mk q.kernelι q.π q.kernelι_π

/-- The sequence `0 → K → O_X^n → Q → 0` is short exact. -/
theorem shortExact (q : LocallyFreeQuotient X k n) : q.shortComplex.ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ q.kernelIsKernel
  mono_f := inferInstanceAs (Mono q.kernelι)
  epi_g := inferInstanceAs (Epi q.π)

/-- The sequence `0 → K → O_X^n → Q → 0` splits on a neighbourhood of every point, because `Q` is
finite locally free. -/
theorem exists_local_splitting (q : LocallyFreeQuotient X k n) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (q.shortComplex.map (overRestriction U)).Splitting :=
  have : IsFiniteLocallyFree X q.shortComplex.X₃ := q.isFiniteLocallyFree_obj
  Scheme.Modules.exists_local_splitting q.shortExact x

/-- **Pullback of the kernel.** For every morphism of schemes `f : Y ⟶ X` (no flatness), the
pullback of the inclusion `K ⟶ O_X^n`, followed by `pullbackFreeIso f : f^* O_X^n ≅ O_Y^n`, is a
kernel of the pulled back quotient map `(q.pullback f).π`. -/
def pullbackKernelιIsKernel (f : Y ⟶ X) (q : LocallyFreeQuotient X k n) :
    IsLimit (KernelFork.ofι (f := (q.pullback f).π)
      ((Scheme.Modules.pullback f).map q.kernelι ≫ (pullbackFreeIso f (ULift.{u} (Fin n))).hom)
      (by
        rw [pullback_π, Category.assoc, CategoryTheory.Iso.hom_inv_id_assoc,
          ← CategoryTheory.Functor.map_comp, kernelι_π, CategoryTheory.Functor.map_zero])) :=
  KernelFork.isLimitOfIsLimitOfIff (pullbackKernelIsKernel f q.π) _
    (pullbackFreeIso f (ULift.{u} (Fin n))) (fun _ φ ↦ by simp [pullback_π])

/-- The pullback of the kernel of a quotient is the kernel of the pulled back quotient. -/
def pullbackKernelIso (f : Y ⟶ X) (q : LocallyFreeQuotient X k n) :
    (Scheme.Modules.pullback f).obj q.kernel ≅ (q.pullback f).kernel :=
  IsLimit.conePointUniqueUpToIso
    (t := KernelFork.ofι (q.pullback f).kernelι (q.pullback f).kernelι_π)
    (pullbackKernelιIsKernel f q) (q.pullback f).kernelIsKernel

/-- Under `pullbackKernelIso`, the inclusion of the kernel of the pulled back quotient into `O_Y^n`
is the pullback of the inclusion `K ⟶ O_X^n` followed by `pullbackFreeIso f`. -/
@[reassoc (attr := simp)]
theorem pullbackKernelIso_hom_kernelι (f : Y ⟶ X) (q : LocallyFreeQuotient X k n) :
    (pullbackKernelIso f q).hom ≫ (q.pullback f).kernelι =
      (Scheme.Modules.pullback f).map q.kernelι ≫ (pullbackFreeIso f (ULift.{u} (Fin n))).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (pullbackKernelιIsKernel f q)
    (q.pullback f).kernelIsKernel WalkingParallelPair.zero

@[reassoc (attr := simp)]
theorem pullbackKernelIso_inv_kernelι (f : Y ⟶ X) (q : LocallyFreeQuotient X k n) :
    (pullbackKernelIso f q).inv ≫ (Scheme.Modules.pullback f).map q.kernelι ≫
      (pullbackFreeIso f (ULift.{u} (Fin n))).hom = (q.pullback f).kernelι :=
  IsLimit.conePointUniqueUpToIso_inv_comp (pullbackKernelιIsKernel f q)
    (q.pullback f).kernelIsKernel WalkingParallelPair.zero

/-- Isomorphic quotients under `O_X^n` have the same kernel: the inclusion of the kernel of `P` is
a kernel of the quotient map of `Q`. -/
def IsoUnder.kernelιIsKernel {P Q : LocallyFreeQuotient X k n} (e : IsoUnder P Q) :
    IsLimit (KernelFork.ofι (f := Q.π) P.kernelι (by rw [← e.comm, kernelι_π_assoc, zero_comp])) :=
  KernelFork.isLimitOfIsLimitOfIff' P.kernelIsKernel Q.π (fun _ φ ↦ by
    rw [← e.comm, ← Category.assoc]
    exact (Preadditive.IsIso.comp_right_eq_zero _ _).symm)

/-- The isomorphism of kernels induced by an isomorphism of quotients under `O_X^n`. -/
def IsoUnder.kernelIso {P Q : LocallyFreeQuotient X k n} (e : IsoUnder P Q) :
    P.kernel ≅ Q.kernel :=
  IsLimit.conePointUniqueUpToIso (t := KernelFork.ofι Q.kernelι Q.kernelι_π) e.kernelιIsKernel
    Q.kernelIsKernel

@[reassoc (attr := simp)]
theorem IsoUnder.kernelIso_hom_kernelι {P Q : LocallyFreeQuotient X k n} (e : IsoUnder P Q) :
    e.kernelIso.hom ≫ Q.kernelι = P.kernelι :=
  IsLimit.conePointUniqueUpToIso_hom_comp e.kernelιIsKernel Q.kernelIsKernel
    WalkingParallelPair.zero

@[reassoc (attr := simp)]
theorem IsoUnder.kernelIso_inv_kernelι {P Q : LocallyFreeQuotient X k n} (e : IsoUnder P Q) :
    e.kernelIso.inv ≫ P.kernelι = Q.kernelι :=
  IsLimit.conePointUniqueUpToIso_inv_comp e.kernelιIsKernel Q.kernelIsKernel
    WalkingParallelPair.zero

end LocallyFreeQuotient

end AlgebraicGeometry.Grassmannian
