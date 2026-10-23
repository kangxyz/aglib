/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Injective
public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Surjective
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The original Artin--Schreier complex and its native kernel

All arrows below are the actual constant-prime-field inclusion and the literal
power-minus-identity map on additive etale sections. The native categorical
kernel retains its original inclusion and its original section values.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- The actual constant-prime-field inclusion followed by the original AS map. -/
def artinSchreierComplex (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  ShortComplex.mk (primeFieldToStructure X p hX) (artinSchreierMap X p hp hX)
    (primeFieldToStructure_artinSchreierMap X p hp hX)

/-- The original constant-prime-field map, factored through the native AS kernel. -/
def primeFieldToArtinSchreierKernel (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    primeFieldSheaf X p ⟶ kernel (artinSchreierMap X p hp hX) :=
  kernel.lift (artinSchreierMap X p hp hX) (primeFieldToStructure X p hX)
    (primeFieldToStructure_artinSchreierMap X p hp hX)

/-- Factoring through the native kernel preserves the original coefficient map. -/
theorem primeFieldToArtinSchreierKernel_ι (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    primeFieldToArtinSchreierKernel X p hp hX ≫ kernel.ι (artinSchreierMap X p hp hX) =
      primeFieldToStructure X p hX :=
  kernel.lift_ι _ _ _

/-- The original prime-field map remains mono after its canonical kernel factorization. -/
theorem primeFieldToArtinSchreierKernel_mono (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : Mono (primeFieldToArtinSchreierKernel X p hp hX) := by
  have : Mono (primeFieldToArtinSchreierKernel X p hp hX ≫
      kernel.ι (artinSchreierMap X p hp hX)) := by
    rw [primeFieldToArtinSchreierKernel_ι]
    exact primeFieldToStructure_mono X p hp hX
  exact mono_of_mono (primeFieldToArtinSchreierKernel X p hp hX)
    (kernel.ι (artinSchreierMap X p hp hX))

/-- The actual global section underlying a section of the original categorical kernel. -/
def artinSchreierKernelSection (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etaleᵒᵖ)
    (s : (kernel (artinSchreierMap X p hp hX)).obj.obj U) :
    (structurePresheaf X).obj U :=
  ((kernel.ι (artinSchreierMap X p hp hX)).hom.app U s).down

/-- Every section of that native kernel is a root of the literal original polynomial. -/
theorem artinSchreierKernelSection_equation (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etaleᵒᵖ)
    (s : (kernel (artinSchreierMap X p hp hX)).obj.obj U) :
    artinSchreierKernelSection X p hp hX U s ^ p -
      artinSchreierKernelSection X p hp hX U s = 0 := by
  have h := congrArg
    (fun t : kernel (artinSchreierMap X p hp hX) ⟶ additiveStructureSheaf X =>
      t.hom.app U s) (kernel.condition (artinSchreierMap X p hp hX))
  exact congrArg ULift.down h

end AlgebraicGeometry.Scheme.EtaleCohomology
