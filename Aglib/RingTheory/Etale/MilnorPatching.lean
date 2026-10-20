/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# General étale Milnor patching interfaces

Relocated unchanged declarations from R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; original namespaces and explicit
source and hypothesis boundaries are retained.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Etale/MilnorPatching.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`db15836b98ef86d9143a99873cf148359187489074cdfb43f6a8b18cca02949e`.
-/

@[expose] public section

/-!
# Curves / Cyclic / Covers / Patching

Object-based extraction of the Wangcai checkpoint-27 construction.
Existing qualified declarations and their explicit mathematical premises are retained.
-/

section
/-! Universal, explicitly conditional Milnor patching interface.
Source: Stacks 08KQ, Lemma 15.7.7(5), in the situation 08KH.
https://stacks.math.columbia.edu/tag/08KQ
https://stacks.math.columbia.edu/tag/08KH
This file defines a proposition; it asserts no axiom and assumes no cycle cover.
-/
noncomputable section
open scoped TensorProduct
universe u
namespace RingHom.Etale.MilnorPatching

variable {R S T C D U : Type u}
  [CommRing R] [CommRing S] [CommRing T]
  [CommRing C] [CommRing D] [CommRing U]

/-- Literal ring-theoretic fibre product. -/
def fiberRing (f : R →+* T) (g : S →+* T) : Subring (R × S) :=
  (f.comp (RingHom.fst R S)).eqLocus (g.comp (RingHom.snd R S))

/-- The induced map of actual fibre products. -/
def fiberMap (f : R →+* T) (g : S →+* T) (r : R →+* C) (s : S →+* D)
    (t : T →+* U) (u : C →+* U) (v : D →+* U)
    (hc : u.comp r = t.comp f) (hd : v.comp s = t.comp g) :
    fiberRing f g →+* fiberRing u v where
  toFun x := ⟨(r x.val.1, s x.val.2), by
    change u (r x.val.1) = v (s x.val.2)
    rw [← RingHom.comp_apply, hc, RingHom.comp_apply,
      ← RingHom.comp_apply v s, hd, RingHom.comp_apply]
    exact congrArg t x.property⟩
  map_zero' := by apply Subtype.ext; exact Prod.ext (map_zero _) (map_zero _)
  map_one' := by apply Subtype.ext; exact Prod.ext (map_one _) (map_one _)
  map_add' x y := by apply Subtype.ext; exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_mul' x y := by apply Subtype.ext; exact Prod.ext (map_mul _ _ _) (map_mul _ _ _)

/-- Exact universal patching statement in tensor form. Both boundary
identifications are algebra isomorphisms compatible with the literal maps.
The quotient form in 08KQ follows from surjectivity and the standard proved
quotient/tensor isomorphism; the application proves this bridge explicitly
in `CyclicAffine.normalizationQuotientBoundaryEquiv`. -/
def EtalePatching : Prop :=
  ∀ (R S T C D U : Type u) [CommRing R] [CommRing S] [CommRing T]
    [CommRing C] [CommRing D] [CommRing U]
    (f : R →+* T) (g : S →+* T) (r : R →+* C) (s : S →+* D)
    (t : T →+* U) (u : C →+* U) (v : D →+* U)
    (hc : u.comp r = t.comp f) (hd : v.comp s = t.comp g),
    letI : Algebra R T := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra R C := r.toAlgebra
    letI : Algebra S D := s.toAlgebra
    letI : Algebra T U := t.toAlgebra
    ∀ (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U),
      (∀ c, eC (1 ⊗ₜ[R] c) = u c) →
      (∀ d, eD (1 ⊗ₜ[S] d) = v d) →
      Function.Surjective f → r.Etale → s.Etale →
      (fiberMap f g r s t u v hc hd).Etale

end RingHom.Etale.MilnorPatching

end -- noncomputable section
end
