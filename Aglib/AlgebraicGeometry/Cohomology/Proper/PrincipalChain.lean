/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.Stabilization
public import Aglib.AlgebraicGeometry.Modules.Invertible.PrincipalChain
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Field
public import Aglib.AlgebraicGeometry.Cohomology.Support.Finite

/-!
# Lifting a principal-chain quotient section on a proper field scheme

The actual principal-section chain has acyclic quotients when its boundary is
a finite set of closed points. Proper coherent finiteness supplies the initial
finite H1; stabilization then lifts one original quotient section through the
original coefficient map on global sections. No H1-vanishing bound, normality,
dimension or prior projectivity of the field scheme is assumed.

The intended upstream module is
`Aglib.AlgebraicGeometry.Cohomology.Proper.PrincipalChain`. Its current consumer
is the finite-pencil construction for proper integral curves in R5Lab. Native
proper finiteness and finite-support acyclicity are from Aglib revision
`197ca0728db3cdf1552a6bcefeeda901e3377862`.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.Proper.PrincipalChain` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`4f2c2378a59794c61b4e6a48d84df135eb4f1be505dbe12b9356a45622d2fcd3`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {K : Type u} [Field K]

/-- The original principal-chain quotient has zero H1 for a finite closed boundary. -/
theorem principalChain_quotientH1_subsingleton
    (X : FScheme K) (C : PrincipalChain X.left)
    (hfin : ((C.W : Set X.left)ᶜ).Finite)
    (hclosed : ∀ x : X.left, x ∉ C.W → IsClosed ({x} : Set X.left)) (n : ℕ) :
    Subsingleton (moduleCohomology K X (C.quotient n) 1) := by
  let Z := (C.W : Set X.left)ᶜ
  let : Finite Z := hfin
  let := Fintype.ofFinite Z
  let e := Fintype.equivFin Z
  let p : Fin (Fintype.card Z) → X.left := fun i => (e.symm i).val
  apply finiteClosedSupportModuleCohomology_positive X (C.quotient n)
    p (Subtype.val_injective.comp e.symm.injective)
    (fun i => hclosed (e.symm i).val (e.symm i).property) ?_ 0
  intro x hx
  have hxW : x ∈ C.W := by
    by_contra h
    exact hx ⟨e ⟨x, h⟩, by simp [p]⟩
  exact C.quotient_stalk_isZero n x hxW

/-- Proper coherent finiteness and finite closed support give an actual lift
of one canonical quotient section, under the original global-section map. -/
theorem exists_lift_principalChain_quotientSection
    (X : FScheme K) [IsProper X.hom] (C : PrincipalChain X.left)
    (hfin : ((C.W : Set X.left)ᶜ).Finite)
    (hclosed : ∀ x : X.left, x ∉ C.W → IsClosed ({x} : Set X.left)) :
    ∃ (n : ℕ) (τ : Γ(C.line (n + 1), ⊤)),
      (C.quotientMap n).val.app (op ⊤) τ = C.quotientSection n := by
  have : FiniteDimensional K (moduleCohomology K X (C.line 0) 1) :=
    properModuleCohomologyFinite K X (C.line 0) 1 inferInstance inferInstance
  obtain ⟨n, _, hsurj⟩ := exists_surjective_moduleH0Map_of_h1_chain X
    C.line C.quotient C.step C.quotientMap (fun n => cokernel.condition (C.step n))
    C.shortExact (principalChain_quotientH1_subsingleton X C hfin hclosed)
  obtain ⟨τ, hτ⟩ := hsurj (C.quotientSection n)
  exact ⟨n, τ, hτ⟩

end AlgebraicGeometry.Scheme.Cohomology
