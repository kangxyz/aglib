/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Ext.DualQuotient

/-! The original coefficient quotient and dual-freeness endpoint. -/

@[expose] public section

open CategoryTheory Abelian

universe u

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

example (a : R) (ha : IsSMulRegular R a)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1)]
    (f : Module.Dual R M) (m : M) :
    Module.dualQuotSMulTopEquivHom a ha (Submodule.Quotient.mk f) m =
      Ideal.Quotient.mk (Ideal.span {a}) (f m) :=
  Module.dualQuotSMulTopEquivHom_apply_mk a ha f m

example [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (a : R) (ha : IsSMulRegular R a) (ham : a ∈ IsLocalRing.maximalIdeal R)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1)]
    [Module.Free (R ⧸ Ideal.span {a}) (M →ₗ[R] R ⧸ Ideal.span {a})] :
    Module.Free R (Module.Dual R M) :=
  Module.free_dual_of_free_quotientHom a ha ham

example [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (a : R) (ha : IsSMulRegular R a) (ham : a ∈ IsLocalRing.maximalIdeal R)
    [Subsingleton (Ext (ModuleCat.of R M)
      (ModuleCat.of R (R ⧸ Ideal.span {a})) 1)] :
    Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1) :=
  Module.subsingleton_ext_one_of_quotient a ha ham
