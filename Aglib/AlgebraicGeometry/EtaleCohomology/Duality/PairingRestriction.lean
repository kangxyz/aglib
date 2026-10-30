/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PairingTranspose

/-!
# The transposed duality map and restriction to an open subscheme

Let `jV : V ⟶ U` and `jU : U ⟶ X` be étale morphisms (open immersions `V ⊆ U ⊆ X` in the
application), `Λ` a ring and `F`, `G` sheaves of `Λ_U`-modules. Write `ε` for the original
counit of `jV_! ⊣ jV^*` and `τ` for the composition comparison
`moduleLowerShriekCompIso : (jV ≫ jU)_! ≅ jU_! ∘ jV_!`. The extension map
`H^r_c(V, F|_V) → H^r_c(U, F)` is postcomposition with `mk₀ (τ ≫ jU_!(ε_F))`, and the restriction
`Ext^s_U(F, G) → Ext^s_V(F|_V, G|_V)` is `e ↦ moduleLowerShriekExtEquiv jV (ε_F^* e)`.

`moduleLowerShriekPairingTransposeHom_restriction` is the square of the transposed map `ψ`
against these maps: `ψ_U(e) ∘ (extension map) = (extension map) ∘ ψ_V(e|_V)` into
`H^d_c(U, G)`. Followed by the trace, it is the square between `H^r(U, μ_n) → H^r(V, μ_n)` and the
dual of `H^{2-r}_c(V, ℤ/n) → H^{2-r}_c(U, ℤ/n)` in the diagram of Milne, *Lectures on Étale
Cohomology* v2.21, Thm. 14.7, proof, Step 2, p. 94 (whose commutativity Milne omits, p. 93);
the trace and the identifications `jV^* μ_n ≅ μ_n`, `jV^* ℤ/n ≅ ℤ/n` are separate.
-/

@[expose] public noncomputable section

universe w w' w'' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {V U X : Scheme.{u}} {jV : V ⟶ U} {jU : U ⟶ X} [Etale jV] [Etale jU]
  {Λ : Type (u + 1)} [Ring Λ]
  [HasExt.{w} (ModuleSheaf V Λ)] [HasExt.{w'} (ModuleSheaf U Λ)]
  [HasExt.{w''} (ModuleSheaf X Λ)]

/-- The square of the transposed map against restriction to `V`: for `e ∈ Ext^s_U(F, G)`,
`ψ_U(e)` after the extension map `H^{d-s}_c(V, F|_V) → H^{d-s}_c(U, F)` is `ψ_V(e|_V)` followed by
the extension map `H^d_c(V, G|_V) → H^d_c(U, G)`, where
`e|_V = moduleLowerShriekExtEquiv jV (ε_F^* e)`. -/
theorem moduleLowerShriekPairingTransposeHom_restriction (F G : ModuleSheaf U Λ) (d s : ℕ)
    (hs : s ≤ d) (e : Ext.{w'} F G s) :
    (moduleLowerShriekPairingTransposeHom jU Λ F G d s hs e).comp
        ((Ext.mk₀ ((moduleLowerShriekCompIso Λ jU jV).hom.app ((moduleInverseImage jV Λ).obj F) ≫
          (moduleLowerShriek jU Λ).map ((moduleLowerShriekAdjunction jV Λ).counit.app F))).postcomp
          (moduleUnit X Λ) (add_zero (d - s))) =
      ((Ext.mk₀ ((moduleLowerShriekCompIso Λ jU jV).hom.app ((moduleInverseImage jV Λ).obj G) ≫
          (moduleLowerShriek jU Λ).map ((moduleLowerShriekAdjunction jV Λ).counit.app G))).postcomp
          (moduleUnit X Λ) (add_zero d)).comp
        (moduleLowerShriekPairingTransposeHom (jV ≫ jU) Λ ((moduleInverseImage jV Λ).obj F)
          ((moduleInverseImage jV Λ).obj G) d s hs
          (moduleLowerShriekExtEquiv jV Λ ((moduleInverseImage jV Λ).obj F) G s
            ((Ext.mk₀ ((moduleLowerShriekAdjunction jV Λ).counit.app F)).comp e
              (zero_add s)))) :=
  Functor.extPairingTransposeHom_restriction
    (τ := moduleLowerShriekCompIso Λ jU jV) (adj := moduleLowerShriekAdjunction jV Λ) F G d s hs e

end AlgebraicGeometry.Scheme.EtaleCohomology
