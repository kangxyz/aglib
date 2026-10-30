/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.YonedaPairing
public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons

/-!
# The Yoneda pairing along a composite extension by zero

Let `jV : V ⟶ U` and `jU : U ⟶ X` be étale morphisms of schemes, for example open immersions
`V ⊆ U ⊆ X` with `X` the complete model of a curve, and `Λ` a ring. Write
`H^r_c(U, F) = Ext^r(Λ_X, jU_! F)` and `H^r_c(V, A) = Ext^r(Λ_X, (jV ≫ jU)_! A)`, as in
`Duality/YonedaPairing`. For a sheaf of `Λ_V`-modules `A` and a sheaf of `Λ_U`-modules `B`:

* `moduleLowerShriekCompAddEquiv : H^r_c(U, jV_! A) ≃+ H^r_c(V, A)` is postcomposition with the
  inverse of the original composition comparison `moduleLowerShriekCompIso : (jV ≫ jU)_! ≅
  jU_! ∘ jV_!`;
* `moduleLowerShriekExtEquiv jV : Ext^s_U(jV_! A, B) ≃+ Ext^s_V(A, jV^* B)` is the adjunction
  `jV_! ⊣ jV^*` on Ext groups.

Under these identifications the pairing on `U` with first argument in `H^r_c(U, jV_! A)` is the
pairing on `V`, followed by the map `H^t_c(V, jV^* B) → H^t_c(U, B)` induced by the composition
comparison and `jU_!` of the original counit `jV_! jV^* B ⟶ B`
(`moduleLowerShriekPairing_eq_comp_counit`): for `c ∈ H^r_c(U, jV_! A)` and
`e ∈ Ext^s_U(jV_! A, B)`,

`φ_U(c, e) = φ_V(c', e') ∘ (mk₀ (compIso.hom ≫ jU_! ε_B))`, `c' = moduleLowerShriekCompAddEquiv c`,
`e' = moduleLowerShriekExtEquiv jV e`.

Its basic case is `moduleLowerShriekPairing_moduleLowerShriekExt`: the pairing on `U` with
`jV_!` of a class on `V` is the pairing on `V` followed by the composition comparison. The proofs
use Mathlib's `Ext.comp_mapExactFunctor` and `Ext.mapExactFunctor_comp_mk₀_natTransApp`.

For an open `V = U − D` with `D` a finite set of closed points, the module localization sequence
`0 → jV_! jV^* F → F → i_* i^* F → 0` on `U` (`moduleLocalization_shortExact`) is a short exact
sequence on `U`, so the squares of `moduleLowerShriekPairingDualHom` apply to it; these
identifications turn its first terms into those on `V`. This is the compatibility used in the
diagram of Milne, *Lectures on Étale Cohomology* v2.21, Thm. 14.7, proof, Step 2, p. 94, whose
commutativity Milne omits (p. 93). No trace, purity or local cohomology is asserted.
-/

@[expose] public noncomputable section

universe w w' w'' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {V U X : Scheme.{u}} (jV : V ⟶ U) (jU : U ⟶ X) [Etale jV] [Etale jU]
  (Λ : Type (u + 1)) [Ring Λ] [HasExt.{w''} (ModuleSheaf X Λ)]

/-- `H^r_c(U, jV_! A) ≃+ H^r_c(V, A)`: postcomposition with the inverse of the original
composition comparison `(jV ≫ jU)_! ≅ jU_! ∘ jV_!`. -/
def moduleLowerShriekCompAddEquiv (A : ModuleSheaf V Λ) (r : ℕ) :
    Ext.{w''} (moduleUnit X Λ)
        ((moduleLowerShriek jU Λ).obj ((moduleLowerShriek jV Λ).obj A)) r ≃+
      Ext.{w''} (moduleUnit X Λ) ((moduleLowerShriek (jV ≫ jU) Λ).obj A) r :=
  Functor.extPairingCompAddEquiv (moduleLowerShriek jV Λ) (moduleLowerShriek jU Λ)
    (moduleLowerShriek (jV ≫ jU) Λ) (moduleLowerShriekCompIso Λ jU jV) (moduleUnit X Λ) A r

theorem moduleLowerShriekCompAddEquiv_apply (A : ModuleSheaf V Λ) (r : ℕ)
    (c : Ext.{w''} (moduleUnit X Λ)
      ((moduleLowerShriek jU Λ).obj ((moduleLowerShriek jV Λ).obj A)) r) :
    moduleLowerShriekCompAddEquiv jV jU Λ A r c =
      c.comp (Ext.mk₀ ((moduleLowerShriekCompIso Λ jU jV).inv.app A)) (add_zero r) :=
  rfl

theorem moduleLowerShriekCompAddEquiv_symm_apply (A : ModuleSheaf V Λ) (r : ℕ)
    (c : Ext.{w''} (moduleUnit X Λ) ((moduleLowerShriek (jV ≫ jU) Λ).obj A) r) :
    (moduleLowerShriekCompAddEquiv jV jU Λ A r).symm c =
      c.comp (Ext.mk₀ ((moduleLowerShriekCompIso Λ jU jV).hom.app A)) (add_zero r) :=
  rfl

variable {jV jU Λ} [HasExt.{w} (ModuleSheaf V Λ)] [HasExt.{w'} (ModuleSheaf U Λ)]

/-- The pairing on `U` with `jV_!` of a class on `V` is the pairing on `V`, followed by the
original composition comparison `(jV ≫ jU)_! B ⟶ jU_! jV_! B`. -/
theorem moduleLowerShriekPairing_moduleLowerShriekExt {A B : ModuleSheaf V Λ} {r s t : ℕ}
    (c : Ext.{w''} (moduleUnit X Λ)
      ((moduleLowerShriek jU Λ).obj ((moduleLowerShriek jV Λ).obj A)) r)
    (e : Ext.{w} A B s) (h : r + s = t) :
    moduleLowerShriekPairing jU Λ c (moduleLowerShriekExt jV Λ A B s e) h =
      (moduleLowerShriekPairing (jV ≫ jU) Λ (moduleLowerShriekCompAddEquiv jV jU Λ A r c) e
          h).comp
        (Ext.mk₀ ((moduleLowerShriekCompIso Λ jU jV).hom.app B)) (add_zero t) :=
  Functor.extPairing_mapExt
    (τ := moduleLowerShriekCompIso Λ jU jV) c e h

/-- The pairing on `U` for `jV_! A` is the pairing on `V` for `A`, followed by the map induced by
the original composition comparison and `jU_!` of the original counit `jV_! jV^* B ⟶ B`:
`φ_U(c, e) = φ_V(c', e') ∘ mk₀ (compIso.hom ≫ jU_! ε_B)`, where
`c' = moduleLowerShriekCompAddEquiv c` and `e' = moduleLowerShriekExtEquiv jV e`. -/
theorem moduleLowerShriekPairing_eq_comp_counit {A : ModuleSheaf V Λ} {B : ModuleSheaf U Λ}
    {r s t : ℕ}
    (c : Ext.{w''} (moduleUnit X Λ)
      ((moduleLowerShriek jU Λ).obj ((moduleLowerShriek jV Λ).obj A)) r)
    (e : Ext.{w'} ((moduleLowerShriek jV Λ).obj A) B s) (h : r + s = t) :
    moduleLowerShriekPairing jU Λ c e h =
      (moduleLowerShriekPairing (jV ≫ jU) Λ (moduleLowerShriekCompAddEquiv jV jU Λ A r c)
          (moduleLowerShriekExtEquiv jV Λ A B s e) h).comp
        (Ext.mk₀ ((moduleLowerShriekCompIso Λ jU jV).hom.app ((moduleInverseImage jV Λ).obj B) ≫
          (moduleLowerShriek jU Λ).map ((moduleLowerShriekAdjunction jV Λ).counit.app B)))
        (add_zero t) :=
  Functor.extPairing_eq_comp_counit
    (τ := moduleLowerShriekCompIso Λ jU jV) (moduleLowerShriekAdjunction jV Λ) c e h

variable (jV jU Λ)

/-- The square of the dual homomorphism for `jV_! A` on `U` against the one for `A` on `V`:
`φ_U(c)` is `φ_V(c')` after `moduleLowerShriekExtEquiv`, followed by postcomposition with
`mk₀ (compIso.hom ≫ jU_! ε_B)`, for `r ≤ d`. -/
theorem moduleLowerShriekPairingDualHom_eq_comp_counit (A : ModuleSheaf V Λ)
    (B : ModuleSheaf U Λ) (d r : ℕ) (hr : r ≤ d)
    (c : Ext.{w''} (moduleUnit X Λ)
      ((moduleLowerShriek jU Λ).obj ((moduleLowerShriek jV Λ).obj A)) r) :
    moduleLowerShriekPairingDualHom jU Λ ((moduleLowerShriek jV Λ).obj A) B d r hr c =
      ((Ext.mk₀ ((moduleLowerShriekCompIso Λ jU jV).hom.app ((moduleInverseImage jV Λ).obj B) ≫
          (moduleLowerShriek jU Λ).map ((moduleLowerShriekAdjunction jV Λ).counit.app B))).postcomp
          (moduleUnit X Λ) (add_zero d)).comp
        ((moduleLowerShriekPairingDualHom (jV ≫ jU) Λ A ((moduleInverseImage jV Λ).obj B) d r hr
          (moduleLowerShriekCompAddEquiv jV jU Λ A r c)).comp
          (moduleLowerShriekExtEquiv jV Λ A B (d - r)).toAddMonoidHom) :=
  Functor.extPairingDualHom_eq_comp_counit (moduleLowerShriek jV Λ) (moduleLowerShriek jU Λ)
    (moduleLowerShriek (jV ≫ jU) Λ) (moduleLowerShriekCompIso Λ jU jV) (moduleUnit X Λ)
    (moduleLowerShriekAdjunction jV Λ) A B d r hr c

end AlgebraicGeometry.Scheme.EtaleCohomology
