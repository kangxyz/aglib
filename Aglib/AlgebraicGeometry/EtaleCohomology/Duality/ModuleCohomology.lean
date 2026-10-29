/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ConstantRing
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Cohomology of constant-ring module sheaves computed among modules

Let `X` be a scheme, `Λ` a ring and `Λ_X` the associated constant ring sheaf on the small
étale site. For a sheaf `G` of `Λ_X`-modules, the group `Ext^q(Λ_X, G)` computed in the
category of `Λ_X`-modules is the abelian sheaf cohomology `Sheaf.H` of the underlying abelian
sheaf of `G`, naturally in `G` and compatibly with the connecting maps of short exact
sequences. For `Λ = ℤ/n` this is the statement of Milne, *Lectures on Étale Cohomology*
(v2.21), p. 102 ("The Ext group"), that `H^r(X_et, F)` is the same whether computed in
`Sh(X_et)` or in `Sh(X_et, n)`.

The isomorphism is `Sheaf.ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars` for the
constant ring sheaf; its forward map is the Ext map of the exact underlying-sheaf functor
followed by the integer-to-unit source map. Naturality and the connecting-map compatibility
are `Sheaf.ModuleCoefficients.cohomologyMap_naturality` and `cohomologyMap_connecting`. This
leaf states them in the étale coefficient notation, for arbitrary independent Ext universes.
No condition on `X` or `Λ` is used; `HasExt` is a size hypothesis, satisfied for example by
`SheafOfModules.hasExt` and `hasExtStandard`.
-/

@[expose] public noncomputable section

universe w w' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge abelianSheafEnoughInjectivesLarge

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The rank-one module sheaf `Λ_X`: the constant ring sheaf as a module over itself. -/
abbrev moduleUnit : ModuleSheaf X Λ :=
  SheafOfModules.liftedUnit.{u + 1, u, u + 1, u + 1} (constantRing X Λ)

variable [HasExt.{w} (ModuleSheaf X Λ)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]

/-- `Ext^q(Λ_X, G)` among `Λ_X`-modules is the cohomology of the underlying abelian sheaf. -/
def moduleUnitExtAddEquiv (G : ModuleSheaf X Λ) (q : ℕ) :
    Ext.{w} (moduleUnit X Λ) G q ≃+
      Sheaf.H.{w'} ((SheafOfModules.toSheaf (constantRing X Λ)).obj G) q :=
  Sheaf.ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars terminalIsTerminal
    (constantRing X Λ) G q

/-- The forward map is the original exact-forgetting comparison map. -/
theorem moduleUnitExtAddEquiv_apply (G : ModuleSheaf X Λ) (q : ℕ)
    (x : Ext.{w} (moduleUnit X Λ) G q) :
    moduleUnitExtAddEquiv X Λ G q x =
      Sheaf.ModuleCoefficients.cohomologyMap terminalIsTerminal (constantRing X Λ) G q x :=
  rfl

/-- In degree zero the comparison is underlying-sheaf forgetting after the integer map. -/
theorem moduleUnitExtAddEquiv_mk₀ (G : ModuleSheaf X Λ) (f : moduleUnit X Λ ⟶ G) :
    moduleUnitExtAddEquiv X Λ G 0 (Ext.mk₀ f) =
      Ext.mk₀ (Sheaf.ModuleCoefficients.liftedUnitIntegerMap terminalIsTerminal
        (constantRing X Λ) ≫ (SheafOfModules.toSheaf (constantRing X Λ)).map f) :=
  Sheaf.ModuleCoefficients.cohomologyMap_mk₀ terminalIsTerminal (constantRing X Λ) G f

/-- Naturality: postcomposition with a module map corresponds to `Sheaf.H.map` of the
underlying map. -/
theorem moduleUnitExtAddEquiv_naturality {G G' : ModuleSheaf X Λ} (f : G ⟶ G') (q : ℕ)
    (x : Ext.{w} (moduleUnit X Λ) G q) :
    moduleUnitExtAddEquiv X Λ G' q (x.comp (Ext.mk₀ f) (add_zero q)) =
      Sheaf.H.map ((SheafOfModules.toSheaf (constantRing X Λ)).map f) q
        (moduleUnitExtAddEquiv X Λ G q x) :=
  Sheaf.ModuleCoefficients.cohomologyMap_naturality terminalIsTerminal (constantRing X Λ) f q x

/-- Connecting maps: the module connecting map, postcomposition with the extension class, is
the `Sheaf.H` connecting map of the underlying short exact sequence. -/
theorem moduleUnitExtAddEquiv_connecting (S : ShortComplex (ModuleSheaf X Λ))
    (hS : S.ShortExact) (q : ℕ) (x : Ext.{w} (moduleUnit X Λ) S.X₃ q) :
    moduleUnitExtAddEquiv X Λ S.X₁ (q + 1) (x.comp hS.extClass rfl) =
      Sheaf.H.δ (hS.map_of_exact (SheafOfModules.toSheaf (constantRing X Λ))) q (q + 1) rfl
        (moduleUnitExtAddEquiv X Λ S.X₃ q x) :=
  Sheaf.ModuleCoefficients.cohomologyMap_connecting terminalIsTerminal (constantRing X Λ)
    S hS q x

end AlgebraicGeometry.Scheme.EtaleCohomology
