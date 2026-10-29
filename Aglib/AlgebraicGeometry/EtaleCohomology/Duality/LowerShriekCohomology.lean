/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ModuleCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlying

/-!
# Cohomology of an extension by zero computed among modules

Let `j : U ⟶ X` be an étale morphism of schemes, `Λ` a ring and `F` a sheaf of modules over the
constant ring sheaf `Λ_U`. The group `Ext^r(Λ_X, j_! F)`, computed among `Λ_X`-modules with
the module extension by zero `j_! = moduleLowerShriek j Λ`, is the abelian sheaf cohomology
`Sheaf.H ((etaleLowerShriek j).obj F₀) r` of the abelian extension by zero of the underlying
abelian sheaf `F₀` of `F`. The isomorphism is natural in `F` and sends the module connecting map
of a short exact sequence `0 → F' → F → F'' → 0` (postcomposition with the extension class of
its extension by zero) to the `Sheaf.H` connecting map of the abelian extension by zero of the
underlying sequence.

For an open immersion `j` of a curve `U` into its complete model `X`, the right side is
`H^r_c(U, F) = H^r(X, j_! F)` of Milne, *Lectures on Étale Cohomology* (v2.21), p. 92, and the
left side is the same group computed in `Sh(X_et, n)` when `Λ = ℤ/n` (p. 102, "The Ext
group"). The construction composes the comparison `moduleUnitExtAddEquiv` with `Sheaf.H` of the
original isomorphism `moduleLowerShriekUnderlyingIso`. No condition on `j`, `X` or `Λ` beyond
étaleness of `j` is used; `HasExt` is a size hypothesis.
-/

@[expose] public noncomputable section

universe w w' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (Λ : Type (u + 1)) [Ring Λ]
  [HasExt.{w} (ModuleSheaf X Λ)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]

/-- `Ext^r(Λ_X, j_! F)` among modules is `Sheaf.H` of the abelian extension by zero of the
underlying sheaf of `F`. -/
def moduleLowerShriekCohomologyAddEquiv (F : ModuleSheaf U Λ) (r : ℕ) :
    Ext.{w} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r ≃+
      Sheaf.H.{w'} ((etaleLowerShriek j).obj
        ((SheafOfModules.toSheaf (constantRing U Λ)).obj F)) r :=
  (moduleUnitExtAddEquiv X Λ ((moduleLowerShriek j Λ).obj F) r).trans
    ((Sheaf.functorH (Scheme.smallEtaleTopology X) r).mapIso
      ((moduleLowerShriekUnderlyingIso j Λ).app F)).addCommGroupIsoToAddEquiv

/-- The isomorphism is the module comparison followed by `Sheaf.H.map` of the original
underlying isomorphism. -/
theorem moduleLowerShriekCohomologyAddEquiv_apply (F : ModuleSheaf U Λ) (r : ℕ)
    (c : Ext.{w} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) :
    moduleLowerShriekCohomologyAddEquiv j Λ F r c =
      Sheaf.H.map ((moduleLowerShriekUnderlyingIso j Λ).hom.app F) r
        (moduleUnitExtAddEquiv X Λ ((moduleLowerShriek j Λ).obj F) r c) :=
  rfl

/-- Naturality in the coefficient sheaf on `U`. -/
theorem moduleLowerShriekCohomologyAddEquiv_naturality {F F' : ModuleSheaf U Λ} (u : F ⟶ F')
    (r : ℕ) (c : Ext.{w} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) :
    moduleLowerShriekCohomologyAddEquiv j Λ F' r
        (c.comp (Ext.mk₀ ((moduleLowerShriek j Λ).map u)) (add_zero r)) =
      Sheaf.H.map ((etaleLowerShriek j).map ((SheafOfModules.toSheaf (constantRing U Λ)).map u)) r
        (moduleLowerShriekCohomologyAddEquiv j Λ F r c) := by
  have hu := (moduleLowerShriekUnderlyingIso j Λ).hom.naturality u
  simp only [Functor.comp_map] at hu
  rw [moduleLowerShriekCohomologyAddEquiv_apply, moduleLowerShriekCohomologyAddEquiv_apply,
    moduleUnitExtAddEquiv_naturality, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, hu]

/-- Connecting maps: the module connecting map of `j_!` of a short exact sequence on `U`
corresponds to the `Sheaf.H` connecting map of the abelian extension by zero of the underlying
short exact sequence. -/
theorem moduleLowerShriekCohomologyAddEquiv_connecting (S : ShortComplex (ModuleSheaf U Λ))
    (hS : S.ShortExact) (r : ℕ)
    (c : Ext.{w} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj S.X₃) r) :
    moduleLowerShriekCohomologyAddEquiv j Λ S.X₁ (r + 1)
        (c.comp (shortExact_moduleLowerShriek j Λ hS).extClass rfl) =
      Sheaf.H.δ (shortExact_etaleLowerShriek j
          (hS.map_of_exact (SheafOfModules.toSheaf (constantRing U Λ)))) r (r + 1) rfl
        (moduleLowerShriekCohomologyAddEquiv j Λ S.X₃ r c) := by
  rw [moduleLowerShriekCohomologyAddEquiv_apply, moduleLowerShriekCohomologyAddEquiv_apply]
  have hc := moduleUnitExtAddEquiv_connecting X Λ (S.map (moduleLowerShriek j Λ))
    (shortExact_moduleLowerShriek j Λ hS) r c
  refine (congrArg
    (Sheaf.H.map ((moduleLowerShriekUnderlyingIso j Λ).hom.app S.X₁) (r + 1)) hc).trans ?_
  exact (Sheaf.H.δ_naturality r (r + 1) rfl _ _
    (S.mapNatTrans (moduleLowerShriekUnderlyingIso j Λ).hom) _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
