/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.OpenLocalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.GeometricFunctors

/-!
# Compactly supported cohomology of a direct image from a closed part, among modules

Let `jU : U ⟶ X` be an open immersion, `i : Z ⟶ U` a morphism such that `i ≫ jU` is a closed
immersion, and `Λ` a ring. For a sheaf `M` of `Λ_Z`-modules with underlying abelian sheaf `M₀`,

`moduleLowerShriekDirectImageAddEquiv : Ext^q(Λ_X, jU_!(i_* M)) ≃+ H^q(Z, M₀)`,

computed among `Λ_X`-modules with the native module direct image `i_*`, is the comparison
`moduleLowerShriekCohomologyAddEquiv` with the abelian compactly supported cohomology, then
`CompactSupport.H.map` of the original underlying isomorphism `moduleDirectImageUnderlyingIso`,
then `CompactSupport.directImageAddEquiv` (through `jU_! ∘ i_* ≅ (i ≫ jU)_*`, Stacks, Tag 0GJ1).
This identifies the third term of the long exact sequence of compactly supported cohomology of
the module localization sequence `0 → jV_! jV^* F → F → i_* i^* F → 0` on `U`
(`moduleLocalization_shortExact`), as in the lower row of Milne, *Lectures on Étale Cohomology*
v2.21, Thm. 14.7, proof, Step 2, p. 94. For the point scheme of a finite set `D` of points of `U`
that are closed in `X`, with separably closed residue fields, these groups vanish in positive
degree (`moduleLowerShriekDirectImage_subsingleton_of_sepClosed`).
-/

@[expose] public noncomputable section

universe w w' w'' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {U Z X : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU] (i : Z ⟶ U)
  [IsClosedImmersion (i ≫ jU)] (Λ : Type (u + 1)) [Ring Λ]
  [HasExt.{w} (ModuleSheaf X Λ)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} Z)]

/-- `Ext^q(Λ_X, jU_!(i_* M)) ≃+ H^q(Z, M₀)` among modules, for `i ≫ jU` a closed immersion. -/
def moduleLowerShriekDirectImageAddEquiv (M : ModuleSheaf Z Λ) (q : ℕ) :
    Ext.{w} (moduleUnit X Λ) ((moduleLowerShriek jU Λ).obj ((moduleDirectImage i Λ).obj M)) q ≃+
      Sheaf.H.{w''} ((SheafOfModules.toSheaf (constantRing Z Λ)).obj M) q :=
  (moduleLowerShriekCohomologyAddEquiv.{w, w'} jU Λ ((moduleDirectImage i Λ).obj M) q).trans
    ((((CompactSupport.functor.{w'} jU q).mapIso
        ((moduleDirectImageUnderlyingIso i Λ).app M)).addCommGroupIsoToAddEquiv).trans
      (CompactSupport.directImageAddEquiv jU i ((SheafOfModules.toSheaf (constantRing Z Λ)).obj M)
        q))

theorem moduleLowerShriekDirectImageAddEquiv_apply (M : ModuleSheaf Z Λ) (q : ℕ)
    (c : Ext.{w} (moduleUnit X Λ)
      ((moduleLowerShriek jU Λ).obj ((moduleDirectImage i Λ).obj M)) q) :
    moduleLowerShriekDirectImageAddEquiv.{w, w', w''} jU i Λ M q c =
      CompactSupport.directImageAddEquiv jU i ((SheafOfModules.toSheaf (constantRing Z Λ)).obj M) q
        (CompactSupport.H.map jU ((moduleDirectImageUnderlyingIso i Λ).hom.app M) q
          (moduleLowerShriekCohomologyAddEquiv.{w, w'} jU Λ ((moduleDirectImage i Λ).obj M) q c)) :=
  rfl

omit [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)] in
open Curves.FiniteClosedSupport in
/-- For the point scheme of a finite set `D` of points of `U` that are closed in `X`, with
separably closed residue fields, `Ext^q(Λ_X, jU_!(i_* M))` vanishes in positive degree. -/
theorem moduleLowerShriekDirectImage_subsingleton_of_sepClosed (D : Set U) (hfin : D.Finite)
    (hclosed : ∀ x ∈ D, IsClosed ({jU x} : Set X))
    (hsep : ∀ x : D, IsSepClosed (U.residueField x.val))
    (M : ModuleSheaf (pointScheme U D) Λ) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Ext.{w} (moduleUnit X Λ)
      ((moduleLowerShriek jU Λ).obj ((moduleDirectImage (inclusion U D) Λ).obj M)) q) := by
  let := CompactSupport.isClosedImmersion_inclusion_comp jU D hfin hclosed
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := HasExt.standard _
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (pointScheme U D)) := HasExt.standard _
  let : Subsingleton (Sheaf.H.{u + 2}
      ((SheafOfModules.toSheaf (constantRing (pointScheme U D) Λ)).obj M) q) :=
    subsingleton_H U D hfin hsep _ q hq
  exact (moduleLowerShriekDirectImageAddEquiv.{w, u + 2, u + 2} jU (inclusion U D) Λ M
    q).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology
