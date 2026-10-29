/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekDirectImage

/-!
# Tests for compactly supported cohomology of a direct image from a closed part

The examples take open immersions `jV : V ⟶ U`, `jU : U ⟶ X`, `Λ = ULift (ZMod n)` and a finite
set `D` of points of `U` closed in `X`: the third term `H^q_c(U, i_* i^* F)` of the module
localization sequence on `U` is `H^q(pointScheme U D, i^* F)` and vanishes for `q > 0`. They
guard the axioms of every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteClosedSupport

universe u

namespace AglibTest.EtaleDualityLowerShriekDirectImage

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU] (n : ℕ) (D : Set U)
  (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({jU x} : Set X))
  (hsep : ∀ x : D, IsSepClosed (U.residueField x.val))

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y) :=
  HasExt.standard _

/-- The third term of the module localization sequence on `U`, through the point scheme. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek jU _).obj ((moduleDirectImage (inclusion U D) _).obj
          ((moduleInverseImage (inclusion U D) _).obj F))) q ≃+
      Sheaf.H.{u + 2} ((SheafOfModules.toSheaf (constantRing (pointScheme U D)
        (ULift.{u + 1} (ZMod n)))).obj ((moduleInverseImage (inclusion U D) _).obj F)) q :=
  letI := CompactSupport.isClosedImmersion_inclusion_comp jU D hfin hclosed
  moduleLowerShriekDirectImageAddEquiv.{u + 2, u + 2, u + 2} jU (inclusion U D) _ _ q

/-- It vanishes in positive degree. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek jU _).obj ((moduleDirectImage (inclusion U D) _).obj
        ((moduleInverseImage (inclusion U D) _).obj F))) q) :=
  moduleLowerShriekDirectImage_subsingleton_of_sepClosed jU _ D hfin hclosed hsep _ q hq

end AglibTest.EtaleDualityLowerShriekDirectImage

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekDirectImageAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekDirectImageAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekDirectImageAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekDirectImageAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekDirectImage_subsingleton_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekDirectImage_subsingleton_of_sepClosed
