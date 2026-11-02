/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Generators.Pullback

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

example (U : X.Opens) :
    (Scheme.Modules.pullback p).obj (Scheme.Modules.openFree X U) ≅
      Scheme.Modules.openFree Y (p ⁻¹ᵁ U) :=
  Scheme.Modules.openFreePullbackIso p U

example : Scheme.Modules.openFreeFunctor X ⋙ Scheme.Modules.pullback p ≅
    Opens.map p.base ⋙ Scheme.Modules.openFreeFunctor Y :=
  Scheme.Modules.openFreePullbackNatIso p

example {U V : X.Opens} (i : U ⟶ V) :
    (Scheme.Modules.pullback p).map ((Scheme.Modules.openFreeFunctor X).map i) ≫
        (Scheme.Modules.openFreePullbackIso p V).hom =
      (Scheme.Modules.openFreePullbackIso p U).hom ≫
        (Scheme.Modules.openFreeFunctor Y).map ((Opens.map p.base).map i) :=
  Scheme.Modules.openFreePullbackIso_naturality p i

example (U : X.Opens) (M : Y.Modules)
    (f : Scheme.Modules.openFree Y (p ⁻¹ᵁ U) ⟶ M) :
    Scheme.Modules.openFreeHomEquiv X U ((Scheme.Modules.pushforward p).obj M)
        ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _
          ((Scheme.Modules.openFreePullbackIso p U).hom ≫ f)) =
      Scheme.Modules.openFreeHomEquiv Y (p ⁻¹ᵁ U) M f :=
  Scheme.Modules.openFreePullbackIso_homEquiv p U M f

/--
info: 'AlgebraicGeometry.Scheme.Modules.openFreePullbackNatIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.openFreePullbackNatIso
