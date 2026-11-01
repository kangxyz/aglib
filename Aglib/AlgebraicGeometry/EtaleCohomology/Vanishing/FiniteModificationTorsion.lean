/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.FiniteModification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.DirectImage

/-! # Finite-modification descent with an explicit torsion boundary bound

The original unit's literal cokernel and its actual closed restriction are
proved internally torsion. The supplied preceding-degree boundary theorem
is then applied to that coefficient before the existing finite-modification
descent. No geometric dimension theorem or boundary vanishing is assumed
implicitly, and no common annihilator is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u eX eY eZ

attribute [local instance] hasSheafifyLarge

/-- A genuine preceding-degree vanishing theorem for internally torsion
coefficients on the displayed boundary descends vanishing through the
original finite modification. The boundary input and all Ext sizes remain
explicit; no field, properness or dimension hypothesis is added. -/
theorem subsingleton_H_of_finiteModification_torsion
    {Y U Z X : Scheme.{u}} (c : Y ⟶ X) [IsFinite c] [Surjective c]
    (j : U ⟶ X) [IsOpenImmersion j] [IsIso (pullback.snd c j)]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) (n : ℕ)
    (hY : Subsingleton (Sheaf.H.{eY} ((inverseImage c).obj F) (n + 1)))
    (hZ : ∀ G : AbelianSheaf.{u, u + 1} Z, IsTorsion Z G →
      Subsingleton (Sheaf.H.{eZ} G n)) :
    Subsingleton (Sheaf.H.{eX} F (n + 1)) :=
  subsingleton_H_of_finiteModification c j i hcomp F n hY
    (hZ _ ((unit_cokernel_isTorsion c F hF).inverseImage i))

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
