/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.CategoryTheory.Sites.Hypercohomology.ContinuousPullbackConstantTerminal
public import Aglib.CategoryTheory.Adjunction.ComparisonCoherence

/-! # Original constant sources of the Zariski--étale pullback square

The small-value Zariski source is identified with the original native
`constantPullbackIso`; the raised source remains the actual continuous-site
constant comparison. Terminal transport is explicit at both value sizes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Sheaf.Hypercohomology

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual inverse-image open of the terminal open is terminal. -/
def opensMapTopIsTerminal : IsTerminal ((Opens.map f.base).obj (⊤ : Y.Opens)) :=
  (isTerminalTop : IsTerminal (⊤ : Y.Opens)).isTerminalObj (Opens.map f.base)

/-- The small-value native continuous-site source uses exactly the original
Zariski constant-pullback map, including its terminal-open transport. -/
theorem opensPullbackConstantIntegerIso_eq :
    pullbackConstantIntegerIso.{u, u, u, u, u} (Opens.map f.base)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      ⊤ isTerminalTop (opensMapTopIsTerminal f) =
    (Scheme.Cohomology.constantPullbackIso f).app (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  have he : continuousDirectImageTerminalSectionsIso.{u, u, u, u, u}
      (Opens.map f.base)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      ⊤ (opensMapTopIsTerminal f) ⊤ isTerminalTop =
      Scheme.Cohomology.pushforwardSectionsIso f := by
    apply Iso.ext
    apply NatTrans.ext
    funext F
    change 𝟙 _ ≫ F.obj.map _ = F.obj.map _
    rw [Category.id_comp]
    congr 1
  apply Iso.ext
  have h := pullbackConstantIntegerIso_hom_eq_terminalComparison.{u, u, u, u, u}
    (Opens.map f.base) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    ⊤ isTerminalTop (opensMapTopIsTerminal f) ⊤ isTerminalTop
  rw [he] at h
  exact h

/-- The inverse source map in original small-value module cohomology is the
inverse of precisely the same native continuous-site comparison. -/
theorem opensPullbackConstantIntegerIso_inv :
    (pullbackConstantIntegerIso.{u, u, u, u, u} (Opens.map f.base)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      ⊤ isTerminalTop (opensMapTopIsTerminal f)).inv =
    (Scheme.Cohomology.constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  rw [opensPullbackConstantIntegerIso_eq]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
