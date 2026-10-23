/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AffineVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiBasis
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ContinuousComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Injectives

/-! # Original all-scheme Zariski--étale comparison for quasi-coherent coefficients

The comparison is the canonical original Ext map induced by exact inverse
image and its counit. Actual affine represented acyclicity proves bijectivity
using all small affine-open covers. No separatedness or quasi-compactness is
required. The map itself is defined for every additive sheaf and is natural
for arbitrary additive coefficient arrows.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open CategoryTheory.Sheaf.BasisAcyclicity

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u})

/-- The actual full open remains terminal in the original small étale site. -/
def opensToEtaleTopIsTerminal : IsTerminal ((opensToEtale X).obj ⊤) :=
  (isLimitMapConeEmptyConeEquiv (opensToEtale X) ⊤).1
    (isLimitOfPreserves (opensToEtale X) (isTerminalTop (α := X.Opens)))

variable [HasExt.{e} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1})]
  [HasExt.{e'} (AbelianSheaf.{u, u + 1} X)]

/-- The original comparison, defined on every actual additive étale coefficient. -/
abbrev zariskiRestrictionCohomologyMap (A : AbelianSheaf.{u, u + 1} X) (n : ℕ) :
    Sheaf.H.{e} ((zariskiRestriction X).obj A) n →+ Sheaf.H.{e'} A n :=
  continuousCohomologyMap.{u, u, u + 1, u, u + 1, e, e'} (opensToEtale X)
    (Opens.grothendieckTopology X) (smallEtaleTopology X) ⊤ isTerminalTop
    (opensToEtaleTopIsTerminal X) A n

/-- Naturality includes arbitrary additive maps such as the principal Frobenius. -/
theorem zariskiRestrictionCohomologyMap_naturality
    {A A' : AbelianSheaf.{u, u + 1} X} (f : A ⟶ A') (n : ℕ)
    (x : Sheaf.H.{e} ((zariskiRestriction X).obj A) n) :
    zariskiRestrictionCohomologyMap X A' n
      (Sheaf.H.map ((zariskiRestriction X).map f) n x) =
    Sheaf.H.map f n (zariskiRestrictionCohomologyMap X A n x) :=
  continuousCohomologyMap_naturality.{u, u, u + 1, u, u + 1, e, e'}
    (opensToEtale X)
    (Opens.grothendieckTopology X) (smallEtaleTopology X) ⊤ isTerminalTop
    (opensToEtaleTopIsTerminal X) f n x

/-- Actual quasi-coherent affine acyclicity makes the original comparison
bijective on every scheme, using arbitrary small affine-open covers. -/
theorem zariskiRestrictionCohomologyMap_bijective (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) : Function.Bijective
      (zariskiRestrictionCohomologyMap X (additiveCoefficient X F) n) := by
  let : EnoughInjectives (AbelianSheaf.{u, u + 1} X) :=
    Sheaf.LargeCohomology.enoughInjectivesLarge (smallEtaleTopology X)
  apply continuousCohomologyMap_bijective.{u, u, u + 1, u, u + 1, e, e', u}
    (opensToEtale X)
    (Opens.grothendieckTopology X) (smallEtaleTopology X) ⊤ isTerminalTop
    (opensToEtaleTopIsTerminal X) IsAffineOpen (exists_affineOpen_covering_family X)
    (injectiveResolution (additiveCoefficient X F))
  intro W hW q x
  let : IsAffine ((opensToEtale X).obj W).left := hW
  exact affineObject_ext_eq_zero X F ((opensToEtale X).obj W) q x

/-- The all-degree comparison retains the canonical original map as its forward map. -/
def zariskiRestrictionCohomologyAddEquiv (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Sheaf.H.{e} ((zariskiRestriction X).obj (additiveCoefficient X F)) n ≃+
      Sheaf.H.{e'} (additiveCoefficient X F) n :=
  AddEquiv.ofBijective (zariskiRestrictionCohomologyMap X (additiveCoefficient X F) n)
    (zariskiRestrictionCohomologyMap_bijective X F n)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
