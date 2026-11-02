/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSigmaSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceCohomology
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.TerminalFiniteCoproduct

/-! # Original cohomology on a finite coproduct of schemes

The actual section restrictions to the canonical component charts give a
finite coproduct of free-representable sources. Original represented Ext and
the actual étale-chart comparisons identify every original cohomology group,
for arbitrary coefficients and independent source/component Ext universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u e e'

attribute [local instance] hasSheafifyLarge

variable {ι : Type u} [Finite ι] (Y : ι → Scheme.{u})
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (∐ Y))]
  [∀ i, HasExt.{e'} (AbelianSheaf.{u, u + 1} (Y i))]

/-- Original cohomology of a finite scheme coproduct is the product of
original cohomology of the actual component inverse images. -/
def finiteCoproductCohomologyEquiv (F : AbelianSheaf.{u, u + 1} (∐ Y)) (q : ℕ) :
    Sheaf.H.{e} F q ≃+
      ∀ i, Sheaf.H.{e'} ((inverseImage (Sigma.ι Y i)).obj F) q := by
  let : Fintype ι := Fintype.ofFinite ι
  let : ∀ U : (∐ Y).Etale,
      HasExt.{u + 2} (Sheaf ((∐ Y).smallEtaleTopology.over U) AddCommGrpCat.{u + 1}) :=
    fun U => HasExt.standard _
  let : ∀ i, HasExt.{e'} (AbelianSheaf.{u, u + 1} (Scheme.Etale.sigmaChart Y i).left) :=
    fun i => inferInstanceAs (HasExt.{e'} (AbelianSheaf.{u, u + 1} (Y i)))
  let e₁ := Sheaf.LargeCohomology.terminalFiniteCoproductAddEquiv.{u + 1, u, u + 1, e, u}
    (∐ Y).smallEtaleTopology (etaleTerminalIsTerminal (∐ Y)) (Scheme.Etale.sigmaChartInclusion Y)
    (Scheme.Etale.sigmaSections_bijective.{u, u + 1} Y) F q
  let e₂ (i : ι) : Sheaf.LargeCohomology.H.{e, u + 1, u, u + 1}
      (∐ Y).smallEtaleTopology F q (Scheme.Etale.sigmaChart Y i) ≃+
        Sheaf.H.{e'} ((inverseImage (Sigma.ι Y i)).obj F) q := by
    let : HasExt.{e'} (AbelianSheaf.{u, u + 1} (Scheme.Etale.sigmaChart Y i).left) :=
      inferInstanceAs (HasExt.{e'} (AbelianSheaf.{u, u + 1} (Y i)))
    let : HasExt.{e'} (Sheaf
        ((𝟭 Scheme.{u}).obj (Scheme.Etale.sigmaChart Y i).left).smallEtaleTopology
          AddCommGrpCat.{u + 1}) :=
      inferInstanceAs (HasExt.{e'} (AbelianSheaf.{u, u + 1} (Y i)))
    exact originalCohomologyChartEquiv.{u, e, u + 2, e'} (Scheme.Etale.sigmaChart Y i) F q
  exact e₁.trans (AddEquiv.piCongrRight e₂)

/-- Componentwise original cohomology vanishing implies vanishing on the
actual finite scheme coproduct, including the empty coproduct. -/
theorem subsingleton_H_of_finite_components
    (F : AbelianSheaf.{u, u + 1} (∐ Y)) (q : ℕ)
    [∀ i, Subsingleton (Sheaf.H.{e'} ((inverseImage (Sigma.ι Y i)).obj F) q)] :
    Subsingleton (Sheaf.H.{e} F q) :=
  (finiteCoproductCohomologyEquiv Y F q).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
