/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSigmaSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleSliceCohomology
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.FiniteCoproduct

/-!
# Original root-cohomology on a finite scheme coproduct

Actual section restrictions along the canonical component inclusions give a
finite coproduct of free-representable sources. Native Ext decomposition and
the actual geometric slice comparisons identify original root cohomology.
Source and component Ext universes are independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w w'

variable {ι : Type u} [Finite ι] (Y : ι → Scheme.{u})
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (∐ Y))]
  [∀ i, HasExt.{w'} (AbelianSheaf.{u, u + 1} (Y i))]

/-- Original root-cohomology decomposes over the actual finite component charts. -/
def rootsFiniteCoproductEquiv (n q : ℕ) :
    Sheaf.H.{w} (mu (∐ Y) n) q ≃+ ∀ i, Sheaf.H.{w'} (mu (Y i) n) q := by
  let : Fintype ι := Fintype.ofFinite ι
  let T : (∐ Y).Etale := Scheme.Etale.mk (𝟙 (∐ Y))
  let : ∀ U : (∐ Y).Etale,
      HasExt.{u + 2} (Sheaf ((∐ Y).smallEtaleTopology.over U) AddCommGrpCat.{u + 1}) :=
    fun U => HasExt.standard _
  let : HasExt.{w} (AbelianSheaf.{u, u + 1} T.left) :=
    inferInstanceAs (HasExt.{w} (AbelianSheaf.{u, u + 1} (∐ Y)))
  let : ∀ i, HasExt.{w'} (AbelianSheaf.{u, u + 1} (Scheme.Etale.sigmaChart Y i).left) :=
    fun i => inferInstanceAs (HasExt.{w'} (AbelianSheaf.{u, u + 1} (Y i)))
  let e₀ := (rootsRepresentedCohomologyEquiv.{u, w, u + 2, w} T n q).symm
  let e₁ := Sheaf.LargeCohomology.finiteCoproductAddEquiv.{u + 1, u, u + 1, w, u}
    (∐ Y).smallEtaleTopology T (Scheme.Etale.sigmaChartInclusion Y)
    (Scheme.Etale.sigmaSections_bijective.{u, u + 1} Y) (mu (∐ Y) n) q
  let e₂ := AddEquiv.piCongrRight fun i =>
    rootsRepresentedCohomologyEquiv.{u, w, u + 2, w'} (Scheme.Etale.sigmaChart Y i) n q
  exact e₀.trans (e₁.trans e₂)

/-- Componentwise original root-cohomology vanishing implies vanishing on the actual coproduct. -/
theorem roots_subsingleton_of_finite_components (n q : ℕ)
    [∀ i, Subsingleton (Sheaf.H.{w'} (mu (Y i) n) q)] :
    Subsingleton (Sheaf.H.{w} (mu (∐ Y) n) q) :=
  (rootsFiniteCoproductEquiv Y n q).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
