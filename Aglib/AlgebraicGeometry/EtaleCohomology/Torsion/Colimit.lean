/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Basic
public import Aglib.CategoryTheory.Sites.Torsion.Colimit

/-!
# The actual bounded-torsion presentation on an etale site

For every scheme, an internally torsion abelian etale sheaf is the filtered
colimit of its actual native multiplication kernels at positive factorial
exponents. All native sheafification and size premises are discharged at the
standard coefficient universe. The maps are the original kernel inclusions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- The actual filtered annihilator presentation of any torsion abelian etale sheaf. -/
def torsionFilteredColimitIso {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsTorsion X F) : colimit (Sheaf.factorialAnnihilatorDiagram F) ≅ F :=
  Sheaf.factorialAnnihilatorColimitIso F hF

/-- The original inclusions give a colimit cocone, with no additional geometric premise. -/
def torsionFilteredColimitIsColimit {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    IsColimit (Sheaf.factorialAnnihilatorCocone F) :=
  Sheaf.factorialAnnihilatorCoconeIsColimit F hF

/-- Every stage maps into the original sheaf through its literal multiplication kernel. -/
theorem torsionFilteredColimitIso_ι {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) (n : ℕ) :
    colimit.ι (Sheaf.factorialAnnihilatorDiagram F) n ≫
        (torsionFilteredColimitIso F hF).hom =
      Sheaf.annihilatorι F (n + 1).factorial :=
  Sheaf.factorialAnnihilatorColimitMap_ι F n

end AlgebraicGeometry.Scheme.EtaleCohomology
