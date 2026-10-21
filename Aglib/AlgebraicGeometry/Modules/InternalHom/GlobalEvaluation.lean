/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineSections

/-! # Literal evaluation of the original global Hom equivalence -/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u
variable {X : Scheme.{u}} (F G : X.Modules)

/-- Restricting the original global Hom section evaluates by the original
morphism component on every open, with no affine hypothesis. -/
theorem sectionEvaluation_globalHomEquiv (φ : F ⟶ G) (U : X.Opens) (m : Γ(F, U)) :
    sectionEvaluation X F G U
        ((sheaf X F G).val.map (homOfLE le_top : U ⟶ ⊤).op (globalHomEquiv X F G φ)) m =
      φ.app U m := rfl

/-- Evaluation of a global Hom section is the component of its actual inverse morphism. -/
theorem sectionEvaluation_globalHomEquiv_symm (t : Γ(sheaf X F G, ⊤))
    (U : X.Opens) (m : Γ(F, U)) :
    sectionEvaluation X F G U
        ((sheaf X F G).val.map (homOfLE le_top : U ⟶ ⊤).op t) m =
      ((globalHomEquiv X F G).symm t).app U m := rfl

end AlgebraicGeometry.Scheme.Modules.InternalHom
