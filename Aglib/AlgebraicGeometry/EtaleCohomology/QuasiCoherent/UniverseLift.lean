/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionsDescent

/-!
# Value-universe lift of quasi-coherent section descent

Only the values are lifted. The schemes and their original module sheaves remain
in their native universes. These are Type-valued sheaves; no ring coefficient,
module action or comparison of cohomology universes is postulated here.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

/-- The actual descent presheaf with its values lifted to the standard size. -/
def liftedHomPresheaf : (Over X)ᵒᵖ ⥤ Type (u + 1) :=
  homPresheaf X F ⋙ uliftFunctor.{u + 1}

/-- Lifting only values preserves the actual fpqc sheaf condition. -/
theorem liftedHomPresheaf_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over X) (liftedHomPresheaf X F) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  exact Presieve.isSheaf_comp_uliftFunctor _
    ((isSheaf_iff_isSheaf_of_type _ _).1 (homPresheaf_isSheaf_fpqc X F))

/-- Lifting only values preserves the actual fppf sheaf condition. -/
theorem liftedHomPresheaf_isSheaf_fppf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over X) (liftedHomPresheaf X F) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  exact Presieve.isSheaf_comp_uliftFunctor _
    ((isSheaf_iff_isSheaf_of_type _ _).1 (homPresheaf_isSheaf_fppf X F))

/-- The resulting fpqc sheaf, at value universe `u + 1`. -/
def liftedHomSheaf : Sheaf (Scheme.fpqcTopology.over X) (Type (u + 1)) :=
  ⟨liftedHomPresheaf X F, liftedHomPresheaf_isSheaf_fpqc X F⟩

/-- The values are genuinely lifted sections of the actual pullback module. -/
def liftedSectionsEquiv (T : Over X) :
    (liftedHomPresheaf X F).obj (op T) ≃
      ULift.{u + 1} Γ((pullback T.hom).obj F, ⊤) :=
  Equiv.ulift.trans ((sectionsEquiv X F T).trans Equiv.ulift.symm)

/-- Evaluation followed by `down` retains the original section equivalence. -/
@[simp]
theorem liftedSectionsEquiv_down (T : Over X)
    (s : (liftedHomPresheaf X F).obj (op T)) :
    (liftedSectionsEquiv X F T s).down = sectionsEquiv X F T s.down := rfl

/-- The lifted restriction is the original restriction after taking `down`. -/
@[simp]
theorem liftedHomPresheaf_map_down {T U : (Over X)ᵒᵖ} (f : T ⟶ U)
    (s : (liftedHomPresheaf X F).obj T) :
    ((liftedHomPresheaf X F).map f s).down = (homPresheaf X F).map f s.down := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
