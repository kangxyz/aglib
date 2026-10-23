/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.UniverseLift
public import Aglib.AlgebraicGeometry.Modules.Invertible.IsomorphismSheaf
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedCoefficients

/-!
# Quasi-coherent Hom descent on the actual small étale site

The inclusion of the small site into the over-site is continuous for the native
étale topologies. We first restrict fppf descent to the étale topology and then
restrict along that inclusion. Only coefficient values, not rings, are lifted.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite Bicategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

/-- Hom descent on the big étale over-site, obtained from actual fppf descent. -/
theorem homPresheaf_isSheaf_etale :
    Presheaf.IsSheaf (Scheme.etaleTopology.over X) (homPresheaf X F) := by
  let : quasicoherentPseudofunctor.{u}.IsPrestack Scheme.etaleTopology :=
    Pseudofunctor.IsPrestack.of_le _
      Modules.Invertible.EtaleDescent.etaleTopology_le_fppfTopology
  exact Pseudofunctor.IsPrestack.isSheaf _ _ _

/-- The native small étale restriction of the quasi-coherent Hom presheaf. -/
def etaleHomPresheaf : X.Etaleᵒᵖ ⥤ Type u :=
  (Scheme.Etale.forget X).op ⋙ homPresheaf X F

/-- Restriction to the native small étale site preserves descent. -/
theorem etaleHomPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (etaleHomPresheaf X F) := by
  exact (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.smallEtaleTopology X) (Scheme.etaleTopology.over X)
    (homPresheaf X F) (homPresheaf_isSheaf_etale X F)

/-- The actual Type-valued small étale coefficient at the standard value size. -/
def etaleHomSheaf : Sheaf (Scheme.smallEtaleTopology X) (Type (u + 1)) where
  obj := etaleHomPresheaf X F ⋙ uliftFunctor.{u + 1}
  property := by
    apply (isSheaf_iff_isSheaf_of_type _ _).2
    exact Presieve.isSheaf_comp_uliftFunctor _
      ((isSheaf_iff_isSheaf_of_type _ _).1 (etaleHomPresheaf_isSheaf X F))

/-- Evaluation on each étale object is the lifted space of actual pullback sections. -/
def etaleSectionsEquiv (T : X.Etale) :
    (etaleHomSheaf X F).obj.obj (op T) ≃
      ULift.{u + 1} Γ((pullback T.hom).obj F, ⊤) :=
  liftedSectionsEquiv X F ((Scheme.Etale.forget X).obj T)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
