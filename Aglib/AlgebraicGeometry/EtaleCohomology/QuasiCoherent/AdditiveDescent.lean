/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveSections

/-! # Big étale descent of the original additive pullback sections -/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

/-- The original lifted additive section presheaf is a sheaf on the big étale slice. -/
theorem additiveSectionsPresheaf_isSheaf_etale :
    Presheaf.IsSheaf (Scheme.etaleTopology.over X) (additiveSectionsPresheaf X F) :=
  CategoryTheory.PresheafTransport.liftAdditiveTransport_isSheaf
    (Scheme.etaleTopology.over X) (homPresheaf X F)
    (fun T => AddCommGrpCat.of Γ((Scheme.Modules.pullback T.hom).obj F, ⊤))
    (sectionsEquiv X F) (fun f => sectionsAddHom X F f)
    (fun f s => sectionsAddHom_apply X F f s)
    (homPresheaf_isSheaf_etale X F)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
