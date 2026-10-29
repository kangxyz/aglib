/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.PresheafTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionsDescent

/-! # Native restrictions of quasi-coherent pullback sections -/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite Bicategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Transport the values of a Type-valued functor through specified equivalences. -/
abbrev transportTypeFunctor := @CategoryTheory.PresheafTransport.transportTypeFunctor

/-- The specified value equivalences give the natural transport isomorphism. -/
abbrev transportTypeFunctorIso := @CategoryTheory.PresheafTransport.transportTypeFunctorIso

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

/-- The presheaf whose values are the actual global sections of pullbacks.
Its restrictions are transported from the original prestack restriction maps. -/
def sectionsPresheaf : (Over X)ᵒᵖ ⥤ Type u :=
  transportTypeFunctor (homPresheaf X F)
    (fun T => Γ((pullback T.unop.hom).obj F, ⊤))
    (fun T => sectionsEquiv X F T.unop)

/-- The native Hom-to-section equivalences constitute a natural isomorphism. -/
def homSectionsIso : homPresheaf X F ≅ sectionsPresheaf X F :=
  transportTypeFunctorIso (homPresheaf X F) _ (fun T => sectionsEquiv X F T.unop)

/-- The actual pullback-section presheaf satisfies fpqc descent. -/
theorem sectionsPresheaf_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over X) (sectionsPresheaf X F) :=
  (Presheaf.isSheaf_of_iso_iff (homSectionsIso X F)).1 (homPresheaf_isSheaf_fpqc X F)

/-- The actual pullback-section presheaf satisfies fppf descent. -/
theorem sectionsPresheaf_isSheaf_fppf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over X) (sectionsPresheaf X F) :=
  (Presheaf.isSheaf_of_iso_iff (homSectionsIso X F)).1 (homPresheaf_isSheaf_fppf X F)

/-- The original pullback of a section, expressed by its unit-module morphism. -/
def nativeSectionPullback {U V : Scheme.{u}} (f : U ⟶ V) (M : V.Modules)
    (s : Γ(M, ⊤)) : Γ((pullback f).obj M, ⊤) :=
  unitHomGlobalSectionsEquiv U ((pullback f).obj M)
    ((pullbackUnitIso f).inv ≫
      (pullback f).map ((unitHomGlobalSectionsEquiv V M).symm s))

/-- The original unit coherence, in the direction used when evaluating sections. -/
theorem pullbackUnitIso_inv_comp {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    (pullbackUnitIso (f ≫ g)).inv ≫
        (pullbackComp f g).inv.app (SheafOfModules.unit W.ringCatSheaf) =
      (pullbackUnitIso f).inv ≫ (pullback f).map (pullbackUnitIso g).inv :=
  Scheme.Modules.pullbackUnitIso_inv_comp f g

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
