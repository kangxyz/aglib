/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.Prestack
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Descent of the actual pullback sections of a quasi-coherent module

The native quasi-coherent prestack gives descent of morphisms from the structure
module. Evaluation on one identifies its values with global sections of the
actual pullback module, also for nonaffine test schemes. This construction uses
no tensor description of sections on a nonaffine scheme.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite Bicategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u})

/-- The actual structure module as an object of the native quasi-coherent category. -/
def unitObject : quasicoherentPseudofunctor.obj (.mk (op X)) :=
  ⟨SheafOfModules.unit X.ringCatSheaf, isQuasicoherent_unit X⟩

/-- A native quasi-coherent module, without a finiteness or flatness assumption. -/
def moduleObject (F : X.Modules) [F.IsQuasicoherent] :
    quasicoherentPseudofunctor.obj (.mk (op X)) := ⟨F, show F.IsQuasicoherent from inferInstance⟩

variable (F : X.Modules) [F.IsQuasicoherent]

/-- The native presheaf of morphisms from the pulled-back structure module. -/
def homPresheaf : (Over X)ᵒᵖ ⥤ Type u :=
  quasicoherentPseudofunctor.presheafHom (unitObject X) (moduleObject X F)

/-- Actual fpqc descent of these morphisms, supplied by the native prestack. -/
theorem homPresheaf_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over X) (homPresheaf X F) :=
  Pseudofunctor.IsPrestack.isSheaf _ _ _

/-- Actual fppf descent of these morphisms. -/
theorem homPresheaf_isSheaf_fppf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over X) (homPresheaf X F) :=
  Pseudofunctor.IsPrestack.isSheaf _ _ _

/-- Forgetting the full-subcategory wrapper preserves exactly the native module morphism. -/
def homPresheafObjEquiv (T : Over X) :
    (homPresheaf X F).obj (op T) ≃
      ((pullback T.hom).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        (pullback T.hom).obj F) where
  toFun h := h.hom
  invFun h := ObjectProperty.homMk h
  left_inv _ := rfl
  right_inv _ := rfl

/-- Evaluation on one after the original pullback-unit comparison. -/
def sectionsEquiv (T : Over X) :
    (homPresheaf X F).obj (op T) ≃ Γ((pullback T.hom).obj F, ⊤) :=
  (homPresheafObjEquiv X F T).trans
    ((Iso.homFromEquiv (pullbackUnitIso T.hom)).trans
      (unitHomGlobalSectionsEquiv T.left ((pullback T.hom).obj F)))

/-- The section equivalence uses the inverse of the original pullback-unit isomorphism. -/
theorem sectionsEquiv_apply (T : Over X) (h : (homPresheaf X F).obj (op T)) :
    sectionsEquiv X F T h =
      unitHomGlobalSectionsEquiv T.left ((pullback T.hom).obj F)
        ((pullbackUnitIso T.hom).inv ≫ h.hom) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
