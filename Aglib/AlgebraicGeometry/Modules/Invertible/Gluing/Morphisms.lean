/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Sheaf
public import Aglib.AlgebraicGeometry.Modules.InternalHom

/-!
# Actual morphisms from a glued line module

Compatible local target sections determine a morphism from the actual module sheaf of a
unit cocycle. The construction uses the existing structure-linear internal-Hom sheaf and
its original local scalar-multiplication maps. The transition equation and local evaluation
are retained exactly.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
  (c : UnitCocycle U) (M : X.Modules)

/-- A global section of the original internal Hom sheaf gives the actual global module
morphism, by evaluating it on every original open. -/
def homOfGlobalInternalSection
    (s : (InternalHom.sheaf X c.sheaf M).val.obj (op ⊤)) : c.sheaf ⟶ M :=
  ⟨_root_.PresheafOfModules.homMk
    { app V := s.val.app (op (Over.mk (homOfLE (le_top : V.unop ≤ ⊤))))
      naturality {V W} f := by
        let g : Over.mk (homOfLE (le_top : W.unop ≤ ⊤)) ⟶
            Over.mk (homOfLE (le_top : V.unop ≤ ⊤)) := Over.homMk f.unop
        exact s.val.naturality g.op }
    (by
      intro V r x
      exact s.property (op (Over.mk (homOfLE (le_top : V.unop ≤ ⊤)))) r x)⟩

/-- A local section of the target defines the original local coefficient homomorphism
using the canonical unit trivialization of the glued source. -/
def localHomSection (i : ι) (m : Γ(M, U i)) :
    (InternalHom.sheaf X c.sheaf M).val.obj (op (U i)) :=
  (InternalHom.sectionHomEquiv X c.sheaf M (U i)).symm
    ((c.localIso i).hom ≫
      InternalHom.sectionHomEquiv X (SheafOfModules.unit X.ringCatSheaf) M (U i)
        (InternalHom.sectionFromUnit X M (U i) m))

/-- Each local coefficient map is multiplication by the original restricted target section. -/
theorem localHomSection_apply (i : ι) (m : Γ(M, U i)) (V : (Over (U i))ᵒᵖ)
    (s : c.sheaf.val.obj (op V.unop.left)) :
    (c.localHomSection M i m).val.app V s =
      c.localSectionsEquiv i (leOfHom V.unop.hom) s • M.val.map V.unop.hom.op m := rfl

/-- The original cocycle compatibility of local target sections gives actual matching
sections of the existing internal-Hom sheaf. -/
theorem localHomSection_compatible (m : ∀ i, Γ(M, U i))
    (hm : ∀ (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      M.val.map (homOfLE hj).op (m j) =
        (c.transitionOn i j hi hj).val • M.val.map (homOfLE hi).op (m i)) :
    TopCat.Presheaf.IsCompatible (InternalHom.sheaf X c.sheaf M).val.presheaf U
      (fun i => c.localHomSection M i (m i)) := by
  intro i j
  apply Subtype.ext
  change (_ : InternalHom.RawHom X c.sheaf M (U i ⊓ U j)) = _
  ext V s
  let hi : V.unop.left ≤ U i := (leOfHom V.unop.hom).trans inf_le_left
  let hj : V.unop.left ≤ U j := (leOfHom V.unop.hom).trans inf_le_right
  change c.localSectionsEquiv i hi s • M.val.map (homOfLE hi).op (m i) =
    c.localSectionsEquiv j hj s • M.val.map (homOfLE hj).op (m j)
  rw [c.localSectionsEquiv_transition i j hi hj s, hm i j V.unop.left hi hj,
    mul_smul, smul_comm]

variable (hU : iSup U = ⊤) (m : ∀ i, Γ(M, U i))
  (hm : ∀ (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
    M.val.map (homOfLE hj).op (m j) =
      (c.transitionOn i j hi hj).val • M.val.map (homOfLE hi).op (m i))

include hU hm

/-- The actual internal-Hom sheaf glues the compatible local coefficient maps uniquely. -/
theorem existsUnique_globalInternalSection :
    ∃! s : (InternalHom.sheaf X c.sheaf M).val.obj (op ⊤), ∀ i,
      (InternalHom.sheaf X c.sheaf M).val.map (homOfLE le_top).op s =
        c.localHomSection M i (m i) := by
  let F : X.Modules := InternalHom.sheaf X c.sheaf M
  let sf : ∀ i, F.presheaf.obj (op (U i)) := fun i => c.localHomSection M i (m i)
  have hsf : TopCat.Presheaf.IsCompatible F.presheaf U sf :=
    c.localHomSection_compatible M m hm
  exact TopCat.Sheaf.existsUnique_gluing' ⟨F.presheaf, F.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) (by rw [hU]) sf hsf

/-- The global internal-Hom section obtained from the original compatible local data. -/
def globalInternalSectionOfLocal : (InternalHom.sheaf X c.sheaf M).val.obj (op ⊤) :=
  Classical.choose (c.existsUnique_globalInternalSection M hU m hm)

/-- The glued section restricts to the original local coefficient homomorphism. -/
theorem globalInternalSectionOfLocal_restrict (i : ι) :
    (InternalHom.sheaf X c.sheaf M).val.map (homOfLE le_top).op
        (c.globalInternalSectionOfLocal M hU m hm) = c.localHomSection M i (m i) :=
  (Classical.choose_spec (c.existsUnique_globalInternalSection M hU m hm)).1 i

/-- Compatible local target sections construct an actual global morphism from the original
glued line module, with no gluing-existence hypothesis. -/
def homOfLocalSections : c.sheaf ⟶ M :=
  c.homOfGlobalInternalSection M (c.globalInternalSectionOfLocal M hU m hm)

/-- The constructed global morphism has the exact original local scalar-multiplication
formula on every subopen of every displayed chart. -/
theorem homOfLocalSections_apply (i : ι) (V : X.Opens) (hi : V ≤ U i)
    (s : c.sheaf.val.obj (op V)) :
    (c.homOfLocalSections M hU m hm).val.app (op V) s =
      c.localSectionsEquiv i hi s • M.val.map (homOfLE hi).op (m i) := by
  have h := congrArg (fun t : (InternalHom.sheaf X c.sheaf M).val.obj (op (U i)) =>
    t.val.app (op (Over.mk (homOfLE hi))) s)
      (c.globalInternalSectionOfLocal_restrict M hU m hm i)
  change (c.homOfLocalSections M hU m hm).val.app (op V) s =
    (c.localHomSection M i (m i)).val.app (op (Over.mk (homOfLE hi))) s at h
  exact h.trans (c.localHomSection_apply M i (m i) (op (Over.mk (homOfLE hi))) s)

/-- The standard local generator is sent to the originally supplied target section. -/
theorem homOfLocalSections_generator (i : ι) :
    (c.homOfLocalSections M hU m hm).val.app (op (U i))
        ((c.localSectionsEquiv i le_rfl).symm (1 : Γ(X, U i))) = m i := by
  rw [c.homOfLocalSections_apply M hU m hm i (U i) le_rfl,
    LinearEquiv.apply_symm_apply, one_smul]
  change M.presheaf.map (𝟙 (op (U i))) (m i) = m i
  rw [M.presheaf.map_id]
  rfl

end AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle
