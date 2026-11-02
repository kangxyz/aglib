/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.ExtensionFiber
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorCohomology

/-! # The original etale extension fibre

The terminal etale object presents an intrinsic global element. The generic
producer uses that same element and retains the original fibre subtype,
restriction maps and positive additive kernel action.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}}

/-- Restriction of an actual global section of an abelian sheaf. -/
def restrictSection (F : AbelianSheaf.{u, u + 1} X)
    (z : F.obj.obj (op (etaleTerminal X))) (U : X.Etaleᵒᵖ) : F.obj.obj U :=
  F.obj.map ((etaleTerminalIsTerminal X).from U.unop).op z

theorem restrictSection_naturality (F : AbelianSheaf.{u, u + 1} X)
    (z : F.obj.obj (op (etaleTerminal X))) {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    F.obj.map f (restrictSection F z U) = restrictSection F z V := by
  have h : ((etaleTerminalIsTerminal X).from U.unop).op ≫ f =
      ((etaleTerminalIsTerminal X).from V.unop).op :=
    congrArg Quiver.Hom.op ((etaleTerminalIsTerminal X).hom_ext _ _)
  change F.obj.map f (F.obj.map ((etaleTerminalIsTerminal X).from U.unop).op z) = _
  rw [← Functor.map_comp_apply, h]
  rfl

variable (S : ShortComplex (AbelianSheaf.{u, u + 1} X))
variable (z : S.X₃.obj.obj (op (etaleTerminal X)))

/-- The original fibre condition, presented by its intrinsic global element. -/
abbrev extensionFiberSubfunctor : Subfunctor (underlyingSetSheaf S.X₂).obj :=
  CategoryTheory.Sheaf.extensionFiberSubfunctor S
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X)
      (underlyingSetSheaf S.X₃)).symm z)

/-- Every component has precisely the original terminal-restriction predicate. -/
@[simp] theorem extensionFiberSubfunctor_obj (U : X.Etaleᵒᵖ) :
    (extensionFiberSubfunctor S z).obj U =
      {s | S.g.hom.app U s = restrictSection S.X₃ z U} := rfl

/-- The original fibre presheaf is a sheaf by the generic local-equality proof. -/
theorem extensionFiber_isSheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (extensionFiberSubfunctor S z).toFunctor :=
  CategoryTheory.Sheaf.extensionFiber_isSheaf S
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X)
      (underlyingSetSheaf S.X₃)).symm z)

/-- The same fibre subtype sheaf on the actual etale site. -/
abbrev extensionFiberSheaf : SetSheaf X :=
  CategoryTheory.Sheaf.extensionFiberSheaf S
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X)
      (underlyingSetSheaf S.X₃)).symm z)

/-- Evaluation preserves the actual kernel of the original short exact sequence. -/
abbrev extensionSectionKernel (hS : S.ShortExact) (U : X.Etaleᵒᵖ) :
    IsLimit (KernelFork.ofι (S.f.hom.app U)
      (show S.f.hom.app U ≫ S.g.hom.app U = 0 from
        congrArg (fun q => q.hom.app U) S.zero)) :=
  CategoryTheory.Sheaf.extensionSectionKernel S hS U

/-- The original fibre with its same positive additive kernel action. -/
abbrev extensionFiberTorsor (hS : S.ShortExact) : Torsor S.X₁ :=
  CategoryTheory.Sheaf.extensionFiberTorsor S
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X)
      (underlyingSetSheaf S.X₃)).symm z) hS

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 e253e8aa107e7041b57acc328a4109a66c86deda16fe337e14e0fb62c6ec34f4.
Definitions, hypotheses and universes are retained modulo native names. -/
