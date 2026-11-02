/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Trivial
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorClass

/-! # The original etale global-section vanishing criterion

The terminal section presents the same intrinsic global point. The based
free-sheaf map and both implications specialize the proved generic argument.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u w
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X}
variable (P : Torsor L) (s : P.carrier.obj.obj (op (etaleTerminal X)))

/-- A chosen global section extends the difference map to the free presheaf. -/
abbrev torsorBasedDifferencePresheaf : torsorFreePresheaf P ⟶ L.obj :=
  CategoryTheory.Sheaf.torsorBasedDifferencePresheaf P
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) P.carrier).symm s)

/-- The section-based extension restricts to the canonical kernel difference. -/
theorem torsorBasedDifferencePresheaf_kernel :
    torsorKernelInclusion P ≫ torsorBasedDifferencePresheaf P s = torsorKernelDifference P :=
  CategoryTheory.Sheaf.torsorBasedDifferencePresheaf_kernel P
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) P.carrier).symm s)

/-- The induced map from the actual free abelian sheaf. -/
abbrev torsorBasedDifferenceSheaf : torsorFreeSheaf P ⟶ L :=
  CategoryTheory.Sheaf.torsorBasedDifferenceSheaf P
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) P.carrier).symm s)

/-- The canonical kernel difference extends to the free sheaf when a section exists. -/
theorem torsorBasedDifferenceSheaf_kernel :
    torsorKernelSheafInclusion P ≫ torsorBasedDifferenceSheaf P s = torsorDifferenceSheafMap P :=
  CategoryTheory.Sheaf.torsorBasedDifferenceSheaf_kernel P
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) P.carrier).symm s)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

include s in
/-- A genuine global torsor section forces the canonical Ext class to vanish. -/
theorem torsorExtClass_eq_zero_of_section : torsorExtClass P = 0 :=
  CategoryTheory.Sheaf.torsorExtClass_eq_zero_of_globalPoint P
    ((Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) P.carrier).symm s)

theorem torsorExtClass_trivial (L : AbelianSheaf.{u, u + 1} X) :
    torsorExtClass (trivialTorsor L) = 0 :=
  CategoryTheory.Sheaf.torsorExtClass_trivial L

/-- The original terminal-section criterion, using the proved intrinsic classifier. -/
theorem torsorExtClass_eq_zero_iff_globalSection (h : Stacks03AJ.{u, w} X) :
    torsorExtClass P = 0 ↔ Nonempty (P.carrier.obj.obj (op (etaleTerminal X))) :=
  (fun _ : Stacks03AJ.{u, w} X =>
    (CategoryTheory.Sheaf.torsorExtClass_eq_zero_iff_globalPoint P).trans
      ⟨fun ⟨t⟩ => ⟨Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) P.carrier t⟩,
       fun ⟨t⟩ => ⟨(Topos.globalPointTerminalEquiv
         (etaleTerminalIsTerminal X) P.carrier).symm t⟩⟩) h

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3ce59431d712a763cfb629793a2451535c269edb5852b31de63d3f48b45aafae.
Definitions, hypotheses and universes are retained modulo native names. -/
