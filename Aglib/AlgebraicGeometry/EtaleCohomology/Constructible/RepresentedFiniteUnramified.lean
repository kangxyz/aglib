/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.UnramifiedRepresentableLocus
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.RepresentedEtaleRestriction

/-! # Bounded abelian sheaves represented by finite unramified schemes

The original restricted Yoneda presheaf is represented on the small-etale
site by the actual etale locus. No flatness of the entire finite scheme is
asserted. Its locus is quasi-compact because the finite source over the
Noetherian base is Noetherian. The existing finite affine generators then
prove constructibility of the original bounded abelian coefficient.

The first application records its separated Noetherian base hypothesis; the
final affine-local result removes separatedness and global quasi-compactness.
No inverse-image claim for non-etale representables along closed
immersions, fibre-point/stalk identification, or new group-scheme model occurs.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- The actual etale locus of a finite scheme over a Noetherian base is
quasi-compact. This does not assert that the original finite map is etale. -/
theorem compactSpace_etaleLocus_of_isFinite
    {K S : Scheme.{u}} [IsNoetherian S] (f : K ⟶ S)
    [IsFinite f] : CompactSpace (f.etaleLocusObject).left := by
  let : IsLocallyNoetherian K := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace K := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian K := ⟨⟩
  change CompactSpace (f.etaleSourceOpen : Set K)
  let : TopologicalSpace.NoetherianSpace (f.etaleSourceOpen : Set K) :=
    TopologicalSpace.NoetherianSpace.set _
  exact TopologicalSpace.NoetherianSpace.compactSpace _

/-- A finite unramified scheme representing the underlying original small-etale
presheaf of a bounded abelian sheaf makes that same sheaf constructible.
The proof constructs the locus and its finite generator epimorphism; neither
constructibility nor an epimorphism is supplied as an extra hypothesis. -/
theorem isConstructible_of_represented_finite_unramified
    {K S : Scheme.{u}} [IsNoetherian S] [IsSeparated (terminal.from S)]
    (f : K ⟶ S) [IsFinite f] [FormallyUnramified f]
    (F : AbelianSheaf.{u, u + 1} S)
    (e : (Scheme.Etale.forget S).op ⋙ yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1} ≅
      F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})
    (n : ℕ) (hn : 0 < n) (hkill : KilledBy n F) : IsConstructible F := by
  let E := f.etaleLocusObject
  let : CompactSpace E.left := compactSpace_etaleLocus_of_isFinite f
  exact RepresentedEtaleTorsion.isConstructible_of_represented_etale E F
    (f.etaleLocusUliftYonedaIso ≪≫ e) n hkill hn

/-- Over a locally Noetherian base, the original etale locus of a finite
scheme is quasi-compact over that base, without global compactness of either. -/
theorem quasiCompact_etaleLocus_of_isFinite
    {K S : Scheme.{u}} [IsLocallyNoetherian S] (f : K ⟶ S)
    [IsFinite f] : QuasiCompact (f.etaleLocusObject).hom := by
  let : IsLocallyNoetherian K := LocallyOfFiniteType.isLocallyNoetherian f
  change QuasiCompact (f.etaleSourceOpen.ι ≫ f)
  infer_instance

/-- The same finite-unramified representation proves constructibility on any
locally Noetherian base. Only the actual etale locus is restricted to affine
opens; no general base-change formula for non-etale representables is used. -/
theorem isConstructible_of_represented_finite_unramified_of_locallyNoetherian
    {K S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : K ⟶ S) [IsFinite f] [FormallyUnramified f]
    (F : AbelianSheaf.{u, u + 1} S)
    (e : (Scheme.Etale.forget S).op ⋙ yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1} ≅
      F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})
    (n : ℕ) (hn : 0 < n) (hkill : KilledBy n F) : IsConstructible F := by
  let E := f.etaleLocusObject
  let : QuasiCompact E.hom := quasiCompact_etaleLocus_of_isFinite f
  exact RepresentedEtaleRestriction.isConstructible_of_quasiCompact_etale_represented E F
    (f.etaleLocusUliftYonedaIso ≪≫ e) n hn hkill

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
