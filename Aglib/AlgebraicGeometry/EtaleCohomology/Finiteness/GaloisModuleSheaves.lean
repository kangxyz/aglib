/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PGroupModuleSheaves
public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.FiniteEtaleDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisSylowCover

/-! # Proper module cohomology from an actual finite Galois trivialization

The original cover relative to its actual Sylow-subgroup quotient has a
p-group deck group. The original trivialization transports through the exact
original quotient triangle. Its cohomology is finite by p-group induction on
the actual proper intermediate scheme. Coprime rank and the original
module-linear trace retraction descend finite generation to the base.

This is a theorem for a supplied actual Galois trivialization by the literal
finite prime-killed module. It does not assume or assert the existence of such
a trivialization for arbitrary finite-type locally constant sheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Constructible.Modules

universe u r e

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {k : Type u} [Field k] [IsSepClosed k] (X : FScheme k) [IsProper X.hom]
  [ConnectedSpace X.left]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X.left)]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  (R : Type r) [CommRing R] [IsNoetherianRing R]

/-- Every supplied actual finite Galois trivialization by a finitely generated
literal module killed by the characteristic gives finite original module
cohomology in every degree on a proper scheme over a separably closed field.

The deck group need not be a p-group. The coefficient-ring and original Ext
universes remain independent, and the chosen module need not be finite as an
additive group. The intermediate quotient uses native standard Ext only. -/
theorem moduleSheaf_cohomology_finite_of_galois_trivialization
    (Y : Scheme.FiniteEtale X.left) [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
    [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (q : ℕ) (F : ModuleSheaf R X.left)
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Module.Finite R ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  let P : Sylow p (Aut Y) := Classical.choice inferInstance
  let Z₀ : Scheme.FiniteEtale X.left :=
    Scheme.FiniteEtale.galoisSubgroupQuotient Y P.toSubgroup
  let Z : FScheme k := Over.mk (Z₀.obj.hom ≫ X.hom)
  let V : Scheme.FiniteEtale Z.left :=
    Scheme.FiniteEtale.galoisSubgroupRelative Y P.toSubgroup
  have : ConnectedSpace Z.left :=
    inferInstanceAs (ConnectedSpace Z₀.obj.left)
  have : IsProper Z.hom :=
    inferInstanceAs (IsProper (Z₀.obj.hom ≫ X.hom))
  let hExtZ : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z₀.obj.left) := HasExt.standard _
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z.left) := hExtZ
  have : PreGaloisCategory.IsGalois V :=
    Scheme.FiniteEtale.galoisSubgroupRelative_isGalois Y P.toSubgroup
  have : Surjective V.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupRelative_surjective Y P.toSubgroup
  have : CompactSpace V.obj.left := inferInstanceAs (CompactSpace Y.obj.left)
  have : QuasiSeparatedSpace V.obj.left := inferInstanceAs (QuasiSeparatedSpace Y.obj.left)
  let E := (moduleInverseImage R Z₀.obj.hom).obj F
  have htriangle : V.obj.hom ≫ Z₀.obj.hom = Y.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupQuotientπ_structure Y P.toSubgroup
  let t' : (moduleInverseImage R V.obj.hom).obj E ≅
      (constantSheaf V.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
    ((moduleInverseImageComp R Z₀.obj.hom V.obj.hom).app F).symm ≪≫
      eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F) htriangle) ≪≫ t
  let HZ : ModuleSheaf R Z.left ⥤ ModuleCat.{u + 2} R :=
    ModuleCat.Sheaf.cohomology Z.left.smallEtaleTopology R q
  have hfinite : Module.Finite R (HZ.obj E) :=
    moduleSheaf_cohomology_finite_of_pGroup_trivialization Z p R V
      (Scheme.FiniteEtale.galoisSylowRelative_isPGroup Y P) q E M hM t'
  exact @moduleSheaf_cohomology_finite_of_finiteEtale_coprime R _ X.left Z₀
    inferInstance hExtZ P.toSubgroup.index
    (Scheme.FiniteEtale.galoisSubgroupQuotient_finrank Y P.toSubgroup) F p
    (Scheme.FiniteEtale.galoisSylow_index_coprime Y P)
    (moduleSheaf_nsmul_id_eq_zero_of_trivialization R Y.obj.hom F M p hM t) q hfinite

end AlgebraicGeometry.Scheme.EtaleCohomology
