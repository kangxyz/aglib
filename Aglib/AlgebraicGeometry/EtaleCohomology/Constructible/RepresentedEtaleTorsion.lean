/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.Representable
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Noetherian.StrongSerre
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.General
public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation.FiniteCover
public import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Constructibility from an original quasi-compact etale representing object

A finite affine open cover of the actual representing scheme supplies finitely
many sections of the original abelian sheaf. Their original positive-modulus
free generators surject onto that sheaf. No group structure is constructed on
the representing scheme, and no epimorphism or constructibility premise is used.
The separated Noetherian base hypothesis is explicit; affine bases are included.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.RepresentedEtaleTorsion

universe u
attribute [local instance] hasSheafifyLarge

variable {S : Scheme.{u}} (E : S.Etale) (F : AbelianSheaf.{u, u + 1} S)
  (e : uliftYoneda.{u + 1}.obj E ≅ F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})

/-- The identity of the same etale object gives the universal original section. -/
def universalSection : F.obj.obj (op E) := e.hom.app (op E) (ULift.up (𝟙 E))

/-- Restricting that section is exactly the specified representing bijection. -/
theorem universalSection_map {U : S.Etale} (a : U ⟶ E) :
    F.obj.map a.op (universalSection E F e) = e.hom.app (op U) (ULift.up a) := by
  have h := congrArg (fun q => TypeCat.Hom.hom q (ULift.up (𝟙 E)))
    (e.hom.naturality a.op)
  simpa [universalSection] using h.symm

/-- Equality on the universal section detects maps out of the original sheaf. -/
theorem hom_ext {G : AbelianSheaf.{u, u + 1} S} (a b : F ⟶ G)
    (h : a.hom.app (op E) (universalSection E F e) =
      b.hom.app (op E) (universalSection E F e)) : a = b := by
  ext U s
  let t := (e.inv.app U s).down
  have hs : F.obj.map t.op (universalSection E F e) = s := by
    rw [universalSection_map]
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app U) s
  rw [← hs]
  have ha : a.hom.app U (F.obj.map t.op (universalSection E F e)) =
      G.obj.map t.op (a.hom.app (op E) (universalSection E F e)) :=
    ConcreteCategory.congr_hom (a.hom.naturality t.op) (universalSection E F e)
  have hb : b.hom.app U (F.obj.map t.op (universalSection E F e)) =
      G.obj.map t.op (b.hom.app (op E) (universalSection E F e)) :=
    ConcreteCategory.congr_hom (b.hom.naturality t.op) (universalSection E F e)
  exact ha.trans ((congrArg (fun x => G.obj.map t.op x) h).trans hb.symm)

variable (n : ℕ) (hkill : KilledBy n F)

include hkill in
theorem killed_section (U : S.Etale) (s : F.obj.obj (op U)) : n • s = 0 := by
  have h := congrArg (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    hkill
  simp only [Functor.map_nsmul, Functor.map_zero] at h
  have h' := congrArg (fun q => q.app (op U)) h
  simp only [NatTrans.app_nsmul, NatTrans.app_zero] at h'
  simpa using ConcreteCategory.congr_hom h' s

/-- The original scalar quotient generator associated with a represented chart. -/
def generatorMap {U : S.Etale} (a : U ⟶ E) :
    freeZModRepresentable.{u + 1} S.smallEtaleTopology n U ⟶ F :=
  (freeZModSectionsEquiv.{u + 1} S.smallEtaleTopology n U F).symm
    ⟨F.obj.map a.op (universalSection E F e), killed_section F n hkill U _⟩

@[simp] theorem generatorMap_section {U : S.Etale} (a : U ⟶ E) :
    (freeZModSectionsEquiv.{u + 1} S.smallEtaleTopology n U F
      (generatorMap E F e n hkill a)).val =
        F.obj.map a.op (universalSection E F e) :=
  congrArg Subtype.val
    ((freeZModSectionsEquiv.{u + 1} S.smallEtaleTopology n U F).apply_symm_apply _)

local instance : HasFiniteBiproducts (AbelianSheaf.{u, u + 1} S) :=
  Abelian.hasFiniteBiproducts

section FiniteCover
variable {I : Type u} [Fintype I] (U : I → S.Etale) (a : ∀ i, U i ⟶ E)

/-- The actual finite sum of chart generators maps to the original coefficient. -/
def coverGeneratorMap :
    (⨁ fun i => freeZModRepresentable.{u + 1} S.smallEtaleTopology n (U i)) ⟶ F :=
  biproduct.desc (fun i => generatorMap E F e n hkill (a i))

/-- Covering the representing object proves epimorphy of the constructed map.
The proof uses separatedness of the target sheaf, not an epimorphism hypothesis. -/
theorem coverGeneratorMap_epi
    (hcover : Sieve.ofArrows U a ∈ S.smallEtaleTopology E) :
    Epi (coverGeneratorMap E F e n hkill U a) := by
  constructor
  intro G b c hbc
  apply hom_ext E F e b c
  apply G.isSeparated E _ hcover
  intro V g hg
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  have hmap : generatorMap E F e n hkill (a i) ≫ b =
      generatorMap E F e n hkill (a i) ≫ c := by
    have h := congrArg (fun q => biproduct.ι
      (fun i => freeZModRepresentable.{u + 1} S.smallEtaleTopology n (U i)) i ≫ q) hbc
    simpa [coverGeneratorMap, ← Category.assoc] using h
  have hsec := congrArg
    (fun q => (freeZModSectionsEquiv.{u + 1} S.smallEtaleTopology n (U i) G q).val) hmap
  simp only [freeZModSectionsEquiv_naturality, generatorMap_section] at hsec
  have hlocal : G.obj.map (a i).op (b.hom.app (op E) (universalSection E F e)) =
      G.obj.map (a i).op (c.hom.app (op E) (universalSection E F e)) := by
    have hb : b.hom.app (op (U i))
        (F.obj.map (a i).op (universalSection E F e)) =
        G.obj.map (a i).op (b.hom.app (op E) (universalSection E F e)) :=
      ConcreteCategory.congr_hom (b.hom.naturality (a i).op) (universalSection E F e)
    have hc : c.hom.app (op (U i))
        (F.obj.map (a i).op (universalSection E F e)) =
        G.obj.map (a i).op (c.hom.app (op E) (universalSection E F e)) :=
      ConcreteCategory.congr_hom (c.hom.naturality (a i).op) (universalSection E F e)
    exact hb.symm.trans (hsec.trans hc)
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
    congrArg (fun s => G.obj.map k.op s) hlocal

end FiniteCover

set_option backward.isDefEq.respectTransparency.types false in
open PositivePresentation in
include e hkill in
/-- A quasi-compact etale representing object makes the original bounded-torsion
abelian sheaf constructible over a separated Noetherian base. The representing
object need not be finite or carry any chosen group-scheme model. -/
theorem isConstructible_of_represented_etale
    [IsNoetherian S] [IsSeparated (terminal.from S)] [CompactSpace E.left]
    (hn : 0 < n) : IsConstructible F := by
  classical
  let C := E.left.affineCover.finiteSubcover
  let U (i : C.I₀) : S.Etale := Scheme.Etale.mk (C.f i ≫ E.hom)
  let a (i : C.I₀) : U i ⟶ E := MorphismProperty.Over.homMk (C.f i) rfl
  have hcover : Sieve.ofArrows U a ∈ S.smallEtaleTopology E := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨C.idx x, C.covers x⟩
  let q := coverGeneratorMap E F e n hkill U a
  have : Epi q := coverGeneratorMap_epi E F e n hkill U a hcover
  apply isConstructible_of_epi_of_noetherian q
  apply FiniteColimits.isConstructible_of_isColimit (Discrete.functor
    (fun i => freeZModRepresentable.{u + 1} S.smallEtaleTopology n (U i)))
      (biproduct.isColimit _) (fun i => ?_)
  have : IsAffine (U i.as).left := by
    change IsAffine (C.X i.as)
    dsimp only [C]
    rw [E.left.affineCover.finiteSubcover_X]
    exact Scheme.isAffine_affineCover _ _
  exact freeZModRepresentable_isConstructible_of_isAffine_of_isSeparated_of_isLocallyNoetherian
    (U i.as) n (ne_of_gt hn)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.RepresentedEtaleTorsion
