/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.Allowed
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! # The original colimit of the allowed annihilator kernels

The canonical map induced by the actual kernel inclusions is mono by exactness
of filtered colimits and locally epi by allowed local torsion. Its isomorphism
is natural in the original coefficient sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] (M : Submonoid ℕ)

/-- The map to the original sheaf induced by its original allowed annihilator inclusions. -/
def allowedAnnihilatorColimitMap (F : Sheaf J AddCommGrpCat.{w}) :
    colimit (allowedAnnihilatorDiagram M F) ⟶ F :=
  colimit.desc _ (allowedAnnihilatorCocone M F)

/-- Every colimit leg recovers the original native kernel inclusion. -/
@[reassoc]
theorem allowedAnnihilatorColimitMap_ι (F : Sheaf J AddCommGrpCat.{w})
    (n : AllowedAnnihilatorIndex M) :
    colimit.ι (allowedAnnihilatorDiagram M F) n ≫ allowedAnnihilatorColimitMap M F =
      annihilatorι F n.val := colimit.ι_desc _ _

/-- Filtered exactness makes the original allowed-annihilator colimit map mono. -/
theorem allowedAnnihilatorColimitMap_mono (F : Sheaf J AddCommGrpCat.{w}) :
    Mono (allowedAnnihilatorColimitMap M F) := by
  let : IsConnected (AllowedAnnihilatorIndex M) := IsFiltered.isConnected _
  have : ∀ n : AllowedAnnihilatorIndex M, Mono ((allowedAnnihilatorCocone M F).ι.app n) :=
    fun n => annihilatorι_mono F n.val
  have : Mono (allowedAnnihilatorCocone M F).ι := NatTrans.mono_of_mono_app _
  let : HasFilteredColimitsOfSize.{0, 0} AddCommGrpCat.{w} :=
    hasFilteredColimitsOfSize_of_univLE.{0, 0, w, w}
  let : AB5OfSize.{0, 0} AddCommGrpCat.{w} := AB5OfSize_of_univLE.{0, 0, w, w} _
  apply colim.map_mono' (allowedAnnihilatorCocone M F).ι
    (colimit.isColimit _) (isColimitConstCocone (AllowedAnnihilatorIndex M) F)
  intro n
  change colimit.ι (allowedAnnihilatorDiagram M F) n ≫
      allowedAnnihilatorColimitMap M F = annihilatorι F n.val ≫ 𝟙 F
  rw [Category.comp_id]
  exact allowedAnnihilatorColimitMap_ι M F n

/-- Allowed local annihilators give literal local preimages in the original colimit. -/
theorem allowedAnnihilatorColimitMap_isLocallySurjective
    (F : Sheaf J AddCommGrpCat.{w})
    (hF : Presheaf.IsLocallyAllowedTorsion M J F.obj) :
    Presheaf.IsLocallySurjective J (allowedAnnihilatorColimitMap M F).hom := by
  constructor
  intro U s
  apply J.superset_covering ?_ (hF U s)
  rintro V f ⟨n, hn, hm, hs⟩
  let a := annihilatorSection F n V (F.obj.map f.op s) hs
  let i : AllowedAnnihilatorIndex M := ⟨n, hn, hm⟩
  refine ⟨(colimit.ι (allowedAnnihilatorDiagram M F) i).hom.app (op V) a, ?_⟩
  change (colimit.ι (allowedAnnihilatorDiagram M F) i ≫
      allowedAnnihilatorColimitMap M F).hom.app (op V) a = F.obj.map f.op s
  rw [allowedAnnihilatorColimitMap_ι]
  exact annihilatorSection_ι F n V (F.obj.map f.op s) hs

/-- The original allowed-annihilator colimit map of an allowed-torsion sheaf is epi. -/
theorem allowedAnnihilatorColimitMap_epi (F : Sheaf J AddCommGrpCat.{w})
    (hF : Presheaf.IsLocallyAllowedTorsion M J F.obj) :
    Epi (allowedAnnihilatorColimitMap M F) := by
  let := allowedAnnihilatorColimitMap_isLocallySurjective M F hF
  infer_instance

/-- Allowed local torsion is presented by the original allowed annihilator kernels. -/
def allowedAnnihilatorColimitIso (F : Sheaf J AddCommGrpCat.{w})
    (hF : Presheaf.IsLocallyAllowedTorsion M J F.obj) :
    colimit (allowedAnnihilatorDiagram M F) ≅ F := by
  let := allowedAnnihilatorColimitMap_mono M F
  let := allowedAnnihilatorColimitMap_epi M F hF
  have := isIso_of_mono_of_epi (allowedAnnihilatorColimitMap M F)
  exact asIso (allowedAnnihilatorColimitMap M F)

/-- The isomorphism's forward arrow is exactly the map induced by the original inclusions. -/
theorem allowedAnnihilatorColimitIso_hom (F : Sheaf J AddCommGrpCat.{w})
    (hF : Presheaf.IsLocallyAllowedTorsion M J F.obj) :
    (allowedAnnihilatorColimitIso M F hF).hom = allowedAnnihilatorColimitMap M F := rfl

/-- The original cocone is a colimit, retaining its designated original coefficient object. -/
def allowedAnnihilatorCoconeIsColimit (F : Sheaf J AddCommGrpCat.{w})
    (hF : Presheaf.IsLocallyAllowedTorsion M J F.obj) :
    IsColimit (allowedAnnihilatorCocone M F) :=
  IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (allowedAnnihilatorColimitIso M F hF)
      (fun n => allowedAnnihilatorColimitMap_ι M F n))

/-- The original colimit map is natural for every original coefficient morphism. -/
@[reassoc]
theorem allowedAnnihilatorColimitMap_naturality {F G : Sheaf J AddCommGrpCat.{w}}
    (q : F ⟶ G) :
    colim.map (allowedAnnihilatorCoefficientMap M q) ≫ allowedAnnihilatorColimitMap M G =
      allowedAnnihilatorColimitMap M F ≫ q := by
  apply colimit.hom_ext
  intro n
  rw [colimit.ι_map_assoc, allowedAnnihilatorColimitMap_ι,
    allowedAnnihilatorColimitMap_ι_assoc]
  exact allowedAnnihilatorCoefficientMap_ι M q n

end CategoryTheory.Sheaf
