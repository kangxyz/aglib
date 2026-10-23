/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Sheaf
public import Aglib.CategoryTheory.Sites.Torsion.Annihilator
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Torsion sheaves are filtered colimits of their actual annihilator subsheaves

Use the native kernel inclusions at the cofinal positive factorial exponents.
Their colimit map is always a monomorphism and is locally surjective when the
original sheaf is internally torsion. Its resulting isomorphism retains every
original annihilator inclusion and is natural in the coefficient sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]

/-- The canonical map from the actual filtered annihilator colimit to the original sheaf. -/
def factorialAnnihilatorColimitMap (F : Sheaf J AddCommGrpCat.{w}) :
    colimit (factorialAnnihilatorDiagram F) ⟶ F :=
  colimit.desc _ (factorialAnnihilatorCocone F)

/-- The canonical colimit map retains the literal original kernel inclusion at each stage. -/
@[reassoc]
theorem factorialAnnihilatorColimitMap_ι (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    colimit.ι (factorialAnnihilatorDiagram F) n ≫ factorialAnnihilatorColimitMap F =
      annihilatorι F (n + 1).factorial :=
  colimit.ι_desc _ _

/-- The actual annihilator colimit maps monomorphically into the original sheaf. -/
theorem factorialAnnihilatorColimitMap_mono (F : Sheaf J AddCommGrpCat.{w}) :
    Mono (factorialAnnihilatorColimitMap F) := by
  let : IsConnected ℕ := IsFiltered.isConnected ℕ
  have : ∀ n : ℕ, Mono ((factorialAnnihilatorCocone F).ι.app n) := by
    intro n
    change Mono (annihilatorι F (n + 1).factorial)
    infer_instance
  have : Mono (factorialAnnihilatorCocone F).ι :=
    NatTrans.mono_of_mono_app _
  let : HasFilteredColimitsOfSize.{0, 0} AddCommGrpCat.{w} :=
    hasFilteredColimitsOfSize_of_univLE.{0, 0, w, w}
  let : AB5OfSize.{0, 0} AddCommGrpCat.{w} :=
    AB5OfSize_of_univLE.{0, 0, w, w} _
  apply colim.map_mono' (factorialAnnihilatorCocone F).ι
    (colimit.isColimit _) (isColimitConstCocone ℕ F)
  intro n
  change colimit.ι (factorialAnnihilatorDiagram F) n ≫
      factorialAnnihilatorColimitMap F = annihilatorι F (n + 1).factorial ≫ 𝟙 F
  rw [Category.comp_id]
  exact factorialAnnihilatorColimitMap_ι F n

/-- Internal local torsion supplies actual local preimages in the filtered kernel colimit. -/
theorem factorialAnnihilatorColimitMap_isLocallySurjective
    (F : Sheaf J AddCommGrpCat.{w}) (hF : IsTorsion F) :
    Presheaf.IsLocallySurjective J (factorialAnnihilatorColimitMap F).hom := by
  constructor
  intro U s
  apply J.superset_covering ?_ (hF U s)
  intro V f hf
  obtain ⟨n, hn, hs⟩ := hf
  obtain ⟨k, hk⟩ := exists_dvd_factorialAnnihilatorExponent n hn
  have hkill : (k + 1).factorial • F.obj.map f.op s = 0 := by
    obtain ⟨m, hm⟩ := hk
    rw [hm, Nat.mul_comm n m, mul_smul, hs, nsmul_zero]
  let a := annihilatorSection F (k + 1).factorial V (F.obj.map f.op s) hkill
  refine ⟨(colimit.ι (factorialAnnihilatorDiagram F) k).hom.app (op V) a, ?_⟩
  change (colimit.ι (factorialAnnihilatorDiagram F) k ≫
      factorialAnnihilatorColimitMap F).hom.app (op V) a = F.obj.map f.op s
  rw [factorialAnnihilatorColimitMap_ι]
  exact annihilatorSection_ι F (k + 1).factorial V (F.obj.map f.op s) hkill

/-- The original filtered-colimit map of an internally torsion sheaf is epi. -/
theorem factorialAnnihilatorColimitMap_epi
    (F : Sheaf J AddCommGrpCat.{w}) (hF : IsTorsion F) :
    Epi (factorialAnnihilatorColimitMap F) := by
  let := factorialAnnihilatorColimitMap_isLocallySurjective F hF
  exact inferInstance

/-- An internally torsion sheaf is the actual filtered colimit of its bounded kernels. -/
def factorialAnnihilatorColimitIso (F : Sheaf J AddCommGrpCat.{w}) (hF : IsTorsion F) :
    colimit (factorialAnnihilatorDiagram F) ≅ F := by
  let := factorialAnnihilatorColimitMap_mono F
  let := factorialAnnihilatorColimitMap_epi F hF
  have := isIso_of_mono_of_epi (factorialAnnihilatorColimitMap F)
  exact asIso (factorialAnnihilatorColimitMap F)

/-- The colimit isomorphism is the original map induced by the original kernel inclusions. -/
theorem factorialAnnihilatorColimitIso_hom
    (F : Sheaf J AddCommGrpCat.{w}) (hF : IsTorsion F) :
    (factorialAnnihilatorColimitIso F hF).hom = factorialAnnihilatorColimitMap F := rfl

/-- The displayed positive stages are internally torsion for their original annihilators. -/
theorem factorialAnnihilatorDiagram_isTorsion
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    IsTorsion ((factorialAnnihilatorDiagram F).obj n) := by
  apply Presheaf.isLocallyTorsion_of_sectionwise
  intro U s
  refine ⟨(n + 1).factorial, Nat.factorial_pos _, ?_⟩
  have h := congrArg
    (fun q : (factorialAnnihilatorDiagram F).obj n ⟶
      (factorialAnnihilatorDiagram F).obj n => q.hom.app (op U) s)
    (factorialAnnihilatorDiagram_annihilated F n)
  exact h

/-- The original cocone into a torsion sheaf is a genuine filtered-colimit presentation. -/
def factorialAnnihilatorCoconeIsColimit
    (F : Sheaf J AddCommGrpCat.{w}) (hF : IsTorsion F) :
    IsColimit (factorialAnnihilatorCocone F) :=
  IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (factorialAnnihilatorColimitIso F hF)
      (fun n => factorialAnnihilatorColimitMap_ι F n))

/-- The canonical colimit map commutes with every actual coefficient morphism. -/
@[reassoc]
theorem factorialAnnihilatorColimitMap_naturality {F G : Sheaf J AddCommGrpCat.{w}}
    (q : F ⟶ G) :
    colim.map (factorialAnnihilatorCoefficientMap q) ≫ factorialAnnihilatorColimitMap G =
      factorialAnnihilatorColimitMap F ≫ q := by
  apply colimit.hom_ext
  intro n
  rw [colimit.ι_map_assoc, factorialAnnihilatorColimitMap_ι,
    factorialAnnihilatorColimitMap_ι_assoc]
  exact factorialAnnihilatorCoefficientMap_ι q n

end CategoryTheory.Sheaf
