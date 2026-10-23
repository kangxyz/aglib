/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SpecSections
public import Aglib.Algebra.Homology.Amitsur.Positive
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# The actual algebraic Amitsur complex and pullback sections

The comparison is a natural isomorphism on all algebras before restricting to
Amitsur's original conerve. Thus every original coface, and not merely each term,
is preserved. This compares the algebraic conerve with its actual spectrum
sections; a separate geometric comparison with the site's Čech products is
still required for affine étale acyclicity.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct Simplicial

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Additive maps from a tensor product are determined on actual pure tensors. -/
theorem tensorSectionAddHom_ext {R M N Z : Type u} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup Z] [Module R M] [Module R N]
    (f g : M ⊗[R] N →+ Z) (h : ∀ m n, f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n)) : f = g := by
  ext s
  induction s using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add s t hs ht => simp only [map_add, hs, ht]

variable (R : Type u) [CommRing R] (F : (Spec (CommRingCat.of R)).Modules)
  [F.IsQuasicoherent]

/-- Forget only the module action and lift the actual coefficient values. -/
def moduleAdditiveLift : ModuleCat.{u} R ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

instance : (moduleAdditiveLift R).Additive :=
  inferInstanceAs (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}).Additive

/-- The actual tensor-section map with only its additive structure retained. -/
def tensorSectionsAddHom (A : CommAlgCat.{u} R) :
    A ⊗[R] moduleSpecΓFunctor.obj F →+
      Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj F, ⊤) :=
  (specTensorSectionsIso R F A).hom.hom.toAddMonoidHom

/-- All algebra-map compatibility is checked on native additive maps before value lifting. -/
theorem tensorSectionsAddHom_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    (tensorSectionsAddHom R F B).comp
      (f.hom.toLinearMap.rTensor (moduleSpecΓFunctor.obj F)).toAddMonoidHom =
    (sectionsAddHom (Spec (CommRingCat.of R)) F
      ((algSpec (CommRingCat.of R)).map f.op)).comp (tensorSectionsAddHom R F A) := by
  apply tensorSectionAddHom_ext
  intro a s
  exact (sectionsPresheaf_map_specTensor_tmul R F f a s).symm

/-- Tensor coordinates form a natural isomorphism for all native algebra maps. -/
def specTensorSectionsNatIso :
    ModuleCat.Amitsur.tensorModule R (moduleSpecΓFunctor.obj F) ⋙ moduleAdditiveLift R ≅
      (algSpec (CommRingCat.of R)).rightOp ⋙
        additiveSectionsPresheaf (Spec (CommRingCat.of R)) F := by
  refine NatIso.ofComponents (fun A => AddEquiv.toAddCommGrpIso
    (AddEquiv.ulift.trans
      ((specTensorSectionsIso R F A).toLinearEquiv.toAddEquiv.trans AddEquiv.ulift.symm))) ?_
  intro A B f
  ext s
  apply ULift.ext
  rcases s with ⟨s⟩
  change (specTensorSectionsIso R F B).hom
      ((f.hom.toLinearMap.rTensor (moduleSpecΓFunctor.obj F)) s) =
    (sectionsPresheaf (Spec (CommRingCat.of R)) F).map
      ((algSpec (CommRingCat.of R)).map f.op).op ((specTensorSectionsIso R F A).hom s)
  exact DFunLike.congr_fun (tensorSectionsAddHom_naturality R F f) s

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Sections on the spectra of the original algebraic Amitsur conerve. -/
def amitsurSections : CosimplicialObject AddCommGrpCat.{u + 1} :=
  Algebra.Amitsur.conerve R S ⋙ (algSpec (CommRingCat.of R)).rightOp ⋙
    additiveSectionsPresheaf (Spec (CommRingCat.of R)) F

/-- The original module-valued Amitsur cosimplicial object gives the actual section maps. -/
def amitsurSectionsIso :
    ModuleCat.Amitsur.cosimplicial R S (moduleSpecΓFunctor.obj F) ⋙ moduleAdditiveLift R ≅
      amitsurSections R F S :=
  Functor.isoWhiskerLeft (Algebra.Amitsur.conerve R S) (specTensorSectionsNatIso R F)

/-- The actual alternating Amitsur differential is preserved by the section comparison. -/
def amitsurSectionsComplexIso :
    ((moduleAdditiveLift R).mapHomologicalComplex (.up ℕ)).obj
        (ModuleCat.Amitsur.complex R S (moduleSpecΓFunctor.obj F)) ≅
      AlgebraicTopology.AlternatingCofaceMapComplex.obj (amitsurSections R F S) :=
  CategoryTheory.Cech.alternatingCofaceCoefficientIso (moduleAdditiveLift R)
      (ModuleCat.Amitsur.cosimplicial R S (moduleSpecΓFunctor.obj F)) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).mapIso
      (amitsurSectionsIso R F S)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
