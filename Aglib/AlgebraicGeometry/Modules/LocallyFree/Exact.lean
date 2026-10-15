/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalSplitting
public import Aglib.CategoryTheory.ExactCategory.Subcategory
/-!
# The genuine exact category of vector bundles on a scheme

Finite locally free sheaves are closed under extensions of actual sheaves of
modules. A short exact sequence splits only locally: near each point choose
finite bases of its endpoints, lift the quotient basis, and take the sum of
the endpoint bases. The resulting exact structure consists of all ambient
short exact sequences, not just globally split ones.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}

/-- The middle term of an actual short exact sequence is finite locally free
when both endpoints are. The splitting used in the proof is only local. -/
theorem finiteLocallyFree_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteLocallyFree X S.X₁] [IsFiniteLocallyFree X S.X₃] :
    IsFiniteLocallyFree X S.X₂ := by
  apply finiteLocallyFree_iff_pointwise.mpr
  intro x
  obtain ⟨U₁, hx₁, G₁, hG₁, hf₁⟩ :=
    finiteLocallyFree_iff_pointwise.mp (inferInstance : IsFiniteLocallyFree X S.X₁) x
  obtain ⟨U₃, hx₃, G₃, hG₃, hf₃⟩ :=
    finiteLocallyFree_iff_pointwise.mp (inferInstance : IsFiniteLocallyFree X S.X₃) x
  let W := U₁ ⊓ U₃
  let GW₃ := restrictLocalBasis (show W ≤ U₃ from inf_le_right) G₃
  let := hS.epi_g
  obtain ⟨V, hVW, hxV, s, hs⟩ :=
    exists_local_section_of_finite_basis S.g W GW₃ x ⟨hx₁, hx₃⟩
  let GV₁ := restrictLocalBasis (hVW.trans inf_le_left) G₁
  let GV₃ := restrictLocalBasis (hVW.trans inf_le_right) G₃
  let hV := shortExact_over hS V
  let split := ShortComplex.Splitting.ofExactOfSection _ hV.exact s hs hV.mono_f
  let e : SheafOfModules.free (GV₁.I ⊕ GV₃.I) ≅ S.X₂.over V :=
    (SheafOfModules.freeSumIso GV₁.I GV₃.I).symm ≪≫
      (biprod.isoCoprod _ _).symm ≪≫
      biprod.mapIso (asIso GV₁.π) (asIso GV₃.π) ≪≫ split.isoBinaryBiproduct.symm
  let G := (SheafOfModules.free.generatingSections (R := X.ringCatSheaf.over V)
    (GV₁.I ⊕ GV₃.I)).ofEpi e.hom
  refine ⟨V, hxV, G, inferInstance, ?_⟩
  constructor
  change Finite (GV₁.I ⊕ GV₃.I)
  infer_instance

/-- Extension closure is for the standard ambient sheaf exact structure. -/
instance finiteLocallyFree_extensionClosed :
    (sheafExactStructure X).IsExtensionClosed (finiteLocallyFree X) where
  prop_middle hS _h₁ _h₃ := finiteLocallyFree_of_shortExact hS

instance finiteLocallyFree_closedUnderFiniteProducts :
    (finiteLocallyFree X).IsClosedUnderFiniteProducts :=
  (sheafExactStructure X).extensionClosed_finiteProducts (finiteLocallyFree X)

/-- Vector bundles carry the exact structure inherited from all module sheaves. -/
def vectorBundleExactStructure (X : Scheme.{u}) : ExactStructure (FiniteLocallyFree X) :=
  ExactSubcategory.exactStructure (sheafExactStructure X) (finiteLocallyFree X)

/-- Its conflations are exactly the ambient short exact sequences. -/
@[simp]
theorem vectorBundleExactStructure_conflation (S : ShortComplex (FiniteLocallyFree X)) :
    (vectorBundleExactStructure X).conflation S ↔
      (S.map (finiteLocallyFree X).ι).ShortExact := Iff.rfl

/-- The inclusion of vector bundles into module sheaves is an actual exact functor. -/
def vectorBundleExactInclusion (X : Scheme.{u}) :
    ExactFunctor (vectorBundleExactStructure X) (sheafExactStructure X) :=
  ExactSubcategory.exactInclusion (sheafExactStructure X) (finiteLocallyFree X)

end AlgebraicGeometry.Scheme.Modules
