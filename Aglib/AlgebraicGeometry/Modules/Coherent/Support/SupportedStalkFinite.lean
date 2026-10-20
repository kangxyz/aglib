/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.CodimensionOneStalk
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StalkKernel
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.HeightSlice

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.SupportedStalkFinite` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`fcb3fa1105f0573fd7379973fa644b99de71ec3dcc68f7aafcbe7af36420607d`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules (stalkFunctor)
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent (FiniteTypeSheaves)
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
    AlgebraicGeometry.Scheme.Modules.Coherent.Support
    AlgebraicGeometry.Scheme.Modules.Coherent.Support
variable (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X]

/-- Positive support has finite actual height-one stalk support, on every
integral Noetherian scheme. No dimension bound or arithmetic model is used. -/
theorem supportedStalk_finite (N : CohOne X) :
    {x : CodimensionOnePoint X | ¬ IsZero ((supportedStalk X x).toFunctor.obj N)}.Finite := by
  let N' := (equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse.obj N.obj
  have hη : IsZero ((stalkFunctor X (genericPoint X)).obj N'.obj) :=
    (smallStalk_kernel_iff X N.obj (genericPoint X)).mp N.property
  have hf := coherent_finite_height_support X N' 1 (fun x hx => by
    simpa only [eq_genericPoint_of_height_lt_one X x hx] using hη)
  apply (hf.preimage (f := fun x : CodimensionOnePoint X => x.1) Subtype.val_injective.injOn).subset
  intro x hx
  refine ⟨x.2, ?_⟩
  intro hz
  apply hx
  apply IsZero.of_full_of_faithful_of_isZero (localSupport X x).ι _
  exact (smallStalk_kernel_iff X N.obj x.1).mpr hz

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
