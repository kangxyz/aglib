/- Positive defining-origin inventory control, independent of consumer namespaces. -/
module
public import Init
@[expose] public section
namespace LeanCiForeign
/-- Generated declarations must remain in the exact origin inventory. -/
inductive Generated where
  | mk : Nat → Generated
private def hidden : Nat := 7
/-- A public declaration in a namespace unrelated to the package. -/
def datum : Nat := 7
end LeanCiForeign
