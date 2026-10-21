/- Compile-pass, audit-negative fixture. Never a positive library build target. -/
module
public import Init
@[expose] public section
namespace LeanCiNegative
private axiom forbidden : False
/-- The generic audit must detect the actual private assumption dependency. -/
private theorem contradiction : False := forbidden
end LeanCiNegative
