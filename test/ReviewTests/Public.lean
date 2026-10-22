module
public import Init

/- Module-system fixture: review must follow a private local definition too. -/
private def boundary : Nat := 3

public section
namespace ReviewPublic

def region (x : Nat) : Prop := x ≤ boundary
theorem witness (x : Nat) (h : region x) : region x := h

end ReviewPublic
