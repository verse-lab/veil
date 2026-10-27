module

public import Veil

/-! Integer comparisons must remain executable after importing Veil, even though its SMT
dependency imports Auto's integer comparison instance at the meta phase. -/

private def intEqual (a b : Int) : Bool := a == b

-- List membership also needs a LawfulBEq instance compatible with the selected BEq.
private def intMember (x a b : Int) : Bool := decide (x ∈ [a, b])

#guard intEqual (-1) (-1)
#guard !intEqual (-1) 1
#guard intMember (-1) (-1) 0
#guard intMember 0 (-1) 0
#guard !intMember 1 (-1) 0
