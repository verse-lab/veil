module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! A counterexample whose step rewrites one row of a relation over two enum
sorts (`pc light S := …`). The certificate proves that step by splitting each
enum variable into its constructors. -/

veil module CexRow

enum proc = {light, car}
enum phase = {cyc, drive, fin}

relation pc : proc → phase → Bool
individual go : Bool

#gen_state

after_init {
  pc P S := if P == light then S == cyc else S == drive
  go := false
}

action step {
  require pc light cyc
  pc light S := S == fin
}

action move {
  require pc light fin
  go := true
}

safety [stays] ¬ go

#gen_spec

#guard_msgs(drop info) in
#updr (expect := unsafe) certify

#gen_theorems

/-- info: 'CexRow.ic3_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CexRow.ic3_unsafe

end CexRow
