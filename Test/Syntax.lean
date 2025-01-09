import Veil.DSL

section Test

type node

relation r : node -> node -> Prop

#gen_state Test

#check
   if true then
      true
    else false

action foo (k : Nat) = {
  skip
  skip; skip
  let x <- skip
  require x = x
  let y <- return 5
  require y = 5
  return 5
  let x <- require y = 5
  require x = ()
  let x <- fresh Int
  require x = k
  let x <- fresh
  require x = ()
  if (x = ()) then
    skip
  else
    skip
  -- else return 5
}

action bar = {
  !foo 5
  r N M := True
  let m <- fresh
  ensure r m m = False
}



end Test
