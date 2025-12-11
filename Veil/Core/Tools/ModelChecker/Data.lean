namespace Veil

instance [BEq α] [Std.Stream αStream α] : Membership α αStream where
  mem stream searchedFor := Id.run do
    for el in stream do
      if el == searchedFor then
        return True
    return False

class abbrev Collection (Coll : Type → Type) (α : Type) :=
  BEq α
  EmptyCollection (Coll α) -- {}
  Std.Stream (Coll α) α -- for-in loop
  Functor Coll -- map
  Insert α (Coll α) -- insert
  Membership α (Coll α) -- mem / `∈`

namespace Collection
@[inline, grind]
def insertMany [Collection Main α] [Collection Extra α] (s : Main α) (xs : Extra α) : Main α := Id.run do
  let mut s := s
  for x in xs do
    s := insert x s
  return s
end Collection

instance prependListCollection [BEq α] : Collection List α where
  insert x xs := x :: xs

end Veil
