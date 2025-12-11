import Std.Data.HashSet
import Veil.Core.Tools.ModelChecker.TransitionSystem

namespace Veil.ModelChecker.Concrete

/-- Functional Queue, from https://vfoley.xyz/functional-queues. -/
structure fQueue (α : Type) where
  front : List α
  back : List α
deriving Inhabited, Repr

namespace fQueue
def empty {α} : fQueue α := ⟨[], []⟩

@[grind]
def norm {α} (q : fQueue α) : fQueue α :=
  match q.front with
  | []    => ⟨q.back.reverse, []⟩
  | _::_  => q

@[grind]
def enqueue {α} (q : fQueue α) (x : α) : fQueue α :=
  ⟨q.front, x :: q.back⟩ -- O(1)

@[grind]
def dequeue? {α} (q : fQueue α) : Option (α × fQueue α) :=
  match (norm q).front with
  | []        => none
  | x :: xs   => some (x, ⟨xs, (norm q).back⟩)

@[grind]
def toList {α} (q : fQueue α) : List α :=
  q.front ++ q.back.reverse

@[grind]
def insertCollection [Collection Coll α] (s : fQueue α) (xs : Coll) : fQueue α := Id.run do
  let mut s := s
  for x in xs do
    s := s.enqueue x
  return s

end fQueue

namespace HashSet
@[grind]
def insertCollection {α} [Collection Coll α] [Hashable α] (s : Std.HashSet α) (xs : Coll) : Std.HashSet α := Id.run do
  let mut s := s
  for x in xs do
    s := s.insert x
  return s
end HashSet

end Veil.ModelChecker.Concrete
