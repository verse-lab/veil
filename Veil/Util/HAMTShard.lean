module

public import VerifiedHAMT.Set
public import VerifiedHAMT.SetWithoutValArray
public import Veil.Util.ShardedSetUInt

@[expose] public section

/-! # HAMT shards

Verified HAMTs as the set type of the shards of a `ShardedSetUSize`, the alternatives to
`TreeSetShard` for the parallel search's seen set (`#model_check` option `seenSet`):
`HAMTShard` (`VerifiedHAMT.Set`) and `HAMTKeysShard` (`VerifiedHAMT.SetWithoutValArray`, which stores
no values and so takes less memory).
-/

open Std

namespace HAMTShard

/-- The hash with its two halves swapped, so that the choice of the shard and the HAMT inside it use
different bits of the hash. A `ShardedSetUSize` picks the shard of a key by `hash k % numShards`,
and a HAMT picks the slot at its root by the lowest 5 bits. With an even number of shards, all keys
of a shard agree on the lowest bits (the lowest 3 for 8 shards), so with the plain hash they would
collide in a few of the root's 32 slots (4 for 8 shards), and the tree would get deeper. Nothing
mixes these bits further: the hash of a `Nat` fingerprint is the fingerprint itself.

NOTE: The swap is cheaper than the three operations suggest: the compiler turns it into a single rotate
instruction (`ror` on arm64). -/
@[inline] def swapHalves (h : UInt64) : UInt64 := (h >>> 32) ||| (h <<< 32)

/-- The `Hashable` instance of the HAMT in a shard. -/
@[reducible] def hashable (α : Type u) [Hashable α] : Hashable α := ⟨fun k => swapHalves (hash k)⟩

end HAMTShard

/-- A verified HAMT (`VerifiedHAMT.Set`, which keeps its size) as the set type of shards.

As the global seen set of the parallel search, it is shared with tasks, so an insertion cannot
update its nodes in place but copies them. A HAMT copies only the nodes on the path to the key, and
a lookup visits a few nodes where a `TreeSet` visits a few dozen, mostly cache misses. It takes more
memory per key than a `TreeSet`: its nodes have 32 slots, and each key is in an entry of its own. -/
abbrev HAMTShard (α : Type u) [BEq α] [Hashable α] : Type u :=
  @VerifiedHAMT.Set α _ (HAMTShard.hashable α)

namespace HAMTShard

variable {α : Type u} [BEq α] [Hashable α]

/-- Membership test, kept out of line.

Once inlined into the parallel search's loop, it reads the root
out of the shard there, and the compiler then holds on to the shard to reuse its memory for a pair
built later. That needs the shard owned, so the loop takes a reference to it from the seen set, and
releases it again, on every lookup: atomic reference count updates, since the shard is shared by
the tasks, and in vain, since a shared shard is never reused.

Out of line, the loop only passes the
shard, without taking a reference: the compiler infers that `contains` borrows its arguments. -/
@[noinline] def contains (s : HAMTShard α) (k : α) : Bool :=
  @VerifiedHAMT.Set.contains α _ (hashable α) s k

variable [LawfulBEq α]

-- The HAMT hashes with `hashable α`, not with the `Hashable α` instance in scope, so the
-- `VerifiedHAMT.Set` operations get their instances explicitly.
instance : SetShard α (HAMTShard α) where
  ofList l := @VerifiedHAMT.Set.ofList α _ (hashable α) _ l
  contains := contains
  insertMany s hs := hs.fold (init := s) (@VerifiedHAMT.Set.insert α _ (hashable α) _)
  size s := @VerifiedHAMT.Set.size α _ (hashable α) s
  contains_iff_mem := fun {s k} => @VerifiedHAMT.Set.contains_eq_true_iff α _ (hashable α) _ s k
  mem_ofList := fun {l k} => @VerifiedHAMT.Set.mem_ofList α _ (hashable α) _ l k
  mem_insertMany := by
    intro s hs k
    rw [HashSet.fold_eq_foldl_toList, @VerifiedHAMT.Set.mem_foldl_insert α _ (hashable α) _,
      HashSet.mem_toList]

end HAMTShard

/-- A verified HAMT that stores only keys (`VerifiedHAMT.SetWithoutValArray`, which keeps its size) as
the set type of shards. It is `HAMTShard` without the values of a map: its leaves hold just the key
and its collision buckets an array of keys, which saves memory; the 32-slot nodes are the same. -/
abbrev HAMTKeysShard (α : Type u) [BEq α] [Hashable α] : Type u :=
  @VerifiedHAMT.SetWithoutValArray α _ (HAMTShard.hashable α)

namespace HAMTKeysShard

variable {α : Type u} [BEq α] [Hashable α]

/-- Membership test, kept out of line for the reason given at `HAMTShard.contains`. -/
@[noinline] def contains (s : HAMTKeysShard α) (k : α) : Bool :=
  @VerifiedHAMT.SetWithoutValArray.contains α _ (HAMTShard.hashable α) s k

variable [LawfulBEq α]

-- As for `HAMTShard`, the operations get the HAMT's `Hashable` instance explicitly.
instance : SetShard α (HAMTKeysShard α) where
  ofList l := @VerifiedHAMT.SetWithoutValArray.ofList α _ (HAMTShard.hashable α) _ l
  contains := contains
  insertMany s hs :=
    hs.fold (init := s) (@VerifiedHAMT.SetWithoutValArray.insert α _ (HAMTShard.hashable α) _)
  size s := @VerifiedHAMT.SetWithoutValArray.Raw.SizedRaw.size α _ (HAMTShard.hashable α)
    (@VerifiedHAMT.SetWithoutValArray.toSizedRaw α _ (HAMTShard.hashable α) s)
  contains_iff_mem := fun {s k} =>
    @VerifiedHAMT.SetWithoutValArray.contains_eq_true_iff α _ (HAMTShard.hashable α) _ s k
  mem_ofList := fun {l k} =>
    @VerifiedHAMT.SetWithoutValArray.mem_ofList α _ (HAMTShard.hashable α) _ l k
  mem_insertMany := by
    intro s hs k
    rw [HashSet.fold_eq_foldl_toList,
      @VerifiedHAMT.SetWithoutValArray.mem_foldl_insert α _ (HAMTShard.hashable α) _,
      HashSet.mem_toList]

end HAMTKeysShard
