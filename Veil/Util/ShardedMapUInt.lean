module

public import Veil.Util.ShardedSetUInt
public import Veil.Util.HAMTShard
public import VerifiedHAMT.Map
meta import Veil.Util.Tactics

@[expose] public section

/-! # Sharded maps

The map counterpart of `ShardedSetUInt`. A `ShardedMapUSize` is a `ShardedUSize` whose shards are
maps, their type abstracted by `MapShard`: with `TreeMapShard` or `HAMTMapShard` shards, the
parallel search's seen set, which also records how the search first reached each state it has
seen; with `HashMap` shards (`ShardedHashMapUSize`), the map in which a merge of the parallel search
collects a BFS layer before adding it to the seen set, shard by shard.
-/

open Std

/-! ## Shards -/

/-- The operations, and their specifications, that a `ShardedMapUSize` needs from the map type `S`
of its shards, whose values have type `β`, beyond those of `KeyShard`. Only single insertions are
required: `MapShard.insertMany` inserts the bindings of a whole `HashMap` by folding them. -/
class MapShard (α : Type u) (β : outParam (Type v)) (S : Type w) [BEq α] [Hashable α] [Membership α S]
    extends KeyShard α S where
  insert : S → α → β → S
  get? : S → α → Option β
  mem_iff_isSome_get? {s : S} {k : α} : k ∈ s ↔ (get? s k).isSome
  get?_empty {k : α} : get? empty k = none
  get?_insert {s : S} {k q : α} {v : β} : get? (insert s k v) q = if k == q then some v else get? s q

namespace MapShard

variable {α : Type u} {β : Type v} {S : Type w} [BEq α] [Hashable α] [Membership α S] [MapShard α β S]

/-- `s` with the bindings of `m` inserted. -/
@[inline]
def insertMany (s : S) (m : HashMap α β) : S :=
  m.fold (init := s) fun s k v => insert s k v

-- CHECK Maybe move this to a utility file of theorems of `HashMap` operations?
/-- The value of `k` in a `HashMap`, read off its list of bindings. -/
private theorem map_snd_find?_toList [LawfulBEq α] [LawfulHashable α] {m : HashMap α β} {k : α} :
    (m.toList.find? (·.1 == k)).map (·.2) = m[k]? := by
  apply Option.ext ; intro v
  simp [Option.map_eq_some_iff, Prod.exists,
    HashMap.find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some,
    ← Option.isSome_iff_exists]
  grind [HashMap.mem_iff_isSome_getElem?]

theorem get?_insertMany [LawfulBEq α] [LawfulHashable α] {s : S} {m : HashMap α β} {k : α} :
    get? (insertMany s m) k = m[k]?.or (get? s k) := by
  simp only [insertMany, HashMap.fold_eq_foldl_toList]
  rw [← map_snd_find?_toList]
  have hl := HashMap.distinct_keys_toList (m := m)
  generalize m.toList = l at hl ⊢
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    rw [List.pairwise_cons] at hl
    open Classical in simp [List.foldl_cons, ih hl.2, get?_insert, List.find?_cons]
    grind

theorem mem_insertMany [LawfulBEq α] [LawfulHashable α] {s : S} {m : HashMap α β} {k : α} :
    k ∈ insertMany s m ↔ k ∈ s ∨ k ∈ m := by
  rw [mem_iff_isSome_get? (β := β), get?_insertMany, Option.isSome_or, Bool.or_eq_true,
    ← HashMap.mem_iff_isSome_getElem?, ← mem_iff_isSome_get? (β := β)]
  apply Or.comm

theorem mem_insert {s : S} {x k : α} {v : β} : k ∈ insert s x v ↔ (x == k) = true ∨ k ∈ s := by
  rw [mem_iff_isSome_get? (β := β), get?_insert, mem_iff_isSome_get? (β := β)]
  split <;> simp_all

end MapShard

/-- `Std.TreeMap` ordered by `compare`, as the map type of shards. The value type comes last, so
that `TreeMapShard σₕ` is the map type as a function of the value type. -/
abbrev TreeMapShard (α : Type u) [Ord α] (β : Type v) := TreeMap α β compare

instance [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulBEq α] [Hashable α] :
    MapShard α β (TreeMapShard α β) where
  empty := ∅
  insert s k v := s.insert k v
  get? s k := s[k]?
  contains := TreeMap.contains
  size := TreeMap.size
  toList := TreeMap.keys
  not_mem_empty := TreeMap.not_mem_emptyc
  contains_iff_mem := TreeMap.contains_iff_mem
  mem_toList := TreeMap.mem_keys
  nodup_toList := TreeMap.distinct_keys.imp fun h heq => by subst heq ; exact h ReflCmp.compare_self
  length_toList := TreeMap.length_keys
  mem_iff_isSome_get? := TreeMap.mem_iff_isSome_getElem?
  get?_empty := TreeMap.getElem?_emptyc
  get?_insert := by intros ; rw [TreeMap.getElem?_insert] ; simp only [LawfulBEqCmp.compare_eq_iff_beq]

/-- A verified HAMT map (`VerifiedHAMT.Map`) as the map type of shards. It hashes with
`HAMTShard.hashable`, for the reason given there. The value type comes last, as for
`TreeMapShard`. -/
abbrev HAMTMapShard (α : Type u) [BEq α] [Hashable α] (β : Type v) : Type (max u v) :=
  @VerifiedHAMT.Map α β _ (HAMTShard.hashable α)

namespace HAMTMapShard

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

/-- Membership test, kept out of line for the reason given at `HAMTShard.contains`. -/
@[noinline] def contains (s : HAMTMapShard α β) (k : α) : Bool :=
  @VerifiedHAMT.Map.contains α β _ (HAMTShard.hashable α) s k

variable [LawfulBEq α]

-- As for `HAMTShard`, the operations get the HAMT's `Hashable` instance explicitly.
instance : MapShard α β (HAMTMapShard α β) where
  empty := @VerifiedHAMT.Map.empty α β _ (HAMTShard.hashable α)
  insert s k v := @VerifiedHAMT.Map.insert α β _ (HAMTShard.hashable α) _ s k v
  get? s k := @VerifiedHAMT.Map.find? α β _ (HAMTShard.hashable α) s k
  contains := contains
  size s := @VerifiedHAMT.SizedRaw.size α β _ (HAMTShard.hashable α)
    (@VerifiedHAMT.Map.toSizedRaw α β _ (HAMTShard.hashable α) s)
  toList s := @VerifiedHAMT.Map.keys α β _ (HAMTShard.hashable α) s
  not_mem_empty := fun {k} => @VerifiedHAMT.Map.not_mem_empty α β _ (HAMTShard.hashable α) k
  contains_iff_mem := fun {s k} => @VerifiedHAMT.Map.contains_eq_true_iff α β _ (HAMTShard.hashable α) _ s k
  mem_toList := fun {s k} => @VerifiedHAMT.Map.mem_keys α β _ (HAMTShard.hashable α) s k
  nodup_toList := fun {s} => @VerifiedHAMT.Map.nodup_keys α β _ (HAMTShard.hashable α) s
  length_toList := fun {s} => @VerifiedHAMT.Map.length_keys α β _ (HAMTShard.hashable α) s
  mem_iff_isSome_get? := fun {s k} => by
    rw [@VerifiedHAMT.Map.find?_isSome_eq_contains α β _ (HAMTShard.hashable α) _ s k,
      @VerifiedHAMT.Map.contains_eq_true_iff α β _ (HAMTShard.hashable α) _ s k]
  get?_empty := fun {k} => @VerifiedHAMT.Map.find?_empty α β _ (HAMTShard.hashable α) _ k
  get?_insert := fun {s k q v} => by
    rw [@VerifiedHAMT.Map.find?_insert α β _ (HAMTShard.hashable α) _ s k q v]
    simp only [BEq.comm]

end HAMTMapShard

/-- `HashMap` as the map type of shards, for `ShardedHashMapUSize`. -/
instance [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : MapShard α β (HashMap α β) where
  empty := HashMap.emptyWithCapacity 8
  insert s k v := s.insert k v
  get? s k := s[k]?
  contains := HashMap.contains
  size := HashMap.size
  toList := HashMap.keys
  not_mem_empty := HashMap.not_mem_emptyWithCapacity
  contains_iff_mem := HashMap.mem_iff_contains.symm
  mem_toList := HashMap.mem_keys
  nodup_toList := HashMap.nodup_keys
  length_toList := HashMap.length_keys
  mem_iff_isSome_get? := HashMap.mem_iff_isSome_getElem?
  get?_empty := HashMap.getElem?_emptyWithCapacity
  get?_insert := HashMap.getElem?_insert

/-! ## Sharded maps -/

-- `β`, the type of the values, only documents the type: the `MapShard` instance determines it.
set_option linter.unusedVariables false in
/-- A map split into shards of type `S` by the hash of each key, with `USize`-based sharding: with
`TreeMapShard` or `HAMTMapShard` shards, the parallel search's seen set, whose values are the log
entries of the states it has seen. -/
abbrev ShardedMapUSize (α : Type u) (β : Type v) (S : Type w) [Hashable α] [Membership α S]
    (numShards : PosUSize) :=
  ShardedUSize α S numShards

/-- A sharded map with `HashMap` shards. A merge of the parallel search collects the new states of a
BFS layer in one, as fingerprint to log entry: it deduplicates the layer with it, then adds its
bindings to the seen set shard by shard (`ShardedMapUSize.insertMany`). -/
abbrev ShardedHashMapUSize (α : Type u) [BEq α] [Hashable α] (β : Type v) (numShards : PosUSize) :=
  ShardedMapUSize α β (HashMap α β) numShards

namespace ShardedMapUSize

variable {α : Type u} {β : Type v} {S : Type w} [BEq α] [Hashable α] [Membership α S] [MapShard α β S]
  {numShards : PosUSize}

@[inline]
def get? (st : ShardedMapUSize α β S numShards) (k : α) : Option β :=
  MapShard.get? (st.getShard k) k

theorem mem_iff_isSome_get? {st : ShardedMapUSize α β S numShards} {k : α} :
    k ∈ st ↔ (st.get? k).isSome := by
  unfold get? ; rw [ShardedUSize.mem_def, MapShard.mem_iff_isSome_get?]

theorem not_mem_iff_get?_none {st : ShardedMapUSize α β S numShards} {k : α} :
    k ∉ st ↔ st.get? k = none := by rw [mem_iff_isSome_get?] ; simp

theorem get?_empty {k : α} :
    ShardedMapUSize.get? (ShardedUSize.empty : ShardedMapUSize α β S numShards) k = none := by
  simp [get?, ShardedUSize.getShard, ShardedUSize.empty, ShardedUSize.replicate, VectorUSize.ugetViaHash,
    VectorUSize.uget, VectorUSize.replicateUSize, Array.uget, MapShard.get?_empty]

open ShardedSetUInt in
/-- Looking up a key in a map built by `ofMap` reads its shard after applying `f`. -/
theorem get?_ofMap {γ : Type w'} {v : VectorUSize γ numShards} {f : γ → S}
    {h : ∀ (i : USize) (hi : i < numShards), ∀ k ∈ f (v.uget i hi), shardIdxOfUSize numShards k = i}
    {k : α} :
    get? (ShardedUSize.ofMap v f h : ShardedMapUSize α β S numShards) k =
      MapShard.get? (f (v.uget (shardIdxOfUSize numShards k) (shardIdxOfUSize_lt k numShards.property))) k := by
  simp only [get?, ShardedUSize.ofMap, ShardedUSize.getShard, VectorUSize.ugetViaHash, VectorUSize.uget_map]

/-- Unconditionally insert a key with its value into the sharded map. -/
@[specialize]
def insert [LawfulBEq α] (st : ShardedMapUSize α β S numShards) (x : α) (v : β) :
    ShardedMapUSize α β S numShards :=
  st.modifyShard x (MapShard.insert · x v) fun _ k hk => by grind [MapShard.mem_insert]

@[simp]
theorem mem_insert [LawfulBEq α] {st : ShardedMapUSize α β S numShards} {x y : α} {v : β} :
    x ∈ st.insert y v ↔ (y == x) = true ∨ x ∈ st := by
  unfold insert ShardedUSize.modifyShard
  rw [ShardedUSize.mem_def, ShardedUSize.mem_def]
  unfold ShardedUSize.getShard
  simp [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.ugetViaHash, VectorUSize.uget, VectorUSize.uset,
    Array.uget, Array.uset, Array.getElem_set]
  grind [MapShard.mem_insert]

theorem get?_insert [LawfulBEq α] {st : ShardedMapUSize α β S numShards} {x y : α} {v : β} :
    (st.insert y v).get? x = if y == x then some v else st.get? x := by
  unfold insert get? ShardedUSize.modifyShard ShardedUSize.getShard
  simp [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.ugetViaHash, VectorUSize.uget, VectorUSize.uset,
    Array.uget, Array.uset, Array.getElem_set]
  grind [MapShard.get?_insert]

/-! ### Inserting a sharded `HashMap` -/

/-- Insert the bindings of a sharded `HashMap`, shard by shard, each shard in a task of its own. -/
@[inline]
def insertMany [LawfulBEq α] [LawfulHashable α] (st : ShardedMapUSize α β S numShards)
    (items : ShardedHashMapUSize α β numShards) : ShardedMapUSize α β S numShards :=
  st.zipShardsPar items MapShard.insertMany fun _ _ _ h => MapShard.mem_insertMany.mp h

theorem get?_insertMany [LawfulBEq α] [LawfulHashable α] {st : ShardedMapUSize α β S numShards}
    {items : ShardedHashMapUSize α β numShards} {k : α} :
    (st.insertMany items).get? k = (items.get? k).or (st.get? k) := by
  simp [get?, insertMany, ShardedUSize.zipShardsPar, ShardedUSize.getShard, Task.spawn,
    VectorUSize.ugetViaHash, VectorUSize.uget, MapShard.get?_insertMany]
  rfl

theorem mem_insertMany [LawfulBEq α] [LawfulHashable α] {st : ShardedMapUSize α β S numShards}
    {items : ShardedHashMapUSize α β numShards} {k : α} :
    k ∈ st.insertMany items ↔ k ∈ st ∨ k ∈ items := by
  simp [ShardedUSize.mem_def, insertMany, ShardedUSize.zipShardsPar, ShardedUSize.getShard, Task.spawn,
    VectorUSize.ugetViaHash, VectorUSize.uget, MapShard.mem_insertMany]

end ShardedMapUSize
