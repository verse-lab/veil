module

public import Veil.Util.ShardedSetUInt
public import Veil.Util.HAMTShard
public import VerifiedHAMT.Map
meta import Veil.Util.Tactics

@[expose] public section

/-! # Sharded maps

The map counterpart of `ShardedSetUInt`. `ShardedMapUSize` splits a map into shards by the hash
of each key, with the map type of the shards abstracted by `MapShard`: the parallel search's seen
set, which also records how the search first reached each state it has seen. `ShardedHashMapUSize`
is the sharded `HashMap` in which a merge of the parallel search collects a BFS layer before
adding it to the seen set, shard by shard.
-/

open Std

/-! ## Shards -/

/-- The operations, and their specifications, that a `ShardedMapUSize` needs from the map type `S`
of its shards, whose values have type `β`. Only single insertions are required:
`MapShard.insertMany` inserts the bindings of a whole `HashMap` by folding them. -/
class MapShard (α : Type u) (β : outParam (Type v)) (S : Type w) [BEq α] [Hashable α] [Membership α S] where
  empty : S
  insert : S → α → β → S
  get? : S → α → Option β
  contains : S → α → Bool
  size : S → Nat
  contains_iff_mem {s : S} {k : α} : contains s k = true ↔ k ∈ s
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

end MapShard

/-- `Std.TreeMap` ordered by `compare`, as the map type of shards. The value type comes last, so
that `TreeMapShard σₕ` is the map type as a function of the value type. -/
abbrev TreeMapShard (α : Type u) [Ord α] (β : Type v) := TreeMap α β compare

instance [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Hashable α] :
    MapShard α β (TreeMapShard α β) where
  empty := ∅
  insert s k v := s.insert k v
  get? s k := s[k]?
  contains := TreeMap.contains
  size := TreeMap.size
  contains_iff_mem := TreeMap.contains_iff_mem
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
  contains_iff_mem := fun {s k} => @VerifiedHAMT.Map.contains_eq_true_iff α β _ (HAMTShard.hashable α) _ s k
  mem_iff_isSome_get? := fun {s k} => by
    rw [@VerifiedHAMT.Map.find?_isSome_eq_contains α β _ (HAMTShard.hashable α) _ s k,
      @VerifiedHAMT.Map.contains_eq_true_iff α β _ (HAMTShard.hashable α) _ s k]
  get?_empty := fun {k} => @VerifiedHAMT.Map.find?_empty α β _ (HAMTShard.hashable α) _ k
  get?_insert := fun {s k q v} => by
    rw [@VerifiedHAMT.Map.find?_insert α β _ (HAMTShard.hashable α) _ s k q v]
    simp only [BEq.comm]

end HAMTMapShard

/-! ## Sharded maps -/

/-- A map split into shards of type `S` by the hash of each key, with `USize`-based sharding: the
parallel search's seen set, whose values are the log entries of the states it has seen. -/
structure ShardedMapUSize (α : Type u) (β : Type v) (S : Type w) where
  numShards : USize
  h_numShards_pos : 0 < (numShards : USize)
  shards : VectorUSize S numShards

namespace ShardedMapUSize

open ShardedSetUInt

variable {α : Type u} {β : Type v} {S : Type w}

/-- Get the shard for a given key. -/
@[inline]
def getShard [Hashable α] (st : ShardedMapUSize α β S) (k : α) : S :=
  st.shards.ugetViaHash k st.h_numShards_pos

instance instMembership [Hashable α] [Membership α S] : Membership α (ShardedMapUSize α β S) where
  mem st k := k ∈ st.getShard k

theorem mem_def [Hashable α] [Membership α S] {st : ShardedMapUSize α β S} {k : α} :
    k ∈ st ↔ k ∈ st.getShard k := Iff.rfl

variable [BEq α] [Hashable α] [Membership α S] [MapShard α β S]

@[inline]
def contains (st : ShardedMapUSize α β S) (k : α) : Bool :=
  MapShard.contains (st.getShard k) k

@[inline]
def get? (st : ShardedMapUSize α β S) (k : α) : Option β :=
  MapShard.get? (st.getShard k) k

/-- Total number of keys across all shards. -/
def size (st : ShardedMapUSize α β S) : Nat :=
  st.shards.val.foldl (init := 0) fun acc shard => acc + MapShard.size (α := α) shard

theorem contains_iff_mem {st : ShardedMapUSize α β S} {k : α} :
    st.contains k ↔ k ∈ st := by
  unfold contains ; rw [mem_def, MapShard.contains_iff_mem]

theorem mem_iff_isSome_get? {st : ShardedMapUSize α β S} {k : α} :
    k ∈ st ↔ (st.get? k).isSome := by
  unfold get? ; rw [mem_def, MapShard.mem_iff_isSome_get?]

set_option compiler.extract_closed false in
/-- The empty map with `n` shards. -/
def empty (n : USize) (h_pos : 0 < n) : ShardedMapUSize α β S :=
  ⟨n, h_pos, .replicateUSize n (MapShard.empty α)⟩

theorem get?_empty {n : USize} {h_pos : 0 < n} {k : α} :
    (empty (α := α) (β := β) (S := S) n h_pos).get? k = none := by
  simp [get?, getShard, empty, VectorUSize.ugetViaHash, VectorUSize.uget, VectorUSize.replicateUSize,
    Array.uget, MapShard.get?_empty]

theorem not_mem_empty {n : USize} {h_pos : 0 < n} {k : α} :
    k ∉ empty (α := α) (β := β) (S := S) n h_pos := by
  rw [mem_iff_isSome_get?, get?_empty] ; simp

/-- Insert the bindings of a vector of `HashMap`s into the corresponding shards, each shard in a
task of its own. -/
@[specialize]
def insertManySharded (st : ShardedMapUSize α β S) (items : VectorUSize (HashMap α β) st.numShards) :
    ShardedMapUSize α β S :=
  let pairs := st.shards.val.zip items.val |>.toList
  let tasks := pairs.map fun (shard, m) =>
    Task.spawn fun () => MapShard.insertMany shard m
  let shardArr := tasks.map Task.get
  let newShards := ⟨shardArr.toArray, by simp [shardArr, tasks, pairs, st.shards.property, items.property]⟩
  { st with shards := newShards }

theorem get?_insertManySharded [LawfulBEq α] [LawfulHashable α] {st : ShardedMapUSize α β S}
    {items : VectorUSize (HashMap α β) st.numShards} {k : α} :
    (st.insertManySharded items).get? k = (items.ugetViaHash k st.h_numShards_pos)[k]?.or (st.get? k) := by
  simp [get?, insertManySharded, getShard, Task.spawn,
    VectorUSize.ugetViaHash, VectorUSize.uget, MapShard.get?_insertMany]

theorem mem_insertManySharded [LawfulBEq α] [LawfulHashable α] {st : ShardedMapUSize α β S}
    {items : VectorUSize (HashMap α β) st.numShards} {k : α} :
    k ∈ st.insertManySharded items ↔ k ∈ st ∨ k ∈ items.ugetViaHash k st.h_numShards_pos := by
  simp [mem_def, insertManySharded, getShard, Task.spawn,
    VectorUSize.ugetViaHash, VectorUSize.uget, MapShard.mem_insertMany]

end ShardedMapUSize

/-! ## The sharded `HashMap` of a merge -/

/-- A map split into `HashMap` shards by the hash of each key, with `USize`-based sharding. A merge
of the parallel search collects the new states of a BFS layer in one, as fingerprint to log
entry: it deduplicates the layer with it, then adds its bindings to the seen set shard by shard
(`ShardedMapUSize.insertManySHM`). -/
structure ShardedHashMapUSize (α : Type u) [BEq α] [Hashable α] (β : Type v) (numShards : USize) where
  h_numShards_pos : 0 < (numShards : USize)
  shards : VectorUSize (HashMap α β) numShards
  h_in_correct_shard : ∀ (i : USize) (h : i < numShards), ∀ k ∈ shards.uget i h,
    ShardedSetUInt.shardIdxOfUSize numShards k = i

namespace ShardedHashMapUSize

open ShardedSetUInt

variable {α : Type u} [BEq α] [Hashable α] {β : Type v} {numShards : USize}

set_option compiler.extract_closed false in
def empty (n : Nat)
  (h_pos : 0 < USize.ofNat n := by native_decide)
  (h_small : n < USize.size := by native_decide) : ShardedHashMapUSize α β n.toUSize where
  h_numShards_pos := h_pos
  shards := .replicate h_small (Std.HashMap.emptyWithCapacity 8)
  h_in_correct_shard := by
    simp only [VectorUSize.replicate, VectorUSize.uget, Array.uget]
    intros ; simp at *

set_option compiler.extract_closed false in
def emptyUSize (n : USize) (h_pos : 0 < (n : USize)) : ShardedHashMapUSize α β n where
  h_numShards_pos := h_pos
  shards := .replicateUSize n (Std.HashMap.emptyWithCapacity 8)
  h_in_correct_shard := by
    simp only [VectorUSize.replicateUSize, VectorUSize.uget, Array.uget]
    intros ; simp at *

theorem empty_eq_emptyUSize (n : Nat) (h_pos : 0 < USize.ofNat n) (h_small : n < USize.size) :
  empty n h_pos h_small = emptyUSize (α := α) (β := β) n.toUSize h_pos := by
  simp [empty, emptyUSize] ; apply VectorUSize.replicate_eq_replicateUSize

def size (shs : ShardedHashMapUSize α β numShards) : Nat :=
  shs.shards.val.foldl (init := 0) fun acc shard => acc + shard.size

@[inline]
def getShard (shs : ShardedHashMapUSize α β numShards) (x : α) : HashMap α β :=
  shs.shards.ugetViaHash x shs.h_numShards_pos

@[inline]
def contains (shs : ShardedHashMapUSize α β numShards) (x : α) : Bool :=
  (shs.getShard x).contains x

@[inline]
def get? (shs : ShardedHashMapUSize α β numShards) (x : α) : Option β :=
  (shs.getShard x)[x]?

/-- The keys. -/
@[inline]
def toList (shs : ShardedHashMapUSize α β numShards) : List α :=
  shs.shards.val.toList.flatMap (·.keys)

@[inline]
instance instMembership : Membership α (ShardedHashMapUSize α β numShards) where
  mem shs x := x ∈ shs.getShard x

theorem mem_def {shs : ShardedHashMapUSize α β numShards} {x : α} :
    x ∈ shs ↔ x ∈ shs.getShard x := Iff.rfl

theorem mem_iff_exists_shard {shs : ShardedHashMapUSize α β numShards} {x : α} :
    x ∈ shs ↔ ∃ shard ∈ shs.shards.val.toList, x ∈ shard := by
  simp only [mem_def, getShard, VectorUSize.ugetViaHash, VectorUSize.uget, Array.uget]
  constructor
  · intro hx
    exact ⟨_, Array.mem_toList_iff.mpr (Array.getElem_mem ..), hx⟩
  · rintro ⟨shard, hshard, hx⟩
    rw [List.mem_iff_getElem] at hshard
    obtain ⟨i, hi, rfl⟩ := hshard
    simp only [Array.getElem_toList] at hx
    have hi' : i < shs.shards.val.size := by simpa using hi
    have hi_ns : i < numShards.toNat := by rw [← shs.shards.property]; exact hi'
    have hiU : i < USize.size := Nat.lt_trans hi_ns (USize.toNat_lt_size numShards)
    have h_toNat_i : (USize.ofNat i).toNat = i := Nat.mod_eq_of_lt hiU
    have h_lt : USize.ofNat i < numShards := by
      rw [USize.lt_iff_toNat_lt, h_toNat_i]; exact hi_ns
    have h_idx := shs.h_in_correct_shard (USize.ofNat i) h_lt x (by
      simp only [VectorUSize.uget, Array.uget, h_toNat_i]; exact hx)
    have h_eq : (shardIdxOfUSize numShards x).toNat = i :=
      (congrArg USize.toNat h_idx).trans h_toNat_i
    simp only [h_eq]; exact hx

theorem contains_iff_mem {shs : ShardedHashMapUSize α β numShards} {x : α} :
    shs.contains x = true ↔ x ∈ shs := by
  unfold contains ; rw [mem_def, HashMap.mem_iff_contains]

theorem mem_iff_isSome_get? [EquivBEq α] [LawfulHashable α]
    {shs : ShardedHashMapUSize α β numShards} {x : α} :
    x ∈ shs ↔ (shs.get? x).isSome := by
  unfold get? ; rw [mem_def, HashMap.mem_iff_isSome_getElem?]

theorem not_mem_empty {n : Nat} {h_pos} {h_small} {x : α} :
    x ∉ ShardedHashMapUSize.empty n h_pos h_small (α := α) (β := β) := by
  simp [mem_def, empty, getShard, VectorUSize.ugetViaHash, VectorUSize.uget,
    VectorUSize.replicate, Array.uget, Array.getElem_replicate]

theorem not_mem_emptyUSize {n : USize} {h_pos} {x : α} :
    x ∉ ShardedHashMapUSize.emptyUSize n h_pos (α := α) (β := β) := by
  simp [mem_def, emptyUSize, getShard, VectorUSize.ugetViaHash, VectorUSize.uget,
    VectorUSize.replicateUSize, Array.uget, Array.getElem_replicate]

/-- Unconditionally insert a key with its value into the sharded hash map. -/
@[specialize 1 2 3]
def insert [LawfulBEq α] [LawfulHashable α]
    (shs : ShardedHashMapUSize α β numShards) (x : α) (v : β) :
    ShardedHashMapUSize α β numShards :=
  { h_numShards_pos := shs.h_numShards_pos,
    shards := shs.shards.umodifyViaHash x (fun shard => shard.insert x v) shs.h_numShards_pos,
    h_in_correct_shard := by
      intro j hj k hk
      simp only [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.uget, VectorUSize.uset,
        Array.uget, Array.uset, Array.getElem_set] at hk
      split at hk
      · -- j.toNat = idx.toNat (modified shard)
        rename_i heq ; rw [USize.toNat_inj] at heq
        simp [HashMap.mem_insert, heq] at hk
        rcases hk with hk | hk
        · grind
        · apply shs.h_in_correct_shard ; apply hk ; assumption
      · -- j.toNat ≠ idx.toNat (unchanged shard)
        apply shs.h_in_correct_shard ; apply hk ; assumption
    }

theorem length_toList [EquivBEq α] [LawfulHashable α]
    {shs : ShardedHashMapUSize α β numShards} :
    shs.size = shs.toList.length := by
  simp [size, toList, ← Array.foldl_toList, HashMap.length_keys,
    List.sum_eq_foldl, List.foldl_map]

theorem nodup_elements [LawfulBEq α] [LawfulHashable α]
    {shs : ShardedHashMapUSize α β numShards} :
    shs.toList.Nodup := by
  simp [toList, Veil.List.nodup_flatMap] ; constructor
  · intros ; apply Std.HashMap.nodup_keys
  · rw [List.pairwise_iff_getElem] ; intros i j hi hj hne
    whnf ; simp ; intro a hini hinj
    simp at hi hj
    have hi_ns : i < numShards.toNat := by rw [← shs.shards.property]; exact hi
    have hj_ns : j < numShards.toNat := by rw [← shs.shards.property]; exact hj
    have hiU : i < USize.size := Nat.lt_trans hi_ns (USize.toNat_lt_size numShards)
    have hjU : j < USize.size := Nat.lt_trans hj_ns (USize.toNat_lt_size numShards)
    have h_toNat_i : (USize.ofNat i).toNat = i := Nat.mod_eq_of_lt hiU
    have h_toNat_j : (USize.ofNat j).toNat = j := Nat.mod_eq_of_lt hjU
    have h_lt_i : USize.ofNat i < numShards := by
      rw [USize.lt_iff_toNat_lt, h_toNat_i]; exact hi_ns
    have h_lt_j : USize.ofNat j < numShards := by
      rw [USize.lt_iff_toNat_lt, h_toNat_j]; exact hj_ns
    have h1 := shs.h_in_correct_shard (USize.ofNat i) h_lt_i a (by
      simp only [VectorUSize.uget, Array.uget, h_toNat_i]; exact hini)
    have h2 := shs.h_in_correct_shard (USize.ofNat j) h_lt_j a (by
      simp only [VectorUSize.uget, Array.uget, h_toNat_j]; exact hinj)
    grind

@[simp]
theorem mem_insert [LawfulBEq α] [LawfulHashable α]
    {shs : ShardedHashMapUSize α β numShards} {x y : α} {v : β} :
    x ∈ shs.insert y v ↔ (y == x) = true ∨ x ∈ shs := by
  unfold insert
  rw [mem_def, mem_def]
  unfold getShard
  simp [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.ugetViaHash, VectorUSize.uget, VectorUSize.uset,
    Array.uget, Array.uset, Array.getElem_set]
  grind

theorem get?_insert [LawfulBEq α] [LawfulHashable α]
    {shs : ShardedHashMapUSize α β numShards} {x y : α} {v : β} :
    (shs.insert y v).get? x = if y == x then some v else shs.get? x := by
  unfold insert get? getShard
  simp [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.ugetViaHash, VectorUSize.uget, VectorUSize.uset,
    Array.uget, Array.uset, Array.getElem_set]
  grind

end ShardedHashMapUSize


namespace ShardedMapUSize

/-! ## Inserting a sharded `HashMap` -/

variable {α : Type u} {β : Type v} {S : Type w} [BEq α] [Hashable α] [Membership α S] [MapShard α β S]

/-- Insert the bindings of a sharded hash map, shard by shard. -/
@[inline]
def insertManySHM (st : ShardedMapUSize α β S) (shm : ShardedHashMapUSize α β st.numShards) :
    ShardedMapUSize α β S :=
  st.insertManySharded shm.shards

theorem get?_insertManySHM [LawfulBEq α] [LawfulHashable α] {st : ShardedMapUSize α β S}
    {shm : ShardedHashMapUSize α β st.numShards} {k : α} :
    (st.insertManySHM shm).get? k = (shm.get? k).or (st.get? k) := by
  simp only [insertManySHM, get?_insertManySharded, ShardedHashMapUSize.get?, ShardedHashMapUSize.getShard]

theorem mem_insertManySHM [LawfulBEq α] [LawfulHashable α] {st : ShardedMapUSize α β S}
    {shm : ShardedHashMapUSize α β st.numShards} {k : α} :
    k ∈ st.insertManySHM shm ↔ k ∈ st ∨ k ∈ shm := by
  simp only [insertManySHM, mem_insertManySharded, ShardedHashMapUSize.mem_def, ShardedHashMapUSize.getShard]

end ShardedMapUSize
