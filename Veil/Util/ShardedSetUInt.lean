module

public import Veil.Util.TreeSetMisc
public import Veil.Util.List
meta import Veil.Util.Tactics

@[expose] public section

/-! # Sharded Set

    Using `USize`-based sharding to skip the conversion from and to `Nat`. The sharded sets are all
    `ShardedUSize`, for different types of shards.
-/

open Std

/-! ## UInt operations for sharding -/

namespace Array

@[inline]
unsafe def modifyInBoundUnsafe (xs : Array α) (i : Nat) (f : α → α) (h_lt : i < xs.size) : Array α :=
  let v                := xs[i]'h_lt
  -- Replace a[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
  -- Note: we assume that arrays have a uniform representation irrespective
  -- of the element type, and that it is valid to store `box(0)` in any array.
  let xs'               := xs.set i (unsafeCast ()) h_lt
  let v := f v
  xs'.set i v (Nat.lt_of_lt_of_eq h_lt (size_set ..).symm)

@[implemented_by modifyInBoundUnsafe]
def modifyInBound (xs : Array α) (i : Nat) (f : α → α) (h_lt : i < xs.size) : Array α :=
  let v := xs[i]'h_lt
  xs.set i (f v) h_lt

theorem size_modifyInBound {xs : Array α} {i : Nat} {f : α → α} {h_lt : i < xs.size} :
  (modifyInBound xs i f h_lt).size = xs.size := by
  simp only [modifyInBound, size_set]

end Array

namespace Vector

@[inline]
def modify {α : Type u} {n : Nat} (v : Vector α n) (i : Nat) (f : α → α) (h_lt : i < n) : Vector α n :=
  ⟨v.toArray.modifyInBound i f (v.size_toArray.symm ▸ h_lt),
   (Eq.trans Array.size_modifyInBound v.size_toArray)⟩

end Vector

namespace ShardedSetUInt

variable {α : Type u} [Hashable α]

/-- Compute the shard index for a given key. -/
@[inline, specialize]
def shardIdxOfUSize (numShards : USize) (k : α) : USize :=
  (hash k).toUSize % numShards

theorem shardIdxOfUSize_lt {numShards : USize} (k : α) (h_pos : 0 < numShards) :
  shardIdxOfUSize numShards k < numShards := Nat.mod_lt _ h_pos

end ShardedSetUInt

/-- A positive `USize`, such as a number of shards. At run time, it is just the `USize`. -/
abbrev PosUSize := { n : USize // 0 < n }

/-! ## Vector using UInt-based operations -/

/-- Similar to `Vector`, but with `USize` indices and size. -/
abbrev VectorUSize (α : Type u) (n : USize) := { arr : Array α // arr.size = n.toNat }

namespace VectorUSize

theorem usize_eq (v : VectorUSize α n) : v.val.usize = n := by
  rcases v with ⟨arr, h_size⟩
  simp only [Array.usize, h_size, Nat.toUSize_eq, USize.ofNat_toNat]

@[inline]
def replicate (h_small : n < USize.size) (x : α) : VectorUSize α n.toUSize :=
  ⟨Array.replicate n x, by simp only [Array.size_replicate] ; symm ; exact USize.toNat_ofNat_of_lt h_small⟩

@[inline]
def replicateUSize (n : USize) (x : α) : VectorUSize α n :=
  ⟨Array.replicate n.toNat x, by simp⟩

theorem replicate_eq_replicateUSize (h_small : n < USize.size) (x : α) :
  replicate h_small x = replicateUSize n.toUSize x := by
  simp only [replicate, replicateUSize]
  congr ; rw [USize.toNat_ofNat_of_lt' h_small]

-- theorem replicateUSize_eq_replicate (x : α) :
--   replicateUSize n x = replicate h_small x := by
--   simp only [replicate, replicateUSize]
--   congr ; rw [USize.toNat_ofNat_of_lt' h_small]

@[inline]
def uget (v : VectorUSize α n) (i : USize) (h_lt : i < n) : α :=
  v.val.uget i (v.property.symm ▸ h_lt)

@[inline]
def uset (v : VectorUSize α n) (i : USize) (x : α) (h_lt : i < n) : VectorUSize α n :=
  ⟨v.val.uset i x (v.property.symm ▸ h_lt), Eq.trans (Array.size_uset (v.property.symm ▸ h_lt)) v.property⟩

-- NOTE: If not using `umodifyUnsafe`, in-place modification would be very
-- difficult to achieve
/-- Modify the element at index `i` by applying `f` to it, returning a new vector.
This is implemented in the way as `Array.modifyMUnsafe` to allow for in-place
modification when possible. -/
@[inline]
unsafe def umodifyUnsafe (v : VectorUSize α n) (i : USize) (f : α → α) (h_lt : i < n) : VectorUSize α n :=
  let y                := v.uget i h_lt
  -- Replace a[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
  -- Note: we assume that arrays have a uniform representation irrespective
  -- of the element type, and that it is valid to store `box(0)` in any array.
  let v'               := v.uset i (unsafeCast ()) h_lt
  let y := f y
  v'.uset i y h_lt

@[implemented_by umodifyUnsafe]
def umodify (v : VectorUSize α n) (i : USize) (f : α → α) (h_lt : i < n) : VectorUSize α n :=
  let y := v.uget i h_lt
  v.uset i (f y) h_lt

open ShardedSetUInt

@[inline, specialize]
def ugetViaHash [Hashable β] (v : VectorUSize α n) (x : β) (h_pos : 0 < n) : α :=
  let idx := shardIdxOfUSize n x
  v.uget idx (shardIdxOfUSize_lt x h_pos)

@[inline, specialize]
def usetViaHash [Hashable β] (v : VectorUSize α n) (x : β) (y : α) (h_pos : 0 < n) : VectorUSize α n :=
  let idx := shardIdxOfUSize n x
  v.uset idx y (shardIdxOfUSize_lt x h_pos)

@[inline, specialize]
def umodifyViaHash [Hashable β] (v : VectorUSize α n) (x : β) (f : α → α) (h_pos : 0 < n) : VectorUSize α n :=
  let idx := shardIdxOfUSize n x
  v.umodify idx f (shardIdxOfUSize_lt x h_pos)

end VectorUSize

/-! ## Sharded collections -/

/-- The operations, and their specifications, that every sharded collection needs from the type `S`
of its shards. `SetShard` extends it with what the sharded sets need. -/
class KeyShard (α : Type u) (S : Type v) [Membership α S] where
  contains : S → α → Bool
  size : S → Nat
  contains_iff_mem {s : S} {k : α} : contains s k = true ↔ k ∈ s

/-- Keys of type `α` split into `numShards` shards of type `S` by their hash: each key is in the
shard at index `shardIdxOfUSize numShards k`. The sharded sets are this structure, for different
types of shards. Since `numShards` is a parameter, it is just the array of shards at run time. -/
structure ShardedUSize (α : Type u) (S : Type v) [Hashable α] [Membership α S] (numShards : PosUSize) where
  shards : VectorUSize S numShards
  h_in_correct_shard : ∀ (i : USize) (h : i < numShards), ∀ k ∈ shards.uget i h,
    ShardedSetUInt.shardIdxOfUSize numShards k = i

namespace ShardedUSize

open ShardedSetUInt

variable {α : Type u} {S : Type v} {T : Type w} [Hashable α] [Membership α S] [Membership α T]
  {numShards : PosUSize}

/-! ### Basic operations -/

/-- Get the shard for a given key. -/
@[inline]
def getShard (st : ShardedUSize α S numShards) (k : α) : S :=
  st.shards.ugetViaHash k numShards.property

-- NOTE: `Membership.mem` has signature `γ → α → Prop` (container first, element second)
instance instMembership : Membership α (ShardedUSize α S numShards) where
  mem st k := k ∈ st.getShard k

theorem mem_def {st : ShardedUSize α S numShards} {k : α} :
    k ∈ st ↔ k ∈ st.getShard k := Iff.rfl

/-- The shard at index `i` is the shard of each of its keys. -/
theorem shardIdx_toNat_of_mem {st : ShardedUSize α S numShards} {i : Nat}
    (hi' : i < st.shards.val.size) {k : α} (hk : k ∈ st.shards.val[i]) :
    (shardIdxOfUSize numShards k).toNat = i := by
  have hi_ns : i < numShards.val.toNat := by rw [← st.shards.property]; exact hi'
  have hiU : i < USize.size := Nat.lt_trans hi_ns (USize.toNat_lt_size numShards.val)
  have h_toNat_i : (USize.ofNat i).toNat = i := Nat.mod_eq_of_lt hiU
  have h_lt : USize.ofNat i < numShards := by
    rw [USize.lt_iff_toNat_lt, h_toNat_i]; exact hi_ns
  have h_idx := st.h_in_correct_shard (USize.ofNat i) h_lt k (by
    simp only [VectorUSize.uget, Array.uget, h_toNat_i]; exact hk)
  exact (congrArg USize.toNat h_idx).trans h_toNat_i

theorem mem_iff_exists_shard {st : ShardedUSize α S numShards} {k : α} :
    k ∈ st ↔ ∃ shard ∈ st.shards.val.toList, k ∈ shard := by
  simp only [mem_def, getShard, VectorUSize.ugetViaHash, VectorUSize.uget, Array.uget]
  constructor
  · intro hk
    exact ⟨_, Array.mem_toList_iff.mpr (Array.getElem_mem ..), hk⟩
  · rintro ⟨shard, hshard, hk⟩
    rw [List.mem_iff_getElem] at hshard
    obtain ⟨i, hi, rfl⟩ := hshard
    simp only [Array.getElem_toList] at hk
    have hi' : i < st.shards.val.size := by simpa using hi
    have h_eq := shardIdx_toNat_of_mem hi' hk
    simp only [h_eq]; exact hk

/-- No key is listed twice if each shard lists its keys with `keys` without duplicates. -/
theorem nodup_flatMap {st : ShardedUSize α S numShards} {keys : S → List α}
    (h_mem : ∀ s k, k ∈ keys s ↔ k ∈ s) (h_nodup : ∀ s, (keys s).Nodup) :
    (st.shards.val.toList.flatMap keys).Nodup := by
  simp [Veil.List.nodup_flatMap] ; constructor
  · intros ; apply h_nodup
  · rw [List.pairwise_iff_getElem] ; intros i j hi hj hne
    whnf ; simp [h_mem] ; intro a hini hinj
    simp at hi hj
    have h1 := shardIdx_toNat_of_mem hi hini
    have h2 := shardIdx_toNat_of_mem hj hinj
    grind

section KeyShard

variable [KeyShard α S]

@[inline]
def contains (st : ShardedUSize α S numShards) (k : α) : Bool :=
  KeyShard.contains (st.getShard k) k

/-- Total number of keys across all shards. -/
def size (st : ShardedUSize α S numShards) : Nat :=
  st.shards.val.foldl (init := 0) fun acc shard => acc + KeyShard.size (α := α) shard

theorem contains_iff_mem {st : ShardedUSize α S numShards} {k : α} :
    st.contains k = true ↔ k ∈ st := by
  unfold contains ; rw [mem_def, KeyShard.contains_iff_mem]

theorem not_contains_iff_not_mem {st : ShardedUSize α S numShards} {k : α} :
    st.contains k = false ↔ k ∉ st := by
  rw [← contains_iff_mem] ; grind

/-- The size is the number of keys of all shards, listed by `keys`. -/
theorem size_eq_length_flatMap {st : ShardedUSize α S numShards} {keys : S → List α}
    (h : ∀ s, KeyShard.size (α := α) s = (keys s).length) :
    st.size = (st.shards.val.toList.flatMap keys).length := by
  simp [size, ← Array.foldl_toList, h, List.sum_eq_foldl, List.foldl_map]

end KeyShard

/-! ### Building and updating shards

Each operation states what it may do to the keys of a shard, so that the keys stay in their
shards. -/

/-- `numShards` copies of a shard without keys. -/
@[inline]
def replicate (s : S) (h : ∀ k : α, k ∉ s) : ShardedUSize α S numShards where
  shards := .replicateUSize numShards s
  h_in_correct_shard := by
    simp only [VectorUSize.replicateUSize, VectorUSize.uget, Array.uget]
    intros ; simp_all

theorem not_mem_replicate {s : S} {h : ∀ k : α, k ∉ s} {k : α} :
    k ∉ replicate (numShards := numShards) s h := by
  simp [mem_def, replicate, getShard, VectorUSize.ugetViaHash, VectorUSize.uget,
    VectorUSize.replicateUSize, Array.uget, Array.getElem_replicate, h]

/-- Apply `f` to the shard of `k`, in place if that shard is not shared. `f` may add only keys of
that shard. -/
@[inline]
def modifyShard (st : ShardedUSize α S numShards) (k : α) (f : S → S)
    (hf : ∀ s q, q ∈ f s → q ∈ s ∨ shardIdxOfUSize numShards q = shardIdxOfUSize numShards k) :
    ShardedUSize α S numShards where
  shards := st.shards.umodifyViaHash k f numShards.property
  h_in_correct_shard := by
    intro j hj q hq
    simp only [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.uget, VectorUSize.uset,
      Array.uget, Array.uset, Array.getElem_set] at hq
    split at hq
    · -- j.toNat = idx.toNat (modified shard)
      rename_i heq ; rw [USize.toNat_inj] at heq
      simp [heq] at hq
      rcases hf _ _ hq with hq | hq
      · apply st.h_in_correct_shard ; apply hq ; assumption
      · grind
    · -- j.toNat ≠ idx.toNat (unchanged shard)
      apply st.h_in_correct_shard ; apply hq ; assumption

/-- Apply `f` to each shard, each in a task of its own. `f` may not add keys. -/
@[specialize]
def mapShardsPar (st : ShardedUSize α S numShards) (f : S → T) (hf : ∀ s k, k ∈ f s → k ∈ s) :
    ShardedUSize α T numShards :=
  let tasks := st.shards.val.toList.map fun s => Task.spawn fun () => f s
  let shardArr := tasks.map Task.get
  { shards := ⟨shardArr.toArray, by simp [shardArr, tasks, st.shards.property]⟩
    h_in_correct_shard := by
      intro i hi k hk
      simp [shardArr, tasks, VectorUSize.uget, Array.uget, Task.spawn] at hk
      exact st.h_in_correct_shard i hi k (hf _ _ hk) }

-- NOTE: The IR of this function seems to contain a lot of things, but
-- should be fine after specialization?
/-- Combine each shard with the shard of `other` at the same index, each pair in a task of its
own. `f` may add only keys of either.

NOTE: `Array.toList` takes the array of `st`, so that this function owns it and frees it before
spawning the tasks: each shard is then unshared and `f` can update it in place. Zipping the arrays
directly would only borrow it, keeping the shards shared until all tasks are done. -/
@[specialize]
def zipShardsPar (st : ShardedUSize α S numShards) (other : ShardedUSize α T numShards)
    (f : S → T → S) (hf : ∀ s t k, k ∈ f s t → k ∈ s ∨ k ∈ t) : ShardedUSize α S numShards :=
  let pairs := st.shards.val.toList.zip other.shards.val.toList
  let tasks := pairs.map fun (s, t) => Task.spawn fun () => f s t
  let shardArr := tasks.map Task.get
  { shards := ⟨shardArr.toArray, by
      simp [shardArr, tasks, pairs, st.shards.property, other.shards.property]⟩
    h_in_correct_shard := by
      intro i hi k hk
      simp [shardArr, tasks, pairs, VectorUSize.uget, Array.uget, Task.spawn] at hk
      rcases hf _ _ _ hk with hk | hk
      · exact st.h_in_correct_shard i hi k hk
      · exact other.h_in_correct_shard i hi k hk }

end ShardedUSize

/-! ## Sharded sets -/

/-- The operations, and their specifications, that a `ShardedSetUSize` needs from the set type `S`
of its shards, beyond those of `KeyShard`. `insertMany` adds a whole `HashSet`: the parallel search
collects the new states of a BFS level per shard and then adds them to each shard in one go. -/
class SetShard (α : Type u) (S : Type v) [BEq α] [Hashable α] [Membership α S] extends KeyShard α S where
  /-- A shard holding the elements of a list. -/
  ofList : List α → S
  insertMany : S → HashSet α → S
  mem_ofList {l : List α} {k : α} : k ∈ ofList l ↔ k ∈ l
  mem_insertMany {s : S} {hs : HashSet α} {k : α} : k ∈ insertMany s hs ↔ k ∈ s ∨ k ∈ hs

/-- `Std.TreeSet` ordered by `compare`, as the set type of shards: the default for the parallel search's
seen set, and the one that takes the least memory (`HAMTKeysShard` and `HAMTShard` are faster). -/
abbrev TreeSetShard (α : Type u) [Ord α] := TreeSet α compare

instance [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulBEq α] [Hashable α] :
    SetShard α (TreeSetShard α) where
  ofList l := TreeSet.ofListFast l compare
  contains := TreeSet.contains
  insertMany s hs := s.insertManyFast hs
  size := TreeSet.size
  contains_iff_mem := TreeSet.mem_iff_contains.symm
  mem_ofList := by simp [TreeSet.mem_ofListFast]
  mem_insertMany := by intros ; simp only [TreeSet.mem_insertManyFast_hashset, HashSet.mem_iff_contains]

instance [BEq α] [Hashable α] : KeyShard α (HashSet α) where
  contains := HashSet.contains
  size := HashSet.size
  contains_iff_mem := HashSet.mem_iff_contains.symm

/-- A set split into shards of type `S` by the hash of each key, with `USize`-based sharding. -/
abbrev ShardedSetUSize (α : Type u) (S : Type v) [Hashable α] [Membership α S] (numShards : PosUSize) :=
  ShardedUSize α S numShards

/-- A sharded set with `HashSet` shards. -/
abbrev ShardedHashSetUSize (α : Type u) [BEq α] [Hashable α] (numShards : PosUSize) :=
  ShardedSetUSize α (HashSet α) numShards

namespace ShardedSetUSize

open ShardedSetUInt

variable {α : Type u} {S : Type v} [Hashable α] {numShards : PosUSize}

/-! ### Distribute: single-pass bucketing -/

/-- Consing a key onto a bucket adds only a key of its shard. -/
theorem mem_cons_shardIdx (x : α) (s : List α) (q : α) (h : q ∈ x :: s) :
    q ∈ s ∨ shardIdxOfUSize numShards q = shardIdxOfUSize numShards x := by
  rcases List.mem_cons.mp h with rfl | h
  · exact .inr rfl
  · exact .inl h

/-- The keys of `l`, bucketed by shard. -/
@[specialize]
def distributeByHash (l : List α) : ShardedUSize α (List α) numShards :=
  l.foldl (init := .replicate [] fun _ => List.not_mem_nil) fun st x =>
    st.modifyShard x (List.cons x) (mem_cons_shardIdx x)

theorem mem_distributeByHash {l : List α} {k : α} :
    k ∈ distributeByHash (numShards := numShards) l ↔ k ∈ l := by
  simp only [ShardedUSize.mem_def, ShardedUSize.getShard, distributeByHash, VectorUSize.ugetViaHash]
  rw [List.foldl_eq_foldr_reverse]
  rewrite (occs := .neg [1]) [← List.mem_reverse]
  generalize l.reverse = l' ; clear l
  induction l' with
  | nil => simp [ShardedUSize.replicate, VectorUSize.replicateUSize, VectorUSize.uget]
  | cons x l' ih =>
    simp only [List.foldr, List.mem_cons, ← ih]
    generalize (List.foldr _ _ l') = acc ; clear ih
    simp only [ShardedUSize.modifyShard, VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.uset, VectorUSize.uget, Array.uget, Array.uset, Array.getElem_set]
    split <;> grind

variable [BEq α] [Membership α S] [SetShard α S]

/-! ### Parallel construction from list -/

/-- Build a `ShardedSetUSize` from a list by distributing elements into shards by hash,
    then building each shard in parallel using `Task.spawn`. -/
@[specialize]
def ofListByHash (l : List α) : ShardedSetUSize α S numShards :=
  (distributeByHash l).mapShardsPar SetShard.ofList fun _ _ h => SetShard.mem_ofList.mp h

theorem mem_ofListByHash {l : List α} {k : α} :
    k ∈ ofListByHash (S := S) (numShards := numShards) l ↔ k ∈ l := by
  simp [ShardedUSize.mem_def, ofListByHash, ShardedUSize.mapShardsPar, ShardedUSize.getShard, Task.spawn,
    VectorUSize.ugetViaHash, VectorUSize.uget, SetShard.mem_ofList]
  exact mem_distributeByHash

/-! ### Sharded insertion -/

/-- Insert the keys of a sharded `HashSet` shard by shard, each shard in a task of its own. -/
@[inline]
def insertMany (st : ShardedSetUSize α S numShards) (items : ShardedHashSetUSize α numShards) :
    ShardedSetUSize α S numShards :=
  st.zipShardsPar items SetShard.insertMany fun _ _ _ h => SetShard.mem_insertMany.mp h

theorem mem_insertMany {st : ShardedSetUSize α S numShards} {items : ShardedHashSetUSize α numShards}
    {k : α} : k ∈ st.insertMany items ↔ k ∈ st ∨ k ∈ items := by
  simp [ShardedUSize.mem_def, insertMany, ShardedUSize.zipShardsPar, ShardedUSize.getShard, Task.spawn,
    VectorUSize.ugetViaHash, VectorUSize.uget, SetShard.mem_insertMany]

end ShardedSetUSize

namespace ShardedHashSetUSize

variable {α : Type u} [BEq α] [Hashable α] {numShards : PosUSize}

/-- The empty set with `numShards` shards. -/
def empty : ShardedHashSetUSize α numShards :=
  .replicate (HashSet.emptyWithCapacity 8) fun _ => HashSet.not_mem_emptyWithCapacity

theorem not_mem_empty {x : α} : x ∉ (empty : ShardedHashSetUSize α numShards) :=
  ShardedUSize.not_mem_replicate

/-- Unconditionally insert an element into the sharded hash set. -/
@[specialize 1 2 3]
def insert [LawfulBEq α] [LawfulHashable α] (shs : ShardedHashSetUSize α numShards) (x : α) :
    ShardedHashSetUSize α numShards :=
  shs.modifyShard x (·.insert x) fun _ k hk => by
    simp [HashSet.mem_insert] at hk
    rcases hk with hk | hk
    · grind
    · exact .inl hk

@[simp]
theorem mem_insert [LawfulBEq α] [LawfulHashable α]
    {shs : ShardedHashSetUSize α numShards} {x y : α} :
    x ∈ shs.insert y ↔ (y == x) = true ∨ x ∈ shs := by
  unfold insert ShardedUSize.modifyShard
  rw [ShardedUSize.mem_def, ShardedUSize.mem_def]
  unfold ShardedUSize.getShard
  simp [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.ugetViaHash, VectorUSize.uget, VectorUSize.uset,
    Array.uget, Array.uset, Array.getElem_set]
  grind

/-- The keys. -/
@[inline]
def toList (shs : ShardedHashSetUSize α numShards) : List α :=
  shs.shards.val.toList.flatMap (·.toList)

theorem length_toList [EquivBEq α] [LawfulHashable α]
    {shs : ShardedHashSetUSize α numShards} :
    shs.size = shs.toList.length :=
  ShardedUSize.size_eq_length_flatMap fun _ => HashSet.length_toList.symm

theorem nodup_elements [LawfulBEq α] [LawfulHashable α]
    {shs : ShardedHashSetUSize α numShards} :
    shs.toList.Nodup :=
  ShardedUSize.nodup_flatMap (fun _ _ => HashSet.mem_toList) fun _ => HashMap.nodup_keys

end ShardedHashSetUSize
