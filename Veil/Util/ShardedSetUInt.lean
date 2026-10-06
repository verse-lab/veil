module

public import Veil.Util.TreeSetMisc
public import Veil.Util.List
meta import Veil.Util.Tactics

@[expose] public section

/-! # Sharded Set

    Using `USize`-based sharding to skip the conversion from and to `Nat`.
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

/-! ## Shards -/

/-- The operations, and their specifications, that a `ShardedSetUSize` needs from the set type `S`
of its shards. `insertMany` adds a whole `HashSet`: the parallel search collects the new states of
a BFS level per shard and then adds them to each shard in one go. -/
class SetShard (α : Type u) (S : Type v) [BEq α] [Hashable α] [Membership α S] where
  /-- A shard holding the elements of a list. -/
  ofList : List α → S
  contains : S → α → Bool
  insertMany : S → HashSet α → S
  size : S → Nat
  contains_iff_mem {s : S} {k : α} : contains s k = true ↔ k ∈ s
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

/-- A set split into shards of type `S` by the hash of each key, with `USize`-based sharding. -/
structure ShardedSetUSize (α : Type u) (S : Type v) where
  numShards : USize
  h_numShards_pos : 0 < (numShards : USize)
  shards : VectorUSize S numShards

namespace ShardedSetUSize

open ShardedSetUInt

variable {α : Type u} {S : Type v}

/-! ## Basic operations -/

/-- Get the shard for a given key. -/
@[inline]
def getShard [Hashable α] (st : ShardedSetUSize α S) (k : α) : S :=
  st.shards.ugetViaHash k st.h_numShards_pos

-- NOTE: `Membership.mem` has signature `γ → α → Prop` (container first, element second)
instance instMembership [Hashable α] [Membership α S] : Membership α (ShardedSetUSize α S) where
  mem st k := k ∈ st.getShard k

theorem mem_def [Hashable α] [Membership α S] {st : ShardedSetUSize α S} {k : α} :
    k ∈ st ↔ k ∈ st.getShard k := Iff.rfl

section

variable [BEq α] [Hashable α] [Membership α S] [SetShard α S]

@[inline]
def contains (st : ShardedSetUSize α S) (k : α) : Bool :=
  SetShard.contains (st.getShard k) k

/-- Total number of elements across all shards. -/
def size (st : ShardedSetUSize α S) : Nat :=
  st.shards.val.foldl (init := 0) fun acc shard => acc + SetShard.size (α := α) shard

theorem contains_iff_mem {st : ShardedSetUSize α S} {k : α} :
    st.contains k ↔ k ∈ st := by
  unfold contains ; rw [mem_def, SetShard.contains_iff_mem]

end

/-! ## Distribute: single-pass bucketing -/

@[specialize]
def distributeByHash [Hashable α] (l : List α) (numShards : Nat)
  (h_pos : 0 < USize.ofNat numShards := by native_decide)
  (h_small : numShards < USize.size := by native_decide) : VectorUSize (List α) numShards.toUSize :=
  l.foldl (init := VectorUSize.replicate h_small []) fun vec x =>
    vec.umodifyViaHash x (List.cons x) h_pos

-- Key membership theorem for distributeByHash
theorem distributeByHash_mem [Hashable α] [BEq α] [LawfulBEq α]
    {numShards : Nat} {h_pos} {h_small}
    {l : List α} {k : α} :
    let d := distributeByHash l numShards h_pos h_small
    k ∈ d.ugetViaHash (β := α) k h_pos ↔ k ∈ l := by
  simp only [distributeByHash, VectorUSize.ugetViaHash]
  rw [List.foldl_eq_foldr_reverse]
  rewrite (occs := .neg [1]) [← List.mem_reverse]
  generalize l.reverse = l' ; clear l
  induction l' with
  | nil => simp [VectorUSize.replicate, VectorUSize.uget]
  | cons x l' ih =>
    simp only [List.foldr, List.mem_cons, ← ih]
    generalize (List.foldr _ _ l') = acc ; clear ih l'
    simp only [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.uset, VectorUSize.uget, Array.uget, Array.uset, Array.getElem_set]
    split <;> grind

variable [BEq α] [Hashable α] [Membership α S] [SetShard α S]

/-! ## Parallel construction from list -/

/-- Build a `ShardedSetUSize` from a list by distributing elements into shards by hash,
    then building each shard in parallel using `Task.spawn`. -/
@[specialize]
def ofListByHash
  (l : List α) (numShards : Nat)
  (h_pos : 0 < USize.ofNat numShards := by native_decide)
  (h_small : numShards < USize.size := by native_decide) : ShardedSetUSize α S :=
  let ⟨buckets, h_buckets⟩ := distributeByHash l numShards h_pos h_small
  let tasks := buckets.toList.map fun bucket =>
    Task.spawn fun () => SetShard.ofList (S := S) bucket
  let shardArr := tasks.map Task.get
  ⟨USize.ofNat numShards, h_pos, ⟨shardArr.toArray, by grind⟩⟩

private theorem ofListByHash_getShard
    {numShards : Nat} {h_pos} {h_small} {l : List α} (k : α) :
    (ofListByHash (S := S) l numShards h_pos h_small).getShard k =
      SetShard.ofList ((distributeByHash l numShards h_pos h_small).ugetViaHash k h_pos) := by
  simp [ofListByHash, getShard, Task.spawn, VectorUSize.ugetViaHash, VectorUSize.uget]

theorem mem_ofListByHash [LawfulBEq α]
    {numShards : Nat} {h_pos} {h_small} {l : List α} {k : α} :
    k ∈ ofListByHash (S := S) l numShards h_pos h_small ↔ k ∈ l := by
  simp only [mem_def, ofListByHash_getShard, SetShard.mem_ofList]
  exact distributeByHash_mem

/-! ## Sharded insertion -/

-- NOTE: The IR of this function seems to contain a lot of things, but
-- should be fine after specialization?
/-- Insert elements from a sharded `HashSet` vector into corresponding shards,
    parallelized via `Task.spawn`. -/
@[specialize]
def insertManySharded
    (st : ShardedSetUSize α S)
    (items : VectorUSize (HashSet α) st.numShards) :
    ShardedSetUSize α S :=
  let pairs := st.shards.val.zip items.val |>.toList
  let tasks := pairs.map fun (shard, hs) =>
    Task.spawn fun () => SetShard.insertMany shard hs
  let shardArr := tasks.map Task.get
  let newShards := ⟨shardArr.toArray, by simp [shardArr, tasks, pairs, st.shards.property, items.property]⟩
  { st with shards := newShards }

private theorem insertManySharded_getShard
    {st : ShardedSetUSize α S}
    {items : VectorUSize (HashSet α) st.numShards}
    (k : α) :
    (st.insertManySharded items).getShard k =
      SetShard.insertMany (st.getShard k) (items.ugetViaHash k st.h_numShards_pos) := by
  simp [insertManySharded, getShard, Task.spawn,
    VectorUSize.ugetViaHash, VectorUSize.uget]

theorem mem_insertManySharded
    {st : ShardedSetUSize α S}
    {items : VectorUSize (HashSet α) st.numShards}
    {k : α} :
    k ∈ st.insertManySharded items ↔
      k ∈ st ∨ k ∈ (items.ugetViaHash k st.h_numShards_pos) := by
  simp only [mem_def, insertManySharded_getShard, SetShard.mem_insertMany]

end ShardedSetUSize

/-- A sharded set implementation using `HashSet` as the underlying shard type,
with `USize`-based sharding. -/
structure ShardedHashSetUSize (α : Type u) [BEq α] [Hashable α] (numShards : USize) where
  h_numShards_pos : 0 < (numShards : USize)
  shards : VectorUSize (HashSet α) numShards
  h_in_correct_shard : ∀ (i : USize) (h : i < numShards), ∀ k ∈ shards.uget i h,
    ShardedSetUInt.shardIdxOfUSize numShards k = i

namespace ShardedHashSetUSize

open ShardedSetUInt

variable {α : Type u} [BEq α] [Hashable α] {numShards : USize}

set_option compiler.extract_closed false in
def empty (n : Nat)
  (h_pos : 0 < USize.ofNat n := by native_decide)
  (h_small : n < USize.size := by native_decide) : ShardedHashSetUSize α n.toUSize where
  h_numShards_pos := h_pos
  shards := .replicate h_small (Std.HashSet.emptyWithCapacity 8)
  h_in_correct_shard := by
    simp only [VectorUSize.replicate, VectorUSize.uget, Array.uget]
    intros ; simp at *

set_option compiler.extract_closed false in
def emptyUSize (n : USize) (h_pos : 0 < (n : USize)) : ShardedHashSetUSize α n where
  h_numShards_pos := h_pos
  shards := .replicateUSize n (Std.HashSet.emptyWithCapacity 8)
  h_in_correct_shard := by
    simp only [VectorUSize.replicateUSize, VectorUSize.uget, Array.uget]
    intros ; simp at *

theorem empty_eq_emptyUSize (n : Nat) (h_pos : 0 < USize.ofNat n) (h_small : n < USize.size) :
  empty n h_pos h_small = emptyUSize (α := α) n.toUSize h_pos := by
  simp [empty, emptyUSize] ; apply VectorUSize.replicate_eq_replicateUSize

def size (shs : ShardedHashSetUSize α numShards) : Nat :=
  shs.shards.val.foldl (init := 0) fun acc shard => acc + shard.size

@[inline]
def getShard (shs : ShardedHashSetUSize α numShards) (x : α) : HashSet α :=
  shs.shards.ugetViaHash x shs.h_numShards_pos

@[inline]
def contains (shs : ShardedHashSetUSize α numShards) (x : α) : Bool :=
  (shs.getShard x).contains x

@[inline]
def toList (shs : ShardedHashSetUSize α numShards) : List α :=
  shs.shards.val.toList.flatMap (·.toList)

@[inline]
instance instMembership : Membership α (ShardedHashSetUSize α numShards) where
  mem shs x := shs.getShard x |>.contains x

theorem mem_def {shs : ShardedHashSetUSize α numShards} {x : α} :
    x ∈ shs ↔ x ∈ shs.getShard x := Iff.rfl

theorem mem_iff_exists_shard {shs : ShardedHashSetUSize α numShards} {x : α} :
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

theorem contains_iff_mem {shs : ShardedHashSetUSize α numShards} {x : α} :
    shs.contains x = true ↔ x ∈ shs := by
  unfold contains ; rw [mem_def, HashSet.mem_iff_contains]

theorem not_mem_empty {n : Nat} {h_pos} {h_small} {x : α} :
    x ∉ ShardedHashSetUSize.empty n h_pos h_small (α := α) := by
  simp [mem_def, empty, getShard, VectorUSize.ugetViaHash, VectorUSize.uget,
    VectorUSize.replicate, Array.uget, Array.getElem_replicate]

theorem not_mem_emptyUSize {n : USize} {h_pos} {x : α} :
    x ∉ ShardedHashSetUSize.emptyUSize n h_pos (α := α) := by
  simp [mem_def, emptyUSize, getShard, VectorUSize.ugetViaHash, VectorUSize.uget,
    VectorUSize.replicateUSize, Array.uget, Array.getElem_replicate]

/-- Unconditionally insert an element into the sharded hash set. -/
@[specialize 1 2 3]
def insert [LawfulBEq α] [LawfulHashable α]
    (shs : ShardedHashSetUSize α numShards) (x : α) :
    ShardedHashSetUSize α numShards :=
  { h_numShards_pos := shs.h_numShards_pos,
    shards := shs.shards.umodifyViaHash x (fun shard => shard.insert x) shs.h_numShards_pos,
    h_in_correct_shard := by
      intro j hj k hk
      simp only [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.uget, VectorUSize.uset,
        Array.uget, Array.uset, Array.getElem_set] at hk
      split at hk
      · -- j.toNat = idx.toNat (modified shard)
        rename_i heq ; rw [USize.toNat_inj] at heq
        simp [HashSet.mem_insert, heq] at hk
        rcases hk with hk | hk
        · grind
        · apply shs.h_in_correct_shard ; apply hk ; assumption
      · -- j.toNat ≠ idx.toNat (unchanged shard)
        apply shs.h_in_correct_shard ; apply hk ; assumption
    }

theorem length_toList [EquivBEq α] [LawfulHashable α]
    {shs : ShardedHashSetUSize α numShards} :
    shs.size = shs.toList.length := by
  rcases shs with ⟨h_pos, ⟨shards, h_n⟩, h_ics⟩
  simp [size, ← Array.foldl_toList, toList, Std.HashSet.length_toList]
  rw [← Nat.add_zero (List.sum _)]
  generalize shards.toList = l
  generalize (0 : Nat) = acc
  clear h_pos h_n h_ics
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => simp ; grind

theorem nodup_elements [LawfulBEq α] [LawfulHashable α]
    {shs : ShardedHashSetUSize α numShards} :
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
    rw [h1] at h2
    have h_eq := congrArg USize.toNat h2
    rw [h_toNat_i, h_toNat_j] at h_eq
    omega

@[simp]
theorem mem_insert [LawfulBEq α] [LawfulHashable α]
    {shs : ShardedHashSetUSize α numShards} {x y : α} :
    x ∈ shs.insert y ↔ (y == x) = true ∨ x ∈ shs := by
  unfold insert
  rw [mem_def, mem_def]
  unfold getShard
  simp only [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.ugetViaHash, VectorUSize.uget, VectorUSize.uset,
    Array.uget, Array.uset, Array.getElem_set]
  constructor
  · intro hk
    split at hk
    · simp only [HashSet.mem_insert] at hk
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (by rename_i heq; simp only [← heq]; exact hk)
    · exact Or.inr hk
  · intro hk
    rcases hk with hk | hk
    · have := LawfulBEq.eq_of_beq hk ; subst x
      rw [if_pos rfl]; simp [HashSet.mem_insert]
    · split
      · rename_i heq
        simp [HashSet.mem_insert]; right
        have : (shardIdxOfUSize numShards x).toNat = (shardIdxOfUSize numShards y).toNat := heq.symm
        simp only [this] at hk; exact hk
      · exact hk

end ShardedHashSetUSize

namespace ShardedSetUSize

open ShardedHashSetUSize

/-! ## Sharded insertion from ShardedHashSet -/

variable {α : Type u} {S : Type v} [BEq α] [Hashable α] [Membership α S] [SetShard α S]

@[inline]
def insertManySHS (st : ShardedSetUSize α S) (shs : ShardedHashSetUSize α st.numShards) :
    ShardedSetUSize α S :=
  st.insertManySharded shs.shards

theorem mem_insertManySHS
    {st : ShardedSetUSize α S} {shs : ShardedHashSetUSize α st.numShards} {k : α} :
    k ∈ st.insertManySHS shs ↔ k ∈ st ∨ k ∈ shs := by
  simp only [insertManySHS, mem_insertManySharded, ShardedHashSetUSize.mem_def, ShardedHashSetUSize.getShard]

end ShardedSetUSize
