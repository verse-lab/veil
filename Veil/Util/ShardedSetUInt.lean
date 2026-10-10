module

public import Veil.Util.TreeSetMisc
public import Veil.Util.List
meta import Veil.Util.Tactics

@[expose] public section

/-! # Sharded Set

    Using `USize`-based sharding to skip the conversion from and to `Nat`. The sharded sets here and
    the sharded maps of `ShardedMapUInt` are all `ShardedUSize`, for different types of shards.
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
def replicateUSize (n : USize) (x : α) : VectorUSize α n :=
  ⟨Array.replicate n.toNat x, by simp⟩

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

@[inline]
def map (f : α → β) (v : VectorUSize α n) : VectorUSize β n :=
  ⟨v.val.map f, by simp [v.property]⟩

/-- Combine each element with the element of `w` at the same index, each pair in a task of its own.
Like `ShardedUSize.zipShardsPar`, it takes the arrays of `v` and `w` (`Array.toList`), so that each
element is unshared and `f` can update it in place. -/
@[specialize]
def zipPar (v : VectorUSize α n) (w : VectorUSize β n) (f : α → β → γ) : VectorUSize γ n :=
  let tasks := (v.val.toList.zip w.val.toList).map fun (a, b) => Task.spawn fun () => f a b
  ⟨(tasks.map Task.get).toArray, by simp [tasks, v.property, w.property]⟩

theorem uget_map {f : α → β} {v : VectorUSize α n} {i : USize} {h : i < n} :
    (v.map f).uget i h = f (v.uget i h) := by
  simp [map, uget, Array.uget]

theorem uget_zipPar {w : VectorUSize β n} {f : α → β → γ} {v : VectorUSize α n} {i : USize} {h : i < n} :
    (v.zipPar w f).uget i h = f (v.uget i h) (w.uget i h) := by
  simp [zipPar, uget, Array.uget, Task.spawn]

theorem ext_uget {v w : VectorUSize α n} (h : ∀ (i : USize) (hi : i < n), v.uget i hi = w.uget i hi) :
    v = w := by
  apply Subtype.ext ; apply Array.ext (by rw [v.property, w.property])
  intro j hj _
  have hj_ns : j < n.toNat := by simpa [v.property] using hj
  exact h (USize.ofNatLT j (Nat.lt_trans hj_ns n.toNat_lt_size)) hj_ns

theorem uget_replicateUSize {x : α} {i : USize} {h : i < n} :
    (replicateUSize n x).uget i h = x := by
  simp [replicateUSize, uget, Array.uget]

theorem uget_umodifyViaHash [Hashable β] {v : VectorUSize α n} {x : β} {f : α → α} {h_pos : 0 < n}
    {i : USize} {h : i < n} :
    (v.umodifyViaHash x f h_pos).uget i h =
      if shardIdxOfUSize n x = i then f (v.uget i h) else v.uget i h := by
  simp only [umodifyViaHash, umodify, uset, uget, Array.uget, Array.uset, Array.getElem_set]
  split <;> split <;> grind [USize.toNat_inj]

/-- `buckets` with each element of `l` put in front of the bucket of its key's shard. -/
@[specialize]
def distributeInto [Hashable β] (key : α → β) (h_pos : 0 < n) (buckets : VectorUSize (List α) n)
    (l : List α) : VectorUSize (List α) n :=
  l.foldl (init := buckets) fun buckets x => buckets.umodifyViaHash (key x) (x :: ·) h_pos

theorem mem_uget_distributeInto [Hashable β] {key : α → β} {h_pos : 0 < n}
    {buckets : VectorUSize (List α) n} {l : List α} {i : USize} {h : i < n} {x : α} :
    x ∈ (distributeInto key h_pos buckets l).uget i h ↔
      x ∈ buckets.uget i h ∨ (x ∈ l ∧ shardIdxOfUSize n (key x) = i) := by
  induction l generalizing buckets with
  | nil => simp [distributeInto]
  | cons y l ih =>
    simp only [distributeInto, List.foldl_cons] at ih ⊢
    rw [ih, uget_umodifyViaHash]
    split <;> grind

theorem mem_toList_iff {v : VectorUSize α n} {x : α} :
    x ∈ v.val.toList ↔ ∃ (i : USize) (h : i < n), v.uget i h = x := by
  constructor
  · intro hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hi, rfl⟩ := hmem
    have hi_ns : i < n.toNat := by simpa [v.property] using hi
    exact ⟨USize.ofNatLT i (Nat.lt_trans hi_ns n.toNat_lt_size), hi_ns, rfl⟩
  · rintro ⟨i, h, rfl⟩
    simp only [uget, Array.uget]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem ..)

/-- The keys of all shards are pairwise distinct, when each shard holds keys of its own index
only and has no duplicate keys itself. -/
theorem nodup_flatMap_of_shards [Hashable β] {v : VectorUSize α n} (keys : α → List β)
    (hsh : ∀ (i : USize) (h : i < n), ∀ k ∈ keys (v.uget i h), shardIdxOfUSize n k = i)
    (hnd : ∀ (i : USize) (h : i < n), (keys (v.uget i h)).Nodup) :
    (v.val.toList.flatMap keys).Nodup := by
  have hsh_nat (i : Nat) (hi : i < v.val.size) (k : β) (hk : k ∈ keys v.val[i]) :
      (shardIdxOfUSize n k).toNat = i := by
    have hi_ns : i < n.toNat := by simpa [v.property] using hi
    exact congrArg USize.toNat (hsh (USize.ofNatLT i (Nat.lt_trans hi_ns n.toNat_lt_size)) hi_ns k hk)
  rw [Veil.List.nodup_flatMap] ; constructor
  · intro l hl ; obtain ⟨i, h, rfl⟩ := mem_toList_iff.mp hl ; exact hnd i h
  · rw [List.pairwise_iff_getElem] ; intros i j hi hj hne
    intro k hx hy
    simp only [Array.getElem_toList] at hx hy
    simp at hi hj
    have h1 := hsh_nat i hi k hx
    have h2 := hsh_nat j hj k hy
    omega

end VectorUSize

/-! ## Sharded collections -/

/-- The operations, and their specifications, that every sharded collection needs from the type `S`
of its shards. `SetShard` and `MapShard` extend it with what the sharded sets and maps need. -/
class KeyShard (α : Type u) (S : Type v) [Membership α S] where
  empty : S
  contains : S → α → Bool
  size : S → Nat
  /-- The keys. -/
  toList : S → List α
  not_mem_empty {k : α} : k ∉ empty
  contains_iff_mem {s : S} {k : α} : contains s k = true ↔ k ∈ s
  mem_toList {s : S} {k : α} : k ∈ toList s ↔ k ∈ s
  nodup_toList {s : S} : (toList s).Nodup
  length_toList {s : S} : (toList s).length = size s

/-- Keys of type `α` split into `numShards` shards of type `S` by their hash: each key is in the
shard at index `shardIdxOfUSize numShards k`. The sharded sets and maps are this structure, for
different types of shards. Since `numShards` is a parameter, it is just the array of shards at run
time. -/
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

theorem mem_iff_exists_shard {st : ShardedUSize α S numShards} {k : α} :
    k ∈ st ↔ ∃ shard ∈ st.shards.val.toList, k ∈ shard := by
  simp only [mem_def, getShard, VectorUSize.ugetViaHash, VectorUSize.mem_toList_iff]
  constructor <;> grind [st.h_in_correct_shard]

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

/-- The keys of all shards. -/
@[inline]
def toList (st : ShardedUSize α S numShards) : List α :=
  st.shards.val.toList.flatMap KeyShard.toList

theorem length_toList {st : ShardedUSize α S numShards} :
    st.size = st.toList.length := by
  simp [size, toList, ← Array.foldl_toList, KeyShard.length_toList, List.sum_eq_foldl, List.foldl_map]

theorem nodup_toList {st : ShardedUSize α S numShards} :
    st.toList.Nodup := VectorUSize.nodup_flatMap_of_shards KeyShard.toList
    (fun i hi k hk => st.h_in_correct_shard i hi k (KeyShard.mem_toList.mp hk))
    (fun _ _ => KeyShard.nodup_toList)

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

/-- The collection without keys. -/
def empty [KeyShard α S] : ShardedUSize α S numShards :=
  replicate (KeyShard.empty (α := α)) fun _ => KeyShard.not_mem_empty

theorem not_mem_empty [KeyShard α S] {k : α} : k ∉ (empty : ShardedUSize α S numShards) :=
  not_mem_replicate

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

/-- The shards `f x` of the elements `x` of `v`, each holding keys of its own index only. -/
@[inline]
def ofMap {β : Type w} (v : VectorUSize β numShards) (f : β → S)
    (h : ∀ (i : USize) (hi : i < numShards), ∀ k ∈ f (v.uget i hi), shardIdxOfUSize numShards k = i) :
    ShardedUSize α S numShards :=
  ⟨v.map f, fun i hi k hk => h i hi k (by rwa [VectorUSize.uget_map] at hk)⟩

theorem ext_shards {st other : ShardedUSize α S numShards} (h : st.shards = other.shards) : st = other := by
  cases st ; cases other ; simp only at h ; subst h ; rfl

theorem uget_zipShardsPar {other : ShardedUSize α T numShards} {f : S → T → S}
    {hf : ∀ s t k, k ∈ f s t → k ∈ s ∨ k ∈ t} {st : ShardedUSize α S numShards} {i : USize} {h : i < numShards} :
    (st.zipShardsPar other f hf).shards.uget i h = f (st.shards.uget i h) (other.shards.uget i h) := by
  simp [zipShardsPar, VectorUSize.uget, Array.uget, Task.spawn]

end ShardedUSize

/-! ## Sharded sets -/

/-- The operations, and their specifications, that a `ShardedSetUSize` needs from the set type `S`
of its shards, beyond those of `KeyShard`. `insertMany` adds a whole `HashSet`: the parallel search
collects the new states of a BFS level per shard and then adds them to each shard in one go. -/
class SetShard (α : Type u) (S : Type v) [BEq α] [Hashable α] [Membership α S] extends KeyShard α S where
  /-- A shard holding the elements of a list. -/
  ofList : List α → S
  insert : S → α → S
  insertMany : S → HashSet α → S
  mem_ofList {l : List α} {k : α} : k ∈ ofList l ↔ k ∈ l
  mem_insert {s : S} {x k : α} : k ∈ insert s x ↔ (x == k) = true ∨ k ∈ s
  mem_insertMany {s : S} {hs : HashSet α} {k : α} : k ∈ insertMany s hs ↔ k ∈ s ∨ k ∈ hs

/-- `Std.TreeSet` ordered by `compare`, as the set type of shards: the default for the parallel search's
seen set, and the one that takes the least memory (`HAMTKeysShard` and `HAMTShard` are faster). -/
abbrev TreeSetShard (α : Type u) [Ord α] := TreeSet α compare

instance [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulBEq α] [Hashable α] :
    SetShard α (TreeSetShard α) where
  empty := ∅
  ofList l := TreeSet.ofListFast l compare
  contains := TreeSet.contains
  insert s x := s.insert x
  insertMany s hs := s.insertManyFast hs
  size := TreeSet.size
  toList := TreeSet.toList
  not_mem_empty := TreeSet.not_mem_emptyc
  contains_iff_mem := TreeSet.mem_iff_contains.symm
  mem_toList := TreeSet.mem_toList
  nodup_toList := TreeSet.distinct_toList.imp fun h heq => by subst heq ; exact h ReflCmp.compare_self
  length_toList := TreeSet.length_toList
  mem_ofList := by simp [TreeSet.mem_ofListFast]
  mem_insert := by intros ; rw [TreeSet.mem_insert, LawfulBEqCmp.compare_eq_iff_beq]
  mem_insertMany := by intros ; simp only [TreeSet.mem_insertManyFast_hashset, HashSet.mem_iff_contains]

/-- `HashSet` as the set type of shards, for `ShardedHashSetUSize`. -/
instance [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] : SetShard α (HashSet α) where
  empty := HashSet.emptyWithCapacity 8
  ofList := HashSet.ofList
  contains := HashSet.contains
  insert s x := s.insert x
  insertMany s hs := s.insertMany hs.toList
  size := HashSet.size
  toList := HashSet.toList
  not_mem_empty := HashSet.not_mem_emptyWithCapacity
  contains_iff_mem := HashSet.mem_iff_contains.symm
  mem_toList := HashSet.mem_toList
  nodup_toList := HashMap.nodup_keys
  length_toList := HashSet.length_toList
  mem_ofList := by simp [HashSet.mem_ofList]
  mem_insert := HashSet.mem_insert
  mem_insertMany := by simp [HashSet.mem_insertMany_list, HashSet.mem_toList]

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

/-- The keys of `l`, bucketed by shard. -/
@[specialize]
def distributeByHash (l : List α) : ShardedUSize α (List α) numShards where
  shards := VectorUSize.distributeInto id numShards.property (.replicateUSize numShards []) l
  h_in_correct_shard := by
    intro i hi k hk
    simp only [VectorUSize.mem_uget_distributeInto, VectorUSize.uget_replicateUSize] at hk
    simp at hk ; exact hk.2

theorem mem_distributeByHash {l : List α} {k : α} :
    k ∈ distributeByHash (numShards := numShards) l ↔ k ∈ l := by
  simp [ShardedUSize.mem_def, ShardedUSize.getShard, distributeByHash, VectorUSize.ugetViaHash,
    VectorUSize.mem_uget_distributeInto, VectorUSize.uget_replicateUSize]

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

/-! ### Single insertion -/

/-- Unconditionally insert an element into the sharded set. -/
@[specialize]
def insert [LawfulBEq α] (st : ShardedSetUSize α S numShards) (x : α) :
    ShardedSetUSize α S numShards :=
  st.modifyShard x (SetShard.insert · x) fun _ k hk => by
    simp [SetShard.mem_insert] at hk
    rcases hk with hk | hk
    · grind
    · exact .inl hk

@[simp]
theorem mem_insert [LawfulBEq α] {st : ShardedSetUSize α S numShards} {x y : α} :
    x ∈ st.insert y ↔ (y == x) = true ∨ x ∈ st := by
  unfold insert ShardedUSize.modifyShard
  rw [ShardedUSize.mem_def, ShardedUSize.mem_def]
  unfold ShardedUSize.getShard
  simp [VectorUSize.umodifyViaHash, VectorUSize.umodify, VectorUSize.ugetViaHash, VectorUSize.uget, VectorUSize.uset,
    Array.uget, Array.uset, Array.getElem_set]
  grind [SetShard.mem_insert]

end ShardedSetUSize
