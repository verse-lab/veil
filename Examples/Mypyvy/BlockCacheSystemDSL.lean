--  https://github.com/wilcoxjay/mypyvy/blob/master/examples/block_cache_system.pyv
--  A simplified model of one refinement proof from the following paper
--  (manually translated from Dafny):
--
--  Travis Hance, Andrea Lattuada, Chris Hawblitzel, Jon Howell, Rob
--  Johnson, Bryan Parno. Storage Systems are Distributed Systems (So
--  Verify Them That Way!). OSDI 2020. https://www.usenix.org/conference/osdi20/presentation/hance
--
--  This model is a simplified version of one of the high-level
--  refienment proofs from the above paper, that a block cache and a
--  disk refine their specification.
import Veil.DSL
import Veil.DSL.Util

namespace BlockCacheSystem
open Classical

type node
type ref
type location
type req_id

-- ### spec

relation spec_ephemeral : ref -> node -> Prop
relation spec_frozen : ref -> node -> Prop
relation spec_persistent : ref -> node -> Prop
individual spec_sync_in_progress : Prop


-- ### disk

relation disk_indirection_tables : location -> ref -> location -> Prop
relation disk_nodes : location -> node -> Prop
relation disk_req_write_indirection_tables : req_id -> location -> Prop
relation disk_req_write_nodes : req_id -> location -> Prop
relation disk_req_read_nodes : req_id -> location -> Prop


-- ## block_cache

relation cache : ref -> node -> Prop
relation ephemeral_clean : ref -> location -> Prop
relation ephemeral_dirty : ref -> Prop
relation frozen_clean : ref -> location -> Prop
relation frozen_dirty : ref -> Prop
relation persistent : ref -> location -> Prop
relation sync_in_progress : Prop
individual persistent_indirection_table_loc : location
individual frozen_indirection_table_loc : location
relation frozen_indirection_table_loc_some : Prop
relation outstanding_indirection_table_write : req_id -> Prop
relation outstanding_block_writes : req_id -> ref -> location -> Prop
relation outstanding_block_reads : req_id -> ref -> Prop


#gen_state

after_init {
  spec_ephemeral X Y := False;
  spec_frozen X Y := False;
  spec_persistent X Y := False;
  spec_sync_in_progress := False;

  disk_indirection_tables X Y Z := False;
  disk_nodes X Y := False;
  disk_req_write_indirection_tables X Y := False;
  disk_req_write_nodes X Y := False;
  disk_req_read_nodes X Y := False;

  cache  _ := False;
  ephemeral_clean  _ := False;
  ephemeral_dirt _ := False;
  persistent  _ := False;
  frozen_dirt _ := False;
  frozen_clean  _ := False;
  frozen_indirection_table_loc_some := False;
  outstanding_indirection_table_write _ := False;
  outstanding_block_writes _ _ _ := False;
  outstanding_block_reads _ _ := False;
  sync_in_progress := False
}

invariant (disk_indirection_tables L R L1) ∧ (disk_indirection_tables L R L2) → L1 = L2
invariant (disk_nodes L N1) ∧ (disk_nodes L N2) → N1 = N2
invariant (disk_req_write_nodes I L1) ∧ (disk_req_write_nodes I L2) → L1 = L2
invariant (disk_req_read_nodes I L1) ∧ (disk_req_read_nodes I L2) → L1 = L2
invariant (disk_req_write_indirection_tables I L1) ∧ (disk_req_write_indirection_tables I L2) → L1 = L2

safety [p] ∀ R, ((∀ N, ¬(cache R N)) ∧ (∀ L, ¬(ephemeral_clean R L))) → (∀ N, ¬(spec_ephemeral R N))

action freeze = {
  require (∀ x, ¬ (outstanding_indirection_table_write x));
  frozen_clean R L := ephemeral_clean R L;
  frozen_dirty R := ephemeral_dirty R;
  sync_in_progress := True;
  frozen_indirection_table_loc_some := False;
  spec_frozen R N := spec_ephemeral R N;
  spec_sync_in_progress := True
}

action write_back_indirection_table_req (i : req_id) (l : location) = {
  require sync_in_progress;
  require (∀ r, ¬ (frozen_dirty r));
  require ¬ frozen_indirection_table_loc_some;
  require l ≠ persistent_indirection_table_loc;
  require (∀ i r l, ¬ (outstanding_block_writes i r l));
  require (∀ l, ¬ (disk_req_write_indirection_tables i l));
  disk_indirection_tables L1 R L2 := (L1 ≠ l ∧ disk_indirection_tables L1 R L2) ∨ (L1 = l ∧ frozen_clean R L2);
  disk_req_write_indirection_tables i L := disk_req_write_indirection_tables i L ∨ (i = i ∧ L = l);
  frozen_indirection_table_loc_some := True;
  frozen_indirection_table_loc := l;
  outstanding_indirection_table_write I := outstanding_indirection_table_write I ∨ (I = i)
}

action write_back_indirection_table_resp (i : req_id) = {
  require frozen_indirection_table_loc_some;
  require outstanding_indirection_table_write i;
  require disk_req_write_indirection_tables i frozen_indirection_table_loc;
  outstanding_indirection_table_write I := outstanding_indirection_table_write I ∧ (I ≠ i);
  disk_req_write_indirection_tables I L := disk_req_write_indirection_tables I L ∨ (I = i ∧ L = frozen_indirection_table_loc)
}

#check_invariants



-- transition cleanup()
--     modifies persistent, persistent_indirection_table_loc, sync_in_progress, frozen_indirection_table_loc_some, spec_persistent, spec_sync_in_progress
--     & sync_in_progress
--     & frozen_indirection_table_loc_some
--     & (forall I. !outstanding_indirection_table_write(I))
--     & (forall R, L. new(persistent(R,L)) <-> frozen_clean(R, L))
--     & new(persistent_indirection_table_loc) = frozen_indirection_table_loc
--     & !new(sync_in_progress)
--     & !new(frozen_indirection_table_loc_some)
--     & (forall R, N. new(spec_persistent(R, N)) <-> spec_frozen(R,N))
--     & !new(spec_sync_in_progress)

-- safety sync_in_progress & frozen_indirection_table_loc_some & (forall I. !outstanding_indirection_table_write(I)) -> spec_sync_in_progress

-- transition crash()
--     modifies cache, ephemeral_clean, persistent, ephemeral_dirty, sync_in_progress, frozen_indirection_table_loc_some, outstanding_indirection_table_write, outstanding_block_reads, outstanding_block_writes, disk_indirection_tables, disk_req_write_indirection_tables, disk_nodes, disk_req_write_nodes, disk_req_read_nodes, spec_ephemeral, spec_sync_in_progress
--     & (forall X, Y. !new(cache(X,Y)))
--     & (forall R, L. new(ephemeral_clean(R, L)) <-> disk_indirection_tables(persistent_indirection_table_loc, R, L))
--     & (forall R, L. new(persistent(R,L)) <-> disk_indirection_tables(persistent_indirection_table_loc, R ,L))
--     & (forall R. !new(ephemeral_dirty(R)))
--     & !new(sync_in_progress)
--     & !new(frozen_indirection_table_loc_some)
--     & (forall I. !new(outstanding_indirection_table_write(I)))
--     & (forall I, R. !new(outstanding_block_reads(I, R)))
--     & (forall I, R, L. !new(outstanding_block_writes(I, R, L)))
--     & (forall L, R, X, Y. new(disk_indirection_tables(L, R, X)) & new(disk_indirection_tables(L, R, Y)) -> X = Y)
--     & (forall L1. (forall I . !disk_req_write_indirection_tables(I,L1)) -> (forall R, L2. new(disk_indirection_tables(L1, R, L2)) <-> disk_indirection_tables(L1, R, L2)))
--     & (forall I, L. !new(disk_req_write_indirection_tables(I,L)))
--     & (forall L, N1, N2. new(disk_nodes(L, N1)) & new(disk_nodes(L, N2)) -> N1 = N2)
--     & (forall L. (forall I . !disk_req_write_nodes(I, L)) -> (forall N. new(disk_nodes(L, N)) <-> disk_nodes(L,N)))
--     & (forall I, L. !new(disk_req_write_nodes(I, L)))
--     & (forall I, L. !new(disk_req_read_nodes(I, L)))
--     & (forall R, N. new(spec_ephemeral(R, N)) <->  spec_persistent(R,N))
--     & !new(spec_sync_in_progress)

-- safety forall R, N. cache(R, N) -> spec_ephemeral(R, N)

-- transition write_node(r: ref, n: node)
--     modifies cache, ephemeral_clean, ephemeral_dirty, spec_ephemeral
--     & (sync_in_progress -> !frozen_dirty(r))
--     & (exists N. cache(r, N))
--     & (forall R, N. new(cache(R, N)) <-> (R != r & cache(R, N)) | (R = r & N = n))
--     & (forall R, L. new(ephemeral_clean(R, L)) <-> ephemeral_clean(R, L) & R != r)
--     & (forall R. new(ephemeral_dirty(R)) <-> ephemeral_dirty(R) | R = r)
--     & (forall R, N. new(spec_ephemeral(R, N)) <-> (R != r & spec_ephemeral(R, N)) | (R = r & N = n))

-- transition alloc(r: ref, n: node)
--     modifies cache, ephemeral_dirty, spec_ephemeral
--     & (forall N. !cache(r, N))
--     & (forall L. !ephemeral_clean(r, L))
--     & !ephemeral_dirty(r)
--     & (forall L. sync_in_progress -> (!frozen_clean(r, L) & !frozen_dirty(r)))
--     & (forall R, N. new(cache(R, N)) <-> cache(R, N) | (R = r & N = n))
--     & (forall R. new(ephemeral_dirty(R)) <-> ephemeral_dirty(R) | R = r)
--     & (forall R, N. new(spec_ephemeral(R, N)) <-> (R != r & spec_ephemeral(R, N)) | (R = r & N = n))

-- transition page_in_node_req(i:req_id, r:ref, l:location)
--     modifies outstanding_block_reads, disk_req_read_nodes
--     & ephemeral_clean(r, l)
--     & (forall N. !cache(r, N))
--     & (forall I. !outstanding_block_reads(I, r))
--     & (forall I, R. new(outstanding_block_reads(I, R)) <-> (I != i & outstanding_block_reads(I, R)) | (I = i & R = r))
--     & (forall L. !disk_req_read_nodes(i, L))
--     & (forall I, L. new(disk_req_read_nodes(I,L)) <-> (I != i & disk_req_read_nodes(I, L)) | (I = i & L = l))

-- invariant outstanding_block_reads(I,R) & disk_req_read_nodes(I,L) -> ephemeral_clean(R,L)
-- invariant outstanding_block_reads(I,R) -> exists L. disk_req_read_nodes(I,L)
-- invariant cache(R,N) -> !outstanding_block_reads(I,R)
-- invariant outstanding_block_reads(I1,R) & outstanding_block_reads(I2,R) -> I1 = I2

-- transition page_in_node_resp(i:req_id, r:ref, l:location, n:node)
--     modifies cache, outstanding_block_reads, disk_req_read_nodes
--     & outstanding_block_reads(i, r)
--     & disk_req_read_nodes(i, l)
--     & (forall R, N. new(cache(R, N)) <-> cache(R, N) | (R = r & N = n))
--     & (forall I, R. new(outstanding_block_reads(I, R)) <-> outstanding_block_reads(I, R) & I != i)
--     & disk_req_read_nodes(i, l)
--     & disk_nodes(l, n)
--     & (forall I, L. new(disk_req_read_nodes(I, L)) <-> (I != i & disk_req_read_nodes(I, L)))

-- transition write_back_node_req_00(i:req_id, r:ref, n:node, l: location)
--     modifies ephemeral_dirty, ephemeral_clean, frozen_dirty, frozen_clean, outstanding_block_writes, disk_nodes, disk_req_write_nodes
--     & (forall R. !persistent(R, l) & !ephemeral_clean(R, l) & !frozen_clean(R, l))
--     & (forall R. !outstanding_block_writes(i, R, L))
--     & cache(r,n)
--     & (forall L. !disk_req_write_nodes(i, L))
--     & (forall L, N. new(disk_nodes(L, N)) <-> (L != l & disk_nodes(L, N)) | (L = l & N = n))
--     & (forall I, L. new(disk_req_write_nodes(I, L)) <-> disk_req_write_nodes(I, L) | (I = i & L = l))
--     & ephemeral_dirty(r)
--     & (forall R. new(ephemeral_dirty(R)) <-> ephemeral_dirty(R) & R != r)
--     & (forall R, L. new(ephemeral_clean(R, L)) <-> (R != r & ephemeral_clean(R, L)) | (R = r & L = l))
--     & (sync_in_progress & frozen_dirty(r))
--     & (forall R. new(frozen_dirty(R)) <-> frozen_dirty(R) & R != r)
--     & (forall R, L. new(frozen_clean(R, L)) <-> (R != r & frozen_clean(R, L)) | (R = r & L = l))
--     & (forall I, R, L. new(outstanding_block_writes(I, R, L)) <-> outstanding_block_writes(I, R, L) | (I = i & R = r & L = l))

-- transition write_back_node_req_01(i:req_id, r:ref, n:node, l: location)
--     modifies ephemeral_dirty, ephemeral_clean, outstanding_block_writes, disk_nodes, disk_req_write_nodes
--     & (forall R. !persistent(R, l) & !ephemeral_clean(R, l) & !frozen_clean(R, l))
--     & (forall R. !outstanding_block_writes(i, R, L))
--     & cache(r,n)
--     & (forall L. !disk_req_write_nodes(i, L))
--     & (forall L, N. new(disk_nodes(L, N)) <-> (L != l & disk_nodes(L, N)) | (L = l & N = n))
--     & (forall I, L. new(disk_req_write_nodes(I, L)) <-> disk_req_write_nodes(I, L) | (I = i & L = l))
--     & ephemeral_dirty(r)
--     & (forall R. new(ephemeral_dirty(R)) <-> ephemeral_dirty(R) & R != r)
--     & (forall R, L. new(ephemeral_clean(R, L)) <-> (R != r & ephemeral_clean(R, L)) | (R = r & L = l))
--     & !(sync_in_progress & frozen_dirty(r))
--     & (forall I, R, L. new(outstanding_block_writes(I, R, L)) <-> outstanding_block_writes(I, R, L) | (I = i & R = r & L = l))

-- transition write_back_node_req_10(i:req_id, r:ref, n:node, l: location)
--     modifies frozen_dirty, frozen_clean, outstanding_block_writes, disk_nodes, disk_req_write_nodes
--     & (forall R. !persistent(R, l) & !ephemeral_clean(R, l) & !frozen_clean(R, l))
--     & (forall R. !outstanding_block_writes(i, R, L))
--     & cache(r,n)
--     & (forall L. !disk_req_write_nodes(i, L))
--     & (forall L, N. new(disk_nodes(L, N)) <-> (L != l & disk_nodes(L, N)) | (L = l & N = n))
--     & (forall I, L. new(disk_req_write_nodes(I, L)) <-> disk_req_write_nodes(I, L) | (I = i & L = l))
--     & !ephemeral_dirty(r)
--     & (sync_in_progress & frozen_dirty(r))
--     & (forall R. new(frozen_dirty(R)) <-> frozen_dirty(R) & R != r)
--     & (forall R, L. new(frozen_clean(R, L)) <-> (R != r & frozen_clean(R, L)) | (R = r & L = l))
--     & (forall I, R, L. new(outstanding_block_writes(I, R, L)) <-> outstanding_block_writes(I, R, L) | (I = i & R = r & L = l))

-- transition write_back_node_req_11(i:req_id, r:ref, n:node, l: location)
--     modifies outstanding_block_writes, disk_nodes, disk_req_write_nodes
--     & (forall R. !persistent(R, l) & !ephemeral_clean(R, l) & !frozen_clean(R, l))
--     & (forall R. !outstanding_block_writes(i, R, L))
--     & cache(r,n)
--     & (forall L. !disk_req_write_nodes(i, L))
--     & (forall L, N. new(disk_nodes(L, N)) <-> (L != l & disk_nodes(L, N)) | (L = l & N = n))
--     & (forall I, L. new(disk_req_write_nodes(I, L)) <-> disk_req_write_nodes(I, L) | (I = i & L = l))
--     & !ephemeral_dirty(r)
--     & !(sync_in_progress & frozen_dirty(r))
--     & (forall I, R, L. new(outstanding_block_writes(I, R, L)) <-> outstanding_block_writes(I, R, L) | (I = i & R = r & L = l))

-- transition write_back_node_resp(i:req_id, l:location)
--     modifies outstanding_block_writes, disk_req_write_nodes
--     & (exists R, L. outstanding_block_writes(i, R, L))
--     & disk_req_write_nodes(i,l)
--     & (forall I, L. new(disk_req_write_nodes(I, L)) <-> disk_req_write_nodes(I, L) & (I != i | L != l))
--     & (forall I, R, L. new(outstanding_block_writes(I, R, L)) <-> outstanding_block_writes(I, R, L) & I != i)

-- transition evict(r:ref)
--     modifies cache
--     & (exists N. cache(r, N))
--     & !ephemeral_dirty(r)
--     & (forall R, N. new(cache(R, N)) <-> cache(R, N) & R != r)

-- invariant (exists R. outstanding_block_reads(I,R)) <-> (exists L. disk_req_read_nodes(I,L))
-- invariant outstanding_block_reads(I,R) & disk_req_read_nodes(I,L) -> ephemeral_clean(R,L)

-- invariant persistent(R1,L) -> !outstanding_block_writes(I,R2,L)
-- invariant frozen_indirection_table_loc_some ->
--       (frozen_clean(R1,L) -> !outstanding_block_writes(I,R2,L))

-- invariant !disk_req_write_indirection_tables(I,persistent_indirection_table_loc)
-- invariant disk_req_write_indirection_tables(I, L) -> outstanding_indirection_table_write(I)
-- invariant disk_req_write_nodes(I,L) -> (exists R . outstanding_block_writes(I,R,L))

-- invariant frozen_indirection_table_loc_some -> (frozen_clean(R, L) <-> disk_indirection_tables(frozen_indirection_table_loc, R, L))

-- invariant outstanding_block_writes(I,R1,L1) & outstanding_block_writes(I,R2,L2)
--      -> R1 = R2 & L1 = L2
-- invariant outstanding_block_reads(I,R1) & outstanding_block_reads(I,R2)
--      -> R1 = R2

-- invariant frozen_indirection_table_loc_some -> !frozen_dirty(R)
-- invariant frozen_indirection_table_loc_some -> sync_in_progress

-- # maybe need that
-- invariant outstanding_indirection_table_write(I1) & outstanding_indirection_table_write(I2) -> I1 = I2
-- invariant sync_in_progress -> (frozen_dirty(R) -> ephemeral_dirty(R))
-- invariant outstanding_indirection_table_write(I) -> frozen_indirection_table_loc_some
-- invariant frozen_indirection_table_loc_some -> (frozen_indirection_table_loc != persistent_indirection_table_loc)
-- # functional relations
-- invariant cache(R, X) & cache(R, Y) -> X = Y
-- invariant ephemeral_clean(R, X) & ephemeral_clean(R, Y) -> X = Y
-- invariant persistent(R, X) & persistent(R, Y) -> X = Y
-- invariant frozen_clean(R, X) & frozen_clean(R, Y) -> X = Y

-- # clean cache invariant (ignoring async disk writes)
-- invariant !(ephemeral_dirty(R) & ephemeral_clean(R, L))
-- invariant cache(R, N) & ephemeral_clean(R, L) -> disk_nodes(L, N)
-- invariant cache(R, N) & !ephemeral_dirty(R) -> exists L. ephemeral_clean(R, L)

-- # under our current simplifications:
-- invariant persistent(R,L) <-> disk_indirection_tables(persistent_indirection_table_loc,R,L)

-- # representation invariants
-- invariant cache(R, N) -> spec_ephemeral(R, N)
-- invariant persistent(R, L) & disk_nodes(L, N) -> spec_persistent(R, N)
-- invariant ephemeral_clean(R, L) & disk_nodes(L, N) -> spec_ephemeral(R, N)
-- # stronger versions not actually needed:
-- invariant spec_persistent(R,N) <-> exists L. persistent(R, L) & disk_nodes(L, N)
-- invariant spec_ephemeral(R, N) <-> cache(R, N) | (exists L. ephemeral_clean(R, L) & disk_nodes(L, N))
-- #invariant sync_in_progress ->
-- #      (spec_frozen(R,N) <->  ((frozen_dirty(R) & cache(R, N))
-- #                               | (exists L. frozen_clean(R, L) & disk_nodes(L, N))))
-- invariant sync_in_progress & spec_frozen(R,N) & !frozen_dirty(R) -> exists L. frozen_clean(R, L) & disk_nodes(L, N)
-- invariant sync_in_progress & spec_frozen(R,N) & !cache(R, N) -> exists L. frozen_clean(R, L) & disk_nodes(L, N)
-- invariant sync_in_progress & frozen_dirty(R) & cache(R, N) -> spec_frozen(R,N)
-- invariant sync_in_progress & frozen_clean(R, L) & disk_nodes(L, N) -> spec_frozen(R,N)
-- invariant sync_in_progress <-> spec_sync_in_progress
-- invariant sync_in_progress -> !(frozen_dirty(R) & frozen_clean(R, L))
