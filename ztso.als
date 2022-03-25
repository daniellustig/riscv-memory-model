open riscv

////////////////////////////////////////////////////////////
// zTSO
fact { AMO in RCsc }
fact { Load in MemoryEvent.acquireRCpc }
fact { Store in MemoryEvent.releaseRCpc }

////////////////////////////////////////////////////////////////////////////////
// =Examples=

// for convenience
fun fr : Event->Event { ~rf.^gmo & address.~address :> Store }

run w_lr_sc_ordered {
  some disj a, b, c : MemoryEvent, disj x, y: Address |
    a->b + b->c in ^po and

    // Hart 1
    a in StoreNormal & y.~address and
    b in LoadReserve & x.~address and
    c in StoreConditional & x.~address and

    // WW Reordering is not allowed
    c->a in gmo and

    RISCV_mm
} for 5

run w_lr_sc_unordered {
  some disj a, b, c : MemoryEvent, disj x, y: Address |
    a->b + b->c in ^po and

    // Hart 1
    a in StoreNormal & y.~address and
    b in LoadReserve & x.~address and
    c in StoreConditional & x.~address and

    // WR Reordering is allowed
    b->a in gmo and

    RISCV_mm
} for 5

run r_lr_sc_ordered {
  some disj a, b, c : MemoryEvent, disj x, y: Address |
    a->b + b->c in ^po and

    // Hart 1
    a in LoadNormal & y.~address and
    b in LoadReserve & x.~address and
    c in StoreConditional & x.~address and

    // RR Reordering is not allowed
    b->a in gmo and

    RISCV_mm
} for 5

run lr_sc_r_ordered {
  some disj a, b, c : MemoryEvent, disj x, y: Address |
    a->b + b->c in ^po and

    // Hart 1
    a in LoadReserve & x.~address and
    b in StoreConditional & x.~address and
    c in LoadNormal & y.~address and

    // RR Reordering is not allowed
    c->a in gmo and

    RISCV_mm
} for 5

run lr_sc_r_unordered {
  some disj a, b, c : MemoryEvent, disj x, y: Address |
    a->b + b->c in ^po and

    // Hart 1
    a in LoadReserve & x.~address and
    b in StoreConditional & x.~address and
    c in LoadNormal & y.~address and

    // WR Reordering is allowed
    c->b in gmo and

    RISCV_mm
} for 5

run lr_sc_w_ordered {
  some disj a, b, c : MemoryEvent, disj x, y: Address |
    a->b + b->c in ^po and

    // Hart 1
    a in LoadReserve & x.~address and
    b in StoreConditional & x.~address and
    c in StoreNormal & y.~address and

    // WW Reordering is not allowed
    c->b in gmo and

    RISCV_mm
} for 5

run r_r_ordered {
  some disj a, b : MemoryEvent, disj x, y: Address |
    a->b in ^po and

    // Hart 1
    a in LoadNormal & x.~address and
    b in LoadNormal & y.~address and

    // RR Reordering is not allowed
    b->a in gmo and

    RISCV_mm
} for 5

run r_w_ordered {
  some disj a, b : MemoryEvent, disj x, y: Address |
    a->b in ^po and

    // Hart 1
    a in LoadNormal & x.~address and
    b in StoreNormal & y.~address and

    // RW Reordering is not allowed
    b->a in gmo and

    RISCV_mm
} for 5

run w_r_unordered {
  some disj a, b : MemoryEvent, disj x, y: Address |
    a->b in ^po and

    // Hart 1
    a in StoreNormal & x.~address and
    b in LoadNormal & y.~address and

    // WR Reordering is allowed
    b->a in gmo and

    RISCV_mm
} for 5

run w_w_ordered {
  some disj a, b : MemoryEvent, disj x, y: Address |
    a->b in ^po and

    // Hart 1
    a in StoreNormal & x.~address and
    b in StoreNormal & y.~address and

    // WW Reordering is not allowed
    b->a in gmo and

    RISCV_mm
} for 5

run amo_ordered {
  some disj a, b : MemoryEvent, disj x, y: Address |
    a->b in ^po and

    // Hart 1
    a in AMO & x.~address and
    b in AMO & y.~address and

    // AMO ops are now RCsc, so reordering is not possible
    b->a in gmo and

    RISCV_mm
} for 5
