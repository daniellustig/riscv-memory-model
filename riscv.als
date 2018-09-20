////////////////////////////////////////////////////////////////////////////////
// =RVWMO axioms=

// See Chapter 6 in the RISC-V ISA Specification

// Preserved Program Order
fun ppo : Event->Event {
  // same-address ordering
  po_loc :> Store
  + (AMO + StoreConditional) <: rfi
  + rdw

  // explicit synchronization
  + ppo_fence
  + Acquire <: ^po :> MemoryEvent
  + MemoryEvent <: ^po :> Release
  + RCsc <: ^po :> RCsc
  + pair

  // syntactic dependencies
  + addrdep
  + datadep
  + ctrldep :> Store

  // pipeline dependencies
  + (addrdep+datadep).rfi
  + addrdep.^po :> Store
}

// the global memory order respects preserved program order
fact { ppo in ^gmo }

// Load Value Axiom
fun candidates[r: MemoryEvent] : set MemoryEvent {
  (r.~^gmo & Store & same_addr[r]) // writes preceding r in gmo
  + (r.^~po & Store & same_addr[r]) // writes preceding r in po
}

fun latest_among[s: set Event] : Event { s - s.~^gmo }

pred LoadValue {
  all w: Store | all r: Load |
    w->r in rf <=> w = latest_among[candidates[r]]
}

// Atomicity Axiom
pred Atomicity {
  all r: Store.~pair |            // starting from the lr,
    no x: Store & same_addr[r] |  // there is no store x to the same addr
      x not in same_hart[r]       // such that x is from a different hart,
      and x in r.~rf.^gmo         // x follows (the store r reads from) in gmo,
      and r.pair in x.^gmo        // and r follows x in gmo
}

// Progress Axiom implicit: Alloy only considers finite models

pred RISCV_mm { LoadValue and Atomicity /* and Progress */ }

////////////////////////////////////////////////////////////////////////////////
// Basic model of memory

sig Hart {  // hardware thread
  start : one Event
}
sig Address {}
abstract sig Event {
  po: lone Event // program order
}

abstract sig MemoryEvent extends Event {
  address: one Address,
  acquireRCpc: lone MemoryEvent,
  acquireRCsc: lone MemoryEvent,
  releaseRCpc: lone MemoryEvent,
  releaseRCsc: lone MemoryEvent,
  addrdep: set MemoryEvent,
  ctrldep: set Event,
  datadep: set MemoryEvent,
  gmo: set MemoryEvent,  // global memory order
  rf: set MemoryEvent
}
sig LoadNormal extends MemoryEvent {} // l{b|h|w|d}
sig LoadReserve extends MemoryEvent { // lr
  pair: lone StoreConditional
}
sig StoreNormal extends MemoryEvent {}       // s{b|h|w|d}
// all StoreConditionals in the model are assumed to be successful
sig StoreConditional extends MemoryEvent {}  // sc
sig AMO extends MemoryEvent {}               // amo
sig NOP extends Event {}

fun Load : Event { LoadNormal + LoadReserve + AMO }
fun Store : Event { StoreNormal + StoreConditional + AMO }

sig Fence extends Event {
  pr: lone Fence, // opcode bit
  pw: lone Fence, // opcode bit
  sr: lone Fence, // opcode bit
  sw: lone Fence  // opcode bit
}
sig FenceTSO extends Fence {}

/* Alloy encoding detail: opcode bits are either set (encoded, e.g.,
 * as f.pr in iden) or unset (f.pr not in iden).  The bits cannot be used for
 * anything else */
fact { pr + pw + sr + sw in iden }
// likewise for ordering annotations
fact { acquireRCpc + acquireRCsc + releaseRCpc + releaseRCsc in iden }
// don't try to encode FenceTSO via pr/pw/sr/sw; just use it as-is
fact { no FenceTSO.(pr + pw + sr + sw) }

////////////////////////////////////////////////////////////////////////////////
// =Basic model rules=

// Ordering annotation groups
fun Acquire : MemoryEvent { MemoryEvent.acquireRCpc + MemoryEvent.acquireRCsc }
fun Release : MemoryEvent { MemoryEvent.releaseRCpc + MemoryEvent.releaseRCsc }
fun RCpc : MemoryEvent { MemoryEvent.acquireRCpc + MemoryEvent.releaseRCpc }
fun RCsc : MemoryEvent { MemoryEvent.acquireRCsc + MemoryEvent.releaseRCsc }

// There is no such thing as store-acquire or load-release, unless it's both
fact { Load & Release in Acquire }
fact { Store & Acquire in Release }

// FENCE PPO
fun FencePRSR : Fence { Fence.(pr & sr) }
fun FencePRSW : Fence { Fence.(pr & sw) }
fun FencePWSR : Fence { Fence.(pw & sr) }
fun FencePWSW : Fence { Fence.(pw & sw) }

fun ppo_fence : MemoryEvent->MemoryEvent {
    (Load  <: ^po :> FencePRSR).(^po :> Load)
  + (Load  <: ^po :> FencePRSW).(^po :> Store)
  + (Store <: ^po :> FencePWSR).(^po :> Load)
  + (Store <: ^po :> FencePWSW).(^po :> Store)
  + (Load  <: ^po :> FenceTSO) .(^po :> MemoryEvent)
  + (Store <: ^po :> FenceTSO) .(^po :> Store)
}

// auxiliary definitions
fun po_loc : Event->Event { ^po & address.~address }
fun same_hart[e: Event] : set Event { e + e.^~po + e.^po }
fun same_addr[e: Event] : set Event { e.address.~address }

// initial stores
fun NonInit : set Event { Hart.start.*po }
fun Init : set Event { Event - NonInit }
fact { Init in StoreNormal }
fact { Init->(MemoryEvent & NonInit) in ^gmo }
fact { all e: NonInit | one e.*~po.~start }  // each event is in exactly one hart
fact { all a: Address | one Init & a.~address } // one init store per address
fact { no Init <: po and no po :> Init }

// po
fact { acyclic[po] }

// gmo
fact { total[^gmo, MemoryEvent] } // gmo is a total order over all MemoryEvents

//rf
fact { rf.~rf in iden } // each read returns the value of only one write
fact { rf in Store <: address.~address :> Load }
fun rfi : MemoryEvent->MemoryEvent { rf & (*po + *~po) }

//dep
fact { no StoreNormal <: (addrdep + ctrldep + datadep) }
fact { addrdep + ctrldep + datadep + pair in ^po }
fact { datadep in datadep :> Store }
fact { ctrldep.*po in ctrldep }
fact { no pair & (^po :> (LoadReserve + StoreConditional)).^po }
fact { StoreConditional in LoadReserve.pair } // assume all SCs succeed

// rdw
fun rdw : Event->Event {
  (Load <: po_loc :> Load)  // start with all same_address load-load pairs,
  - (~rf.rf)                // subtract pairs that read from the same store,
  - (po_loc.rfi)            // and subtract out "fri-rfi" patterns
}

// filter out redundant instances and/or visualizations
fact { no gmo & gmo.gmo } // keep the visualization uncluttered
fact { all a: Address | some a.~address }

////////////////////////////////////////////////////////////////////////////////
// =Optional: opcode encoding restrictions=

// the list of blessed fences
fact { Fence in
  Fence.pr.sr
  + Fence.pw.sw
  + Fence.pr.pw.sw
  + Fence.pr.sr.sw
  + FenceTSO
  + Fence.pr.pw.sr.sw
}

pred restrict_to_current_encodings {
  no (LoadNormal + StoreNormal) & (Acquire + Release)
}

////////////////////////////////////////////////////////////////////////////////
// =Alloy shortcuts=
pred acyclic[rel: Event->Event] { no iden & ^rel }
pred total[rel: Event->Event, bag: Event] {
  all disj e, e': bag | e->e' in rel + ~rel
  acyclic[rel]
}

////////////////////////////////////////////////////////////////////////////////
// =Examples=

// for convenience
fun fr : Event->Event { ~rf.^gmo & address.~address :> Store }

run Sanity { RISCV_mm } for 3

run MP {
  some disj a, b, c, d : MemoryEvent, disj x, y: Address |
    a in Store & x.~address and
    b in Store & y.~address and
    c in Load & y.~address and
    d in Load & x.~address and
    a->b + c->d in ppo and
    b->c in rf and
    d->a in fr and
    RISCV_mm
} for 8

run MP_fences {
  some disj a, b, c, d, e, f : Event, disj x, y: Address |
    a in Store & x.~address and
    b in Fence.pr.pw.sw and
    c in Store & y.~address and
    d in Load & y.~address and
    e in Fence.pr.sr.sw and
    f in Load & x.~address and
    po = a->b + b->c + d->e + e->f and
    c->d in rf and
    f->a in fr and
    RISCV_mm
} for 8

run MP_rl_addr {
  some disj a, b, c, d : MemoryEvent, disj x, y: Address |
    a in Store & x.~address and
    b in Store.releaseRCsc & y.~address and
    c in Load & y.~address and
    d in Load & x.~address and
    po = a->b + c->d and
    b->c in rf and
    d->a in fr and
    c->d in addrdep and
    RISCV_mm
} for 6

run MP_rl_fri_rfi_addr_legal {
  some disj a, b, c, d, e, f, g : Event, disj x, y: Address |
    a in Store & x.~address and
    b in Fence.pw.sw and
    c in Store & y.~address and
    d in Load & y.~address and
    e in Store & y.~address and
    f in Load & y.~address and
    g in Load & x.~address and
    po = a->b + b->c + d->e + e->f + f->g and
    c->d + e->f in rf and
    g->a in fr and
    f->g in addrdep and
    RISCV_mm
} for 9

run MP_rsw_legal {
  some disj a, b, c, d, e, f, g : Event, disj x, y, z: Address |
    a in Store & x.~address and
    b in Fence.pw.sw and
    c in Store & y.~address and
    d in Load & y.~address and
    e in Load & z.~address and
    f in Load & z.~address and
    g in Load & x.~address and
    po = a->b + b->c + d->e + e->f + f->g and
    c->d in rf and
    g->a in fr and
    d->e + f->g in addrdep and
    RISCV_mm
} for 10

run SB {
  some disj a, b, c, d : MemoryEvent, disj x, y: Address |
    a in Store & x.~address and
    b in Load & y.~address and
    c in Store & y.~address and
    d in Load & x.~address and
    a->b + c->d in ppo and
    d->a + b->c in fr and
    RISCV_mm
} for 6

run atoms {
  some disj a, b, c, d: MemoryEvent, x: Address |
    a in LoadReserve & x.~address and
    b in StoreConditional & x.~address and
    c in LoadReserve & x.~address and
    d in StoreConditional & x.~address and
    po = a->b + c->d and
    b->c not in rf and
    d->a not in rf and
    RISCV_mm
} for 5


/* LKMM scenario 1: if the Linux Kernel Memory Model needs
 * L -> rel/unlock -> acq/lock -> L ordering, then the "intuitive" mappings
 * aren't quite sufficient */
run lkmm_rel_acq_insufficient {
  some disj a, b, c, d, e, f: Event, z: Address |
    a->b + b->c + c->d + d->e + e->f in ^po
    and c->d in rf
    and a in MemoryEvent
    and ((a in Store and f in Store)
      or (a in Load  and f in Store)
      or (a in Load  and f in Load))
    and ((b in Fence.pr.pw.sw and c in StoreNormal                  & z.~address)
      or (b in Fence.pr.pw.sw and c in StoreConditional             & z.~address)
      or (                        c in StoreConditional.releaseRCsc & z.~address)
      or (                        c in AMO.releaseRCsc              & z.~address))
    and ((d in LoadNormal              & z.~address and e in Fence.pr.sr.sw)
      or (d in LoadNormal              & z.~address and e in Fence.pr.sr     and d->d.^po in ctrldep)
      or (d in LoadReserve             & z.~address and e in Fence.pr.sr.sw)
      or (d in LoadReserve             & z.~address and e in Fence.pr.sr     and d->d.^po in ctrldep)
      or (d in LoadReserve.acquireRCsc & z.~address)
      or (d in AMO.acquireRCsc         & z.~address))
    and RISCV_mm  // <---
    and f in MemoryEvent
    and a->f not in ^ppo
} for 8

/* ...but if we strengthen to fence.tso and fence w,w, we're OK */
run lkmm_rel_acq_fence_tso {
  some disj a, b, c, d, e, f: Event, z: Address |
    a->b + b->c + c->d + d->e + e->f in ^po
    and c->d in rf
    and a in MemoryEvent
    and ((a in Store and f in Store)
      or (a in Load  and f in Store)
      or (a in Load  and f in Load))
    and ((b in FenceTSO       and c in StoreNormal                  & z.~address)
      or (b in FenceTSO       and c in StoreConditional             & z.~address)
      or (                        c in StoreConditional.releaseRCsc & z.~address)
      or (                        c in AMO.releaseRCsc              & z.~address))
    and ((d in LoadNormal              & z.~address and e in Fence.pr.sr.sw)
      or (d in LoadNormal              & z.~address and e in Fence.pr.sr     and d->d.^po in ctrldep)
      or (d in LoadReserve             & z.~address and e in Fence.pr.sr.sw)
      or (d in LoadReserve             & z.~address and e in Fence.pr.sr     and d->d.^po in ctrldep)
      or (d in LoadReserve.acquireRCsc & z.~address)
      or (d in AMO.acquireRCsc         & z.~address))
    and RISCV_mm  // <---
    and f in MemoryEvent
    and a->f not in ^ppo
} for 10

/* Alternatively, if we don't use LR.aq, we're also OK */
run lkmm_rel_acq_no_lr_aq {
  some disj a, b, c, d, e, f: Event, z: Address |
    a->b + b->c + c->d + d->e + e->f in ^po
    and c->d in rf
    and a in MemoryEvent
    and ((a in Store and f in Store)
      or (a in Load  and f in Store)
      or (a in Load  and f in Load))
    and ((b in Fence.pr.pw.sw and c in StoreNormal                  & z.~address)
      or (b in Fence.pr.pw.sw and c in StoreConditional             & z.~address)
      or (                        c in StoreConditional.releaseRCsc & z.~address)
      or (                        c in AMO.releaseRCsc              & z.~address))
    and ((d in LoadNormal              & z.~address and e in Fence.pr.sr.sw)
      or (d in LoadNormal              & z.~address and e in Fence.pr.sr     and d->d.^po in ctrldep)
      or (d in LoadReserve             & z.~address and e in Fence.pr.sr.sw)
      or (d in LoadReserve             & z.~address and e in Fence.pr.sr     and d->d.^po in ctrldep)
   /* or (d in LoadReserve.acquireRCsc & z.~address) */
      or (d in AMO.acquireRCsc         & z.~address))
    and RISCV_mm  // <---
    and f in MemoryEvent
    and a->f not in ^ppo
} for 10


/* LKMM scenario 2: eliding the leading fence in fully-ordered atomics mapped using LR/SC
 * also applies to TSO atomics mapped using LR/SC
 * see: https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/commit/?id=8e86f0b409a44193f1587e87b69c5dcf8f65be67
 * [A]
 * // <-- elide this fence rw,rw
 * lr.aq
 * sc.rl
 * fence rw,rw
 * [G]
 */
run lkmm_elide_leading_fence {
  some disj a, b, c, d, g : Event, disj x, y, z : Address |
    a->b + b->c + c->d + d->g in ^po
    and a in x.~address
    and b in LoadReserve.acquireRCsc & z.~address
    and c in StoreConditional.releaseRCsc & z.~address
    and b.pair = c
    and d in Fence.pr.pw.sr.sw
    and g in y.~address
    and RISCV_mm
    and some iden & ppo.rf.(a <: ^po :> b).fr
} for 11

run lkmm_elide_leading_fence_aqrl {
  some disj a, b, c, g : Event, disj x, y, z : Address |
    a->b + b->c + c->g in ^po
    and a in x.~address
    and b in LoadReserve.acquireRCsc & z.~address
    and c in StoreConditional.acquireRCsc.releaseRCsc & z.~address
    and b.pair = c
    and g in y.~address
    and RISCV_mm
    and some iden & ppo.rf.(a <: ^po :> b).fr
} for 11

/* ...but eliding the trailing fence fails, even with a control dependency off of the SC! */
run lkmm_elide_trailing_fence {
  some disj a, b, c, d, g : Event, disj x, y, z : Address |
    a->b + b->c + c->d + d->g in ^po
    and a in x.~address
    and b in Fence.pr.pw.sr.sw
    and c in LoadReserve.acquireRCsc & z.~address
    and d in StoreConditional.releaseRCsc & z.~address
    and c.pair = d
    and g in y.~address
    and d->g in ctrldep
    and RISCV_mm
    and some iden & ppo.(gmo & address.~address).(d <: ^po :> g).(gmo & address.~address)
} for 10

/* ...but a dummy load after the SC can restore the necessary orderings more cheaply than a fence*/
run lkmm_replace_trailing_fence_with_load {
  some disj a, b, c, d, e, f, g : Event, disj x, y, z : Address |
    a->b + b->c + c->d + d->e + e->f + f->g in ^po
    and a in x.~address
    and b in Fence.pr.pw.sr.sw
    and c in LoadReserve.acquireRCsc & z.~address
    and d in StoreConditional.releaseRCsc & z.~address
    and c.pair = d
    and ((e in Load & Acquire & z.~address) // and f is whatever
      or (e in Load           & z.~address and f in Fence.pr.sr.sw))
    and g in y.~address
    and RISCV_mm
    and some iden & ppo.(gmo & address.~address).(d <: ^po :> g).(gmo & address.~address)
} for 14
