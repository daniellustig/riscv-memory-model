////////////////////////////////////////////////////////////////////////////////
// =RVWMO axioms=

// Preserved Program Order
fun ppo : Event->Event {
  // same-address ordering
  po_loc :> Store

  // explicit synchronization
  + ppo_fence
  + Load.aq <: ^po
  + ^po :> Store.rl
  + Store.aq.rl <: ^po :> Load.aq.rl
  + ^po :> Load.sc
  + Store.sc <: ^po

  // dependencies
  + addr
  + data
  + ctrl :> Store
  + (addr+data).successdep

  // CoRR
  + rdw & po_loc_no_intervening_write

  // pipeline dependency artifacts
  + (addr+data).rfi
  + addr.^po :> Store
  + ctrl.(FenceI <: ^po)
  + addr.^po.(FenceI <: ^po)
}

// the global memory order respects preserved program order
fact { ppo in gmo }

// Load value axiom
fun candidates[r: Load] : set Store {
  (r.~gmo & Store & same_addr[r]) // writes preceding r in gmo
  + (r.^~po & Store & same_addr[r]) // writes preceding r in po
}

fun latest_among[s: set Event] : Event { s - s.~gmo }

pred LoadValue {
  all w: Store | all r: Load |
    w->r in rf <=> w = latest_among[candidates[r]]
}

fun after_reserve_of[r: Load] : Event { latest_among[r + r.~rf].gmo }

pred Atomicity {
  all r: Store.~rmw |               // starting from the read r of an atomic,
    no x: Store & same_addr[r + r.rmw] | // there is no write x to the same addr
      x not in same_hart[r]         // from a different hart, such that
      and x in after_reserve_of[r]  // x follows (the write r reads from) in gmo
      and r.rmw in x.gmo            // and r follows x in gmo
}

pred RISCV_mm { LoadValue and Atomicity }

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
  aq: lone MemoryEvent, // opcode bit
  rl: lone MemoryEvent, // opcode bit
  sc: lone MemoryEvent, // for AMOs with .aq and .rl, to distinguish from lr/sc
  gmo: set MemoryEvent   // global memory order
}
sig Load extends MemoryEvent {
  addr: set Event,
  ctrl: set Event,
  data: set Store,
  successdep: set Event,
  rmw: lone Store
}
sig Store extends MemoryEvent {
  rf: set Load
}
sig Fence extends Event {
  pr: lone Fence, // opcode bit
  pw: lone Fence, // opcode bit
  sr: lone Fence, // opcode bit
  sw: lone Fence  // opcode bit
}
sig FenceI extends Event {}
   
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
}

// auxiliary definitions
fun po_loc_no_intervening_write : MemoryEvent->MemoryEvent {
  po_loc - ((po_loc :> Store).po_loc)
}

fun RFInit : Load { Load - Store.rf }
fun rsw : Load->Load { ~rf.rf + (RFInit <: address.~address :> RFInit) }
fun rdw : Load->Load { (Load <: po_loc :> Load) - rsw }

fun po_loc : Event->Event { ^po & address.~address }
fun same_hart[e: Event] : set Event { e + e.^~po + e.^po }
fun same_addr[e: Event] : set Event { e.address.~address }

// basic facts about well-formed execution candidates
fact { acyclic[po] }
fact { all e: Event | one e.*~po.~start }  // each event is in exactly one hart
fact { rf.~rf in iden } // each read returns the value of only one write
fact { total[gmo, MemoryEvent] } // gmo is a total order over all MemoryEvents

//rf
fact { rf in address.~address }
fun rfi : Store->Load { Store <: po_loc_no_intervening_write :> Load }

//dep
fact { addr + ctrl + data in ^po }
fact { successdep in (Store.~rmw) <: ^po }
fact { ctrl.*po in ctrl }
fact { rmw in ^po }

// to unclutter the display a bit
fun mo : MemoryEvent->MemoryEvent {
  gmo - (gmo.gmo)
}

////////////////////////////////////////////////////////////////////////////////
// =Opcode encoding restrictions=

// opcode bits are either set (encoded, e.g., as f.pr in iden) or unset
// (f.pr not in iden).  The bits cannot be used for anything else
fact { pr + pw + sr + sw + aq + rl + sc in iden }
fact { sc in aq & rl }
fact { Load.sc.rmw in Store.sc and Store.sc.~rmw in Load.sc }

// Fences must have either pr or pw set, and either sr or sw set
fact { Fence in Fence.(pr + pw) & Fence.(sr + sw) }

// there is no write-acquire, but there is write-strong-acquire
fact { Store.aq in Store.aq.rl }
fact { Load.rl in Load.aq.rl }

////////////////////////////////////////////////////////////////////////////////
// =Alloy shortcuts=
pred acyclic[rel: Event->Event] { no iden & ^rel }
pred total[rel: Event->Event, bag: Event] {
  all disj e, e': bag | e->e' in rel + ~rel
  acyclic[rel]
}
