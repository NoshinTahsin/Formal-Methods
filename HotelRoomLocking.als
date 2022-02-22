module examples/hotel
open util/ordering[Time] as TO
open util/ordering[Key] as KO

//Signatures and Fields
sig Key, Time {}

sig Room {
	keys: set Key,
	currentKey: keys one -> Time
}

sig Guest {
	keys: Key -> Time
}

one sig FrontDesk {
	lastKey: (Room -> lone Key) -> Time,
	occupant: Room -> Guest -> Time
}

//Room Constraint
fact DisjointKeySets {
	//Room <: keys = Room lone -> Key
	all k: Key | lone keys.k
}

//New Key Generation
fun nextKey [k: Key, ks: set Key]: set Key {
	KO/min [KO/nexts[k] & ks]
}

//Hotel Operations: Initial State
pred init [t: Time] {
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t
}

//guest entry
pred entry[t, tnew: Time, g: Guest, r: Room, k: Key] {
	k in g.keys.t
	let ck = r.currentKey |
	(k = ck.t and ck.tnew = ck.t) or
	(k = nextKey[ck.t, r.keys] and ck.tnew = k)
	noRoomChangeExcept [t, tnew, r]
	noGuestChangeExcept [t, tnew, none]
	noFrontDeskChange [t, tnew]
}

//checkout
pred checkout (t, tnew: Time, g: Guest) {
	let occ = FrontDesk.occupant {
	some occ.t.g
	occ.tnew = occ.t - Room -> g
	}
	FrontDesk.lastKey.t = FrontDesk.lastKey.tnew
	noRoomChangeExcept [t, tnew, none]
	noGuestChangeExcept [t, tnew, none]
}

//checkin
pred checkin (t, tnew: Time, g: Guest, r: Room, k: Key) {
	g.keys.tnew = g.keys.t + k
	let occ = FrontDesk.occupant {
		no occ.t [r]
		occ.tnew = occ.t + r -> g
	}
	let lk = FrontDesk.lastKey {
		lk.tnew = lk.t ++ r -> k
		k = nextKey [lk.t [r], r.keys]
	}
	noRoomChangeExcept [t, tnew, none]
	noGuestChangeExcept [t, tnew, g]
}

//frame conditions
pred noFrontDeskChange (t, tnew: Time) {
	FrontDesk.lastKey.t = FrontDesk.lastKey.tnew
	FrontDesk.occupant.t = FrontDesk.occupant.tnew
}

pred noRoomChangeExcept (t, tnew: Time, rs: set Room) {
	all r: Room - rs | r.currentKey.t = r.currentKey.tnew
}

pred noGuestChangeExcept (t, tnew: Time, gs: set Guest) {
	all g: Guest - gs | g.keys.t = g.keys.tnew
}

//trace generation
fact Traces {
	init [TO/first]
	all t: Time - TO/last| let tnew= TO/next[t] |
	some g: Guest, r: Room, k: Key |
	entry [t, tnew, g, r, k]
	or checkin [t, tnew, g, r, k]
	or checkout [t, tnew, g]
}

//checking if unauthorized entry is possible
assert NoBadEntry {
	all t: Time, r: Room, g: Guest, k: Key | let tnew= TO/next[t] |
	let o = FrontDesk.occupant.t [r] |
	entry [t, tnew, g, r, k] and some o => g in o
}

//necessary restriction
fact NoIntervening {
	all t: Time - TO/last| let tnew = TO/next [t], tnext = TO/next[tnew] |
	all g: Guest, r: Room, k: Key |
	checkin [t, tnew, g, r, k] => (entry [tnew, tnext, g, r, k] or no tnext)
}
//check NoBadEntry for 5 but 3 Room, 3 Guest, 9 Time
check NoBadEntry for 5 but 2 Room, 2 Guest, 5 Time


