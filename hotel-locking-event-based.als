//An event-based variation
module examples/hotelEvents
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

/*Instead of writing a predicate for each operation, 
a signature is declared whose atoms represent a set of events. 
The Checkin signature represents the set of all events in which a guest checks in. 
The constraints that were in the predicate now appear instead as signature facts.
Arguments to operation predicates now become fields of the event signatures.*/
abstract sig Event {
	pre, post: Time,
	guest: Guest
}

abstract sig RoomKeyEvent extends Event {
	room: Room,
	key: Key
}

//guest entry
sig Entry extends RoomKeyEvent {} {
	key in guest.keys.pre
	let ck = room.currentKey |
	(key = ck.pre and ck.post = ck.pre) or
	(key = nextKey[ck.pre, room.keys] and ck.post = key)
	-- frame conditions
	/*noFrontDeskChange[pre, post]
	noRoomChangeExcept[room, pre, post]
	noGuestChangeExcept[none, pre, post]*/
}

/*pred entry[t, tnew: Time, g: Guest, r: Room, k: Key] {
	k in g.keys.t
	let ck = r.currentKey |
	(k = ck.t and ck.tnew = ck.t) or
	(k = nextKey[ck.t, r.keys] and ck.tnew = k)
	noRoomChangeExcept [t, tnew, r]
	noGuestChangeExcept [t, tnew, none]
	noFrontDeskChange [t, tnew]
}*/

//checkout
sig Checkin extends RoomKeyEvent {} {
	
	keys.post = keys.pre + guest -> key
	
	let occ = FrontDesk.occupant {
		no occ.pre [room]
		occ.post = occ.pre + room -> guest
	}

	let lk = FrontDesk.lastKey {
		lk.post = lk.pre ++ room -> key
		key = nextKey [lk.pre [room], room.keys]
	}

	//why removing these?
	//noRoomChangeExcept[none, pre, post]
	//noGuestChangeExcept[guest, pre, post]
}

//checkout
sig Checkout extends Event {} {
	let occ = FrontDesk.occupant {
		some occ.pre.guest
		occ.post = occ.pre - Room -> guest
	}
	
	-- frame condition
	/*FrontDesk.lastKey.pre = FrontDesk.lastKey.post
	noRoomChangeExcept[none, pre, post]
	noGuestChangeExcept[none, pre, post]*/
}

//trace generation
fact Traces {
	init [TO/first]
	all t: Time - TO/last| let tnew = TO/next[t] |
	some e: Event {
		e.pre = t and e.post = tnew
		currentKey.t != currentKey.tnew => e in Entry
		occupant.t != occupant.tnew => e in Checkin + Checkout
		(lastKey.t != lastKey.tnew or keys.t != keys.tnew)
		=> e in Checkin
	}
}

//ekhane jhamela
//checking if unauthorized entry is possible
assert NoBadEntry {
	all e: Entry | let o = FrontDesk.occupant.(e.pre) [e.room] |
	some o => e.guest in o
}

check NoBadEntry for 5 but 2 Room, 2 Guest, 5 Time, 8 Event

//necessary restriction
fact NoIntervening {
	all c: Checkin |
	c.post = TO/last
	or some e: Entry {
		e.pre = c.post
		e.room = c.room
		e.guest = c.guest
	}
}

