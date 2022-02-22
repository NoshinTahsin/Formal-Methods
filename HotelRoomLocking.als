module examples/hotel
open util/ordering[Time] as TO
open util/ordering[Key] as KO

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

fact DisjointKeySets {
	//Room <: keys = Room lone -> Key
	all k: Key | lone keys.k
}

fun nextKey [k: Key, ks: set Key]: set Key {
	KO/min [KO/nexts[k] & ks]
}

pred init [t: Time] {
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t
}

/*abstract sig Event {
	pre, post: Time,
	guest: Guest
}

abstract sig RoomKeyEvent extends Event {
	room: Room,
	key: Key
}

sig Entry extends RoomKeyEvent {} {
	key in guest.keys.pre
	let ck = room.currentKey |
	(key = ck.pre and ck.post = ck.pre) or
	(key = nextKey[ck.pre, room.keys] and ck.post = key)
	-- frame conditions
	noFrontDeskChange[pre, post]
	noRoomChangeExcept[room, pre, post]
	noGuestChangeExcept[none, pre, post]
}*/

pred entry[t, tnew: Time, g: Guest, r: Room, k: Key] {
	k in g.keys.t
	let ck = r.currentKey |
	(k = ck.t and ck.tnew = ck.t) or
	(k = nextKey[ck.t, r.keys] and ck.tnew = k)
	noRoomChangeExcept [t, tnew, r]
	noGuestChangeExcept [t, tnew, none]
	noFrontDeskChange [t, tnew]
}

/*
pred noFrontDeskChange [t,tnew: Time]
{
	FrontDesk.lastKey.t = FrontDesk.lastKey.tnew
	FrontDesk.occupant.t = FrontDesk.occupant.tnew
}

pred noRoomChangeExcept [rs: set Room, t,tnew: Time]
{
	all r: Room - rs |
	r.currentKey.t = r.currentKey.tnew
}

pred noGuestChangeExcept [gs: set Guest, t,tnew: Time]
{
	all g: Guest - gs | g.keys.t = g.keys.tnew
}*/

pred checkout (t, tnew: Time, g: Guest) {
	let occ = FrontDesk.occupant {
	some occ.t.g
	occ.tnew = occ.t - Room -> g
	}
	FrontDesk.lastKey.t = FrontDesk.lastKey.tnew
	noRoomChangeExcept [t, tnew, none]
	noGuestChangeExcept [t, tnew, none]
}

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

fact Traces {
	init [TO/first]
	all t: Time - TO/last| let tnew= TO/next[t] |
	some g: Guest, r: Room, k: Key |
	entry [t, tnew, g, r, k]
	or checkin [t, tnew, g, r, k]
	or checkout [t, tnew, g]
}

assert NoBadEntry {
	all t: Time, r: Room, g: Guest, k: Key | let tnew= TO/next[t] |
	let o = FrontDesk.occupant.t [r] |
	entry [t, tnew, g, r, k] and some o => g in o
}

fact NoIntervening {
	all t: Time - TO/last| let tnew = TO/next [t], tnext = TO/next[tnew] |
	all g: Guest, r: Room, k: Key |
	checkin [t, tnew, g, r, k] => (entry [tnew, tnext, g, r, k] or no tnext)
}
check NoBadEntry for 5 but 3 Room, 3 Guest, 9 Time

/*sig Checkin extends RoomKeyEvent {} {
	
	keys.post = keys.pre + guest -> key
	
	let occ = FrontDesk.occupant {
		no occ.pre [room]
		occ.post = occ.pre + room -> guest
	}

	let lk = FrontDesk.lastKey {
		lk.post = lk.pre ++ room -> key
		key = nextKey [lk.pre [room], room.keys]
	}

	noRoomChangeExcept[none, pre, post]
	noGuestChangeExcept[guest, pre, post]
}

/*sig Checkout extends Event {} {
	let occ = FrontDesk.occupant {
		some occ.pre.guest
		occ.post = occ.pre - Room -> guest
	}
	
	-- frame condition
	FrontDesk.lastKey.pre = FrontDesk.lastKey.post
	noRoomChangeExcept[none, pre, post]
	noGuestChangeExcept[none, pre, post]
}

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
assert NoBadEntry {
	all e: Entry | let o = FrontDesk.occupant.(e.pre) [e.room] |
	some o => e.guest in o
}

check NoBadEntry for 5 but 2 Room, 2 Guest, 5 Time //,8 Event

fact NoIntervening {
	all c: Checkin |
	c.post = TO/last
	or some e: Entry {
		e.pre = c.post
		e.room = c.room
		e.guest = c.guest
	}
}*/

