/*

Finish the specification of this notification concept,
including its events, scenarios, and operational principles.

*/ 

sig Event {}

sig User {
	var subscriptions : set Event,
	var notifications : set Event
}

pred stutter {
	subscriptions' = subscriptions
	notifications' = notifications
}

pred read [u : User] {
	// Read all notifications
	some u.notifications

	notifications' = notifications - u->Event
	subscriptions' = subscriptions
}

pred subscribe [u : User, e : Event] {
	// Subscribe an event
	e not in u.subscriptions

	notifications' = notifications
	subscriptions' = subscriptions + u->e
}

pred unsubscribe [u : User, e : Event] {
	// Unsubscribe from a event
	e in u.subscriptions

	notifications' = notifications -  u->e
	subscriptions' = subscriptions - u->e
}

pred occur [e : Event] {
	// Occurrence of an event
	notifications' = notifications + subscriptions :> e
	subscriptions' = subscriptions
}

fact {
	no subscriptions
	no notifications
	always {
		stutter or
		(some u : User | read[u]) or
		(some u : User, e : Event | subscribe[u,e] or unsubscribe[u,e]) or
		(some e : Event | occur[e])
	}
}

// Validation

run Example {
	// Empty run to be used for simulation
}

run Scenario1 {
	// An event is subscribed, then occurs, and the respective notification is read 
	some u : User, e : Event {
		subscribe[u,e];
		occur[e];
		read[u]
	}
} expect 1

run Scenario2 {
	// An event is subscribed, unsubscribed, and then occurs
	some u : User, e : Event {
		subscribe[u,e];
		unsubscribe[u,e];
		occur[e]
	}
} expect 1

run Scenario3 {
	// An event is subscribed by two users and then occurs
	some disj u1, u2 : User, e : Event {
		subscribe[u1,e];
		subscribe[u2,e];
		occur[e]
	}
} expect 1

run Scenario4 {
	// An user subscribes two events, then both occur, then unsubscribes one of them, and finally reads the notifications
	some u : User, disj e1, e2 : Event {
		subscribe[u,e1];
		subscribe[u,e2];
		occur[e1];
		occur[e2];
		unsubscribe[u,e1];
		read[u]
	}
} expect 1

run Scenario5 {
	// An user subscribes the same event twice in a row
	some u : User, e : Event {
		subscribe[u,e];
		subscribe[u,e]
	}
} expect 0

run Scenario6 {
	// Eventually an user reads nofications twice in a row
	eventually some u : User {
		read[u]; 
		read[u]
	}
} expect 0

// Verification 

check OP1 {
	// Users can only have notifications of subscribed events
	all u : User | always (u.notifications in u.subscriptions)
}

check OP2 {
	// Its not possible to read notifications before some event is subscribed
	all u : User | read[u] implies once (some e : Event | subscribe[u,e])
}

check OP3 {
	// Unsubscribe undos subscribe
	all u : User, e : Event | always(subscribe[u,e] and unsubscribe[u,e] implies u.subscriptions'' = u.subscriptions)
}

check OP4 {
	// Notify is idempotent
	all e : Event | always ((occur[e]; occur[e]) implies (occur[e];stutter))
}

check OP5 {
	// After reading the notifications it is only possible to read again after some notification on a subscribed event occurs
	all u : User | always (read[u] implies after (read[u] implies once (some e : Event | subscribe[u,e] and occur[e])))
}
