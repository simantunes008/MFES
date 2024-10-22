/*

Finish the specification of this reservation concept,
including its events, scenarios, and operational principles.

*/ 



sig Resource {}

sig User {
	var reservations : set Resource
}

var sig Available in Resource {}




// Clauses in a predicate are interpreted as conjuncts
// -- no need for "and".
// The use of prime notation ( ' ) allows for system
// actions to be specified.
// Clauses referring only to the pre-state can be seen
// as pre-conditions


pred reserve[u : User, r : Resource] {
	// Make a reservation

	// Precondition: a logic condition on the pre-state
	
	r in Available

	// Effect: a formula involving pre- and post-state
	
	Available' = Available - r
	reservations' = reservations + u->r
}



pred cancel[u : User, r : Resource] {
	// Cancel a reservation

	r in u.reservations
	
	Available' = Available + r
	reservations' = reservations - u->r	
}



pred use[u : User, r : Resource] {
	// Use a reserved resource - does not liberate it 

	r in u.reservations
	
	Available' = Available
	reservations' = reservations - u->r	
}



pred cleanup {
	// Make all used resources available again

	some Resource - Available - User.reservations

	Available' = Resource - User.reservations
	reservations' = reservations
}



pred stutter {
	Available' = Available
	reservations' = reservations
}





fact {
	// System Init
	Available = Resource
	no reservations

	// Dynamics
	always {
		(some u : User , r : Resource | reserve[u,r])
	 	or 
	 	(some u : User , r : Resource | cancel[u,r])
		or 
		(some u : User , r : Resource | use[u,r])
		or 
		cleanup
		or 
		stutter
	}
}





// Validation

run Example {
	// Empty run to be used for simulation
}






