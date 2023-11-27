# Specification Writing

R2U2 compares the current system run to a specification and notes when they differ. A specification is any statement that describes a, possibly temporal, pattern over the system variables observable by R2U2.

## Common Types of Specifications

!!Requirements!! describe safety behaviors of the system that we want to always hold. Examples include, "every request will be acknowledged and either granted or rejected within 2 minutes," and "the air traffic control system will never direct two planes in a projected loss of separation to get closer to each other." Requirements can either describe positive ("the system must always do this to be safe") or negative ("the system should never do this") behaviors. A good way to brainstorm requirements that would make specifications amenable to runtime monitoring is to ask:
* What emergent behaviors do we expect a (safe) correctly-operating system to have?
* What would be bad? What actions or scenarios should never happen?

!!Fault Signatures!! describe patterns of known possible faults or system error signatures so that R2U2 can identify them and detect them quickly. Examples of temporal fault signatures include a flaky wire (e.g., a signal that changes back-and-forth more often than is realistic as a sensor reading), a buffer overflow, an iced pitot tube, and a software error code embedding in an output stream. 

!!Sanity Checks!! describe independent checks of common sense, often physical, realities of the system to provide a reliable spot-check that something is wrong. Examples include, "the temperature cannot rise more than 10 degrees in one second," and, "the navigation system and flight computer should always agree on what waypoint the vehicle is currently visiting." Common sanity checks detailed in \cite{Roz16} include the following.

*Ranges* describe checks of well-defined operating ranges, both ranges of the values sensors can report and ranges of operation.

*Rates* describe checks that value changes fall within realistic bounds, both for the sensitivity and tolerances of the individual sensor and for the physics of the system. 

*Relationships* describe predictable relationships between multiple sensors or software values, and often compare temporal outputs from related or redundant sensors for correctness.

*Control Sequences* describe predictable sequences of actions or events that must happen in a specific temporal order to complete a procedure or carry out a command sent to the system. 

*Consistency Checks* describe checks that all components have the same view of system state/environment, considering both intra- and inter-component properties.
k