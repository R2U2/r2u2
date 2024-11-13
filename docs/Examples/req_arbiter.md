# Request Arbiter System Example
The following example is adapted from R2U2's [CAV 2023 tool paper](https://link.springer.com/chapter/10.1007/978-3-031-37709-9_23) that reasons over a system with two arbiters that grants or rejects requests as they are received. 
Requests have a state that is either `waiting`, `granted`, or `rejected` and a floating-point number denoting the time it has been active.
Each arbiter can handle at most five requests (for simplicity).
The specification uses a number of features in tandem to express two properties:

1. The difference between requests' `request_0` and `request_1` time active shall be no greater than 10 seconds.
2. For each request in each arbiter, that request shall be granted or rejected within the next 5 seconds and until then shall be waiting.

## C2PO File
As this is a more comprehensive example, we'll walk through the C2PO input file section-by-section.

### STRUCT Section
First we define our data structures to organize our data. We need two data structures: one for requests and another for arbiters. 
The `Request` struct requires fields to encode its state and its time active and the `Arbiter` struct requires a single field for a set of `Request` structs.

     STRUCT
        Request: { state: int; time_active: float; };
        Arbiter: { ReqSet: set<Request>; };

### INPUT Section
Recall that our system has two arbiters and each arbiter can handle only a maximum of five requests at once -- therefore we need inputs for up to ten `Request` structs. 
This means that we declare ten `state` variables and ten `time_active` variables; one for each `Request` we'll define.
We'll encode the `state` variables as integers and define each possible value as a constant later.

    INPUT
       -- State inputs
       state_0, state_1, state_2, state_3, state_4, 
       state_5, state_6, state_7, state_8, state_9: int;

       -- Time active inputs
       time_active_0, time_active_1, time_active_2, time_active_3, time_active_4,
       time_active_5, time_active_6, time_active_7, time_active_8, time_active_9: float;

### DEFINE Section
Now we use the `DEFINE` section to define all our data structures using our inputs and any constants we need. 
First we declare all the possible state values:

    DEFINE
       WAIT := 0; 
       GRANT := 1; 
       REJECT := 2;

Next we declare the ten requests, where the order in which the members of the `Request` struct definition determines the order we must pass the corresponding signal:

       request_0 := Request(state_0, time_active_0); 
       request_1 := Request(state_1, time_active_1); 
       request_2 := Request(state_2, time_active_2); 
       request_3 := Request(state_3, time_active_3); 
       request_4 := Request(state_4, time_active_4); 
       request_5 := Request(state_5, time_active_5); 
       request_6 := Request(state_6, time_active_6); 
       request_7 := Request(state_7, time_active_7); 
       request_8 := Request(state_8, time_active_8); 
       request_9 := Request(state_9, time_active_9); 

Then we declare the arbiters:

       Arb0 := Arbiter({request_0, request_1, request_2,
                        request_3, request_4}); 
       Arb1 := Arbiter({request_5, request_6, request_7,
                        request_8, request_9});

And finally we define a set of the defined arbiters:

       ArbSet := {Arb0, Arb1};

### FTSPEC Section

Now to define the specifications using our structured data, we start with the first English requirement: "The difference between requests' `request_0` and `request_1` time active shall be no greater than 10 seconds."

    FTSPEC
       (rq0.time_active - rq1.time_active) < 10.0 &&
       (rq1.time_active - rq0.time_active) < 10.0;

Next, recall the second requirement we have: "For each request in each arbiter, that request shall be granted or rejected within the next 5 seconds and until then shall be waiting." This time, we use the *set aggregation* operator `foreach`, which applies its argument expression over each element in the given set and returns true if every element in the set satisfies the expression.

       foreach(arb: ArbSet)(
         foreach(rq: arb.ReqSet)(
           (rq.state == WAIT) U[0,5] (rq.state == GRANT || 
                                       rq.state == REJECT)
         )
       );

## Compiling with C2PO

Since we are using compound arithmetic expressions (e.g., `(rq0.time_active - rq1.time_active) < 10.0`), we need to use the Booleanizer for our front end.