---- MODULE JobSystem ----

EXTENDS Naturals, FiniteSets, Sequences

----

CONSTANT NULL
VARIABLES server, runners, messages
vars == <<server, runners, messages>>

----

Maybe(T) ==
  T \cup {NULL}

ID == Nat

Job == [
  id: ID
]

Message == [
  kind: {"job-request"}
]

Server == [
  state: {"init", "waiting-for-job-for-runner"},
  jobs: SUBSET Job,
  message: Maybe(Message)
]

Runner == [
  id: ID,
  mode: {"static", "on-demand"},
  state: {"init", "waiting-for-assignment"},
  job: Maybe(Job)
]

TypeOK ==
  /\ server \in Server
  /\ runners \subseteq Runner
  /\ messages \subseteq Message

----

Init ==
  /\ server = [
       state   |-> "init",
       jobs    |-> {},
       message |-> NULL
     ]
  /\ runners = {
       [
         id    |-> 1,
         mode  |-> "static",
         state |-> "init",
         job   |-> NULL
       ]
     }
  /\ messages = {}

StaticRunnerSendsJobRequest ==
  \E runner \in runners :
    /\ runner.mode = "static"
    /\ runner.state = "init"
    /\ runners' = (runners \ {runner}) \cup {[runner EXCEPT !.state = "waiting-for-assignment"]}
    /\ messages' = messages \cup {[kind |-> "job-request", runnerId |-> runner.id]}
    /\ UNCHANGED <<server>>

ServerReceivesJobRequest ==
  /\ server.state = "init"
  /\ \E message \in messages :
        /\ message.kind = "job-request"
        /\ server' = [server EXCEPT
             !.state = "waiting-for-job-for-runner",
             !.message = message
           ]
        /\ messages' = messages \ {message}
        /\ UNCHANGED runners

Next ==
  \/ StaticRunnerSendsJobRequest
  \/ ServerReceivesJobRequest

Spec ==
  Init /\ [][Next]_vars

====
