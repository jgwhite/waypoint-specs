---- MODULE JobSystem ----

EXTENDS FiniteSets, Sequences

----

CONSTANT NULL
VARIABLES server, runners
vars == <<server, runners>>

----

Maybe(T) ==
  T \cup {NULL}

ID == STRING

Job == [
  id: ID
]

Server == [
  jobs: SUBSET Job
]

Runner == [
  id: ID,
  mode: {"static", "on-demand"},
  state: {"idle"},
  job: Maybe(Job)
]

TypeOK ==
  /\ server \in Server
  /\ runners \subseteq Runner

----

Init ==
  /\ server = [jobs |-> {}]
  /\ runners = {}

Next ==
  UNCHANGED vars

Spec ==
  Init /\ [][Next]_vars

====
