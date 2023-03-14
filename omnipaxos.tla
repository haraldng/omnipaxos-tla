----------------------------- MODULE omnipaxos -----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT NSERVERS, MAXB, NPROPOSALS

Servers == 1..NSERVERS
Ballots == 1..MAXB

MAJORITY == NSERVERS \div 2 + 1

Max(i, j) == IF i > j THEN i ELSE j
Prefix(log,idx) == IF log = <<>> THEN <<>> ELSE SubSeq(log, 1, idx)
Suffix(log,idx) == IF log = <<>> \/ Len(log) <= idx THEN <<>> ELSE SubSeq(log, idx+1, Len(log))

AcceptedSet(S, idx) == {x \in Servers: S[x] >= idx}     \* the set that has accepted at least up to idx
IsChosen(S, idx) == IF Cardinality(AcceptedSet(S, idx)) >= MAJORITY THEN TRUE ELSE FALSE
\* pick the highest promise. Either the highest ballot or highest ballot AND longest log.
GetMaxPromise(P) == CHOOSE x \in P: \A y \in P: y.accRnd < x.accRnd \/ (y.accRnd <= x.accRnd /\ y.logIdx <= x.logIdx) 

(*--algorithm OmniPaxos
 { 
    variables
        mailbox = [s \in Servers |-> <<>>], 
        logs = [s \in Servers |-> <<>>],
        decidedIdx = [s \in Servers |-> 0],
        \* The following variables are only needed for model checking.
        last_decided = [s \in Servers |-> <<>>],    \* last decided log of every server. Used to check SC3 Integrity property.
        proposals = NPROPOSALS;                     \* proposals remaining
        
    macro ClearLeaderState(){
        promises := {};
        accepted := [s \in Servers |-> 0];
        chosenIdx := 0;
    }
    
    macro ReadMsg() {
        read_msg := Head(mailbox[self]);
        mailbox[self] := Tail(mailbox[self]);
    }
            
    macro Decide(idx) {
        assert(last_decided[self] = Prefix(logs[self], Len(last_decided[self])));   \* Assert SC3 Integrity: the last decided is a strict prefix to what is decided now.
        decidedIdx[self] := idx;
        last_decided[self] := Prefix(logs[self], idx);
        \*print <<"Server: ", self, "decidedIdx = ", idx>>;          
    }
    
    macro HandlePrepare(msg) {
        if (msg.n > promisedRnd) {
            state := <<"FOLLOWER", "PREPARE">>;
            promisedRnd := msg.n;
            if (acceptedRnd >= msg.accRnd) {
                if (acceptedRnd > msg.accRnd) { suffix := Suffix(logs[self], msg.decIdx); }
                else suffix := Suffix(logs[self], msg.logIdx);  
            } else {
                suffix := <<>>;
            };
            out_msg := [type |-> "PROMISE", from |-> self, n |-> msg.n, accRnd |-> acceptedRnd, logIdx |-> Len(logs[self]), decIdx |-> decidedIdx[self], sfx |-> suffix];        
            mailbox[msg.from] := Append(mailbox[msg.from], out_msg);
        }            
    }
    
    macro HandlePropose(C) {
        either {
            await(state = <<"LEADER", "PREPARE">>);
            buffer := Append(buffer, C);
        } or {
            await(state = <<"LEADER", "ACCEPT">>);
            logs[self] := Append(logs[self], C);
            accepted[self] := Len(logs[self]);
            out_msg := [type |-> "ACCEPT", from |-> self, n |-> currentRnd, C |-> C];
            with (p \in {x.from : x \in { y \in promises : y.from /= self} }) {
                mailbox[p] := Append(mailbox[p], out_msg);
            }
        }
    
    }
    
    macro HandleAccept(msg) {
        if (msg.n = promisedRnd /\ state = <<"FOLLOWER", "ACCEPT">>) {
            logs[self] := Append(logs[self], msg.C);
            out_msg := [type |-> "ACCEPTED", from |-> self, n |-> currentRnd, logIdx |-> Len(logs[self])];
            mailbox[msg.from] := Append(mailbox[msg.from], out_msg);
        }
    }
    
    macro HandleAccepted(msg) {
        if (msg.n = currentRnd /\ state = <<"LEADER", "ACCEPT">>) {
            accepted[msg.from] := msg.logIdx;
            if (msg.logIdx > chosenIdx) {
                if (IsChosen(accepted, msg.logIdx) = TRUE) {
                    chosenIdx := msg.logIdx;
                    Decide(msg.logIdx);
                    out_msg := [type |-> "DECIDE", from |-> self, n |-> currentRnd, decIdx |-> chosenIdx];
                    with (p \in {x.from : x \in promises} \ {self}) {
                        mailbox[p] := Append(mailbox[p], out_msg);
                    }
                }
            }
        }
    }
    
    macro HandleDecide(msg) {
        if (msg.n = promisedRnd /\ state = <<"FOLLOWER", "ACCEPT">>) {
            Decide(msg.decIdx);
        }        
    }
    
    fair process (s \in Servers)
    variable promisedRnd=0, acceptedRnd=0, state = <<"FOLLOWER", "PREPARE">>, currentRnd=0,
             promises={}, maxProm = <<0, 0, 0>>, accepted=[s \in Servers |-> 0], chosenIdx=0, buffer = <<>>,
             \* auxiliary variables needed in PlusCal
             read_msg = [a |-> 0], out_msg = [a |-> 0], suffix = <<>>, syncidx=0, idx=0;
    {
HANDLE: while (TRUE) {
            await(Len(mailbox[self]) > 0);
            ReadMsg();
            either {
LEADER:         await(read_msg.type = "LEADER");
                if (read_msg.n > promisedRnd /\ read_msg.s = self) {
                    ClearLeaderState();
                    state := <<"LEADER", "PREPARE">>;
                    currentRnd := read_msg.n;
LP:                 promises := promises \union {[accRnd |-> acceptedRnd, logIdx |-> Len(logs[self]), from |-> self, decIdx |-> decidedIdx[self], sfx |-> <<>>]};
                    out_msg := [type |-> "PREPARE", from |-> self, n |-> currentRnd, accRnd |-> acceptedRnd, logIdx |-> Len(logs[self]), decIdx |-> decidedIdx[self]];        
                    with (f \in (Servers \ {self})) {
                        mailbox[f] := Append(mailbox[f], out_msg);
                    }
                }
            } or {
PREPARE:        await(read_msg.type = "PREPARE");
                HandlePrepare(read_msg);    
            } or {
PROMISE:        await(read_msg.type = "PROMISE");
                if (read_msg.n = currentRnd) {
                    promises := promises \union {[accRnd |-> read_msg.accRnd, logIdx |-> read_msg.logIdx, from |-> read_msg.from, decIdx |-> read_msg.decIdx, sfx |-> read_msg.sfx]};
                    either {
                        await state = <<"LEADER", "PREPARE">>;
                        if (Cardinality(promises) >= MAJORITY) {
                            maxProm := GetMaxPromise(promises);
                            if (maxProm.accRnd /= acceptedRnd) {
                                logs[self] := Prefix(logs[self], decidedIdx[self]);
                            };
P1:                         logs[self] := logs[self] \o maxProm.sfx \o buffer;
                            acceptedRnd := currentRnd;
                            accepted[self] := Len(logs[self]);
                            state := <<"LEADER", "ACCEPT">>;
                            buffer := <<>>;
                            with (p \in {[from |-> x.from, accRnd |-> x.accRnd, logIdx |-> x.logIdx, decIdx |-> x.decIdx] : x \in {y \in promises : y.from /= self} }) {
                                if (p.accRnd = maxProm.accRnd) {
                                    syncidx := p.logIdx;
                                }
                                else syncidx := p.decIdx;
                                out_msg := [type |-> "ACCEPTSYNC", from |-> self, n |-> currentRnd, sfx |-> Suffix(logs[self], syncidx), syncIdx |-> syncidx];
                                mailbox[p.from] := Append(mailbox[p.from], out_msg);
                            } 
                        }
                    } or {
                        await state = <<"LEADER", "ACCEPT">>;
                        if (read_msg.accRnd = maxProm.accRnd) {
                            syncidx := maxProm.logIdx;
                        };
                        else syncidx := read_msg.decIdx;
                        out_msg := [type |-> "ACCEPTSYNC", from |-> self, n |-> currentRnd, sfx |-> Suffix(logs[self], syncidx), syncIdx |-> syncidx];
                        mailbox[read_msg.from] := Append(mailbox[read_msg.from], out_msg);
                        idx := Max(chosenIdx, decidedIdx);
                        if (idx > read_msg.decIdx) {
P2:                         out_msg := [type |-> "DECIDE", from |-> self, n |-> currentRnd, decIdx |-> idx];
                            mailbox[read_msg.from] := Append(mailbox[read_msg.from], out_msg);
                        }
                    }
                }   
            } or {
ACCEPTSYNC:     await(read_msg.type = "ACCEPTSYNC");
                if (read_msg.n = promisedRnd /\ state = <<"FOLLOWER", "PREPARE">>) {
                    acceptedRnd := read_msg.n;
                    state := <<"FOLLOWER", "ACCEPT">>;
                    logs[self] := Prefix(logs[self], read_msg.syncIdx);
AS:                 logs[self] := logs[self] \o read_msg.sfx;
                    out_msg := [type |-> "ACCEPTED", from |-> self, n |-> promisedRnd, logIdx |-> Len(logs[self])];
                    mailbox[read_msg.from] := Append(mailbox[read_msg.from], out_msg);
                }  
            } or {
                await(read_msg.type = "ACCEPT");
ACCEPT:         HandleAccept(read_msg);    
            } or {
ACCEPTED:       await(read_msg.type = "ACCEPTED");
                HandleAccepted(read_msg);    
            } or {
DECIDE:         await(read_msg.type = "DECIDE");
                HandleDecide(read_msg);    
            } or {
PROPOSE:        await(read_msg.type = "PROPOSE");
                HandlePropose(read_msg.C);    
            }
        }
    }
    
    \* Process to model external events such as Leader Election and Client requests.
    fair process (ble_client = NSERVERS + 1)
    variable current_rnd = 0, current_leader = 0, out_msg = <<>>;
    {
BLECLIENT:    while (proposals > 0) {
            either {
                await(current_rnd < MAXB);
                current_leader := CHOOSE x \in Servers : x /= current_leader;    \* Create a leader change.
                current_rnd := current_rnd + 1;
                out_msg := [type |-> "LEADER", n |-> current_rnd, s |-> current_leader];
                with (p \in Servers) {
                    mailbox[p] := Append(mailbox[p], out_msg);
                }
            } or {
                await(proposals > 0 /\ current_leader > 0);
                out_msg := [type |-> "PROPOSE", C |-> proposals]; \* propose request
                mailbox[current_leader] := Append(mailbox[current_leader], out_msg);
                proposals := proposals - 1;
            }
        }
    }    
  }
  *)
\* BEGIN TRANSLATION (chksum(pcal) = "8571830a" /\ chksum(tla) = "3fa81dc3")
\* Process variable out_msg of process s at line 114 col 36 changed to out_msg_
VARIABLES mailbox, logs, decidedIdx, last_decided, proposals, pc, promisedRnd, 
          acceptedRnd, state, currentRnd, promises, maxProm, accepted, 
          chosenIdx, buffer, read_msg, out_msg_, suffix, syncidx, idx, 
          current_rnd, current_leader, out_msg

vars == << mailbox, logs, decidedIdx, last_decided, proposals, pc, 
           promisedRnd, acceptedRnd, state, currentRnd, promises, maxProm, 
           accepted, chosenIdx, buffer, read_msg, out_msg_, suffix, syncidx, 
           idx, current_rnd, current_leader, out_msg >>

ProcSet == (Servers) \cup {NSERVERS + 1}

Init == (* Global variables *)
        /\ mailbox = [s \in Servers |-> <<>>]
        /\ logs = [s \in Servers |-> <<>>]
        /\ decidedIdx = [s \in Servers |-> 0]
        /\ last_decided = [s \in Servers |-> <<>>]
        /\ proposals = NPROPOSALS
        (* Process s *)
        /\ promisedRnd = [self \in Servers |-> 0]
        /\ acceptedRnd = [self \in Servers |-> 0]
        /\ state = [self \in Servers |-> <<"FOLLOWER", "PREPARE">>]
        /\ currentRnd = [self \in Servers |-> 0]
        /\ promises = [self \in Servers |-> {}]
        /\ maxProm = [self \in Servers |-> <<0, 0, 0>>]
        /\ accepted = [self \in Servers |-> [s \in Servers |-> 0]]
        /\ chosenIdx = [self \in Servers |-> 0]
        /\ buffer = [self \in Servers |-> <<>>]
        /\ read_msg = [self \in Servers |-> [a |-> 0]]
        /\ out_msg_ = [self \in Servers |-> [a |-> 0]]
        /\ suffix = [self \in Servers |-> <<>>]
        /\ syncidx = [self \in Servers |-> 0]
        /\ idx = [self \in Servers |-> 0]
        (* Process ble_client *)
        /\ current_rnd = 0
        /\ current_leader = 0
        /\ out_msg = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "HANDLE"
                                        [] self = NSERVERS + 1 -> "BLECLIENT"]

HANDLE(self) == /\ pc[self] = "HANDLE"
                /\ (Len(mailbox[self]) > 0)
                /\ read_msg' = [read_msg EXCEPT ![self] = Head(mailbox[self])]
                /\ mailbox' = [mailbox EXCEPT ![self] = Tail(mailbox[self])]
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "LEADER"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "PREPARE"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "PROMISE"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "ACCEPTSYNC"]
                   \/ /\ (read_msg'[self].type = "ACCEPT")
                      /\ pc' = [pc EXCEPT ![self] = "ACCEPT"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "ACCEPTED"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "DECIDE"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "PROPOSE"]
                /\ UNCHANGED << logs, decidedIdx, last_decided, proposals, 
                                promisedRnd, acceptedRnd, state, currentRnd, 
                                promises, maxProm, accepted, chosenIdx, buffer, 
                                out_msg_, suffix, syncidx, idx, current_rnd, 
                                current_leader, out_msg >>

LEADER(self) == /\ pc[self] = "LEADER"
                /\ (read_msg[self].type = "LEADER")
                /\ IF read_msg[self].n > promisedRnd[self] /\ read_msg[self].s = self
                      THEN /\ promises' = [promises EXCEPT ![self] = {}]
                           /\ accepted' = [accepted EXCEPT ![self] = [s \in Servers |-> 0]]
                           /\ chosenIdx' = [chosenIdx EXCEPT ![self] = 0]
                           /\ state' = [state EXCEPT ![self] = <<"LEADER", "PREPARE">>]
                           /\ currentRnd' = [currentRnd EXCEPT ![self] = read_msg[self].n]
                           /\ pc' = [pc EXCEPT ![self] = "LP"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                           /\ UNCHANGED << state, currentRnd, promises, 
                                           accepted, chosenIdx >>
                /\ UNCHANGED << mailbox, logs, decidedIdx, last_decided, 
                                proposals, promisedRnd, acceptedRnd, maxProm, 
                                buffer, read_msg, out_msg_, suffix, syncidx, 
                                idx, current_rnd, current_leader, out_msg >>

LP(self) == /\ pc[self] = "LP"
            /\ promises' = [promises EXCEPT ![self] = promises[self] \union {[accRnd |-> acceptedRnd[self], logIdx |-> Len(logs[self]), from |-> self, decIdx |-> decidedIdx[self], sfx |-> <<>>]}]
            /\ out_msg_' = [out_msg_ EXCEPT ![self] = [type |-> "PREPARE", from |-> self, n |-> currentRnd[self], accRnd |-> acceptedRnd[self], logIdx |-> Len(logs[self]), decIdx |-> decidedIdx[self]]]
            /\ \E f \in (Servers \ {self}):
                 mailbox' = [mailbox EXCEPT ![f] = Append(mailbox[f], out_msg_'[self])]
            /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
            /\ UNCHANGED << logs, decidedIdx, last_decided, proposals, 
                            promisedRnd, acceptedRnd, state, currentRnd, 
                            maxProm, accepted, chosenIdx, buffer, read_msg, 
                            suffix, syncidx, idx, current_rnd, current_leader, 
                            out_msg >>

PREPARE(self) == /\ pc[self] = "PREPARE"
                 /\ (read_msg[self].type = "PREPARE")
                 /\ IF read_msg[self].n > promisedRnd[self]
                       THEN /\ state' = [state EXCEPT ![self] = <<"FOLLOWER", "PREPARE">>]
                            /\ promisedRnd' = [promisedRnd EXCEPT ![self] = read_msg[self].n]
                            /\ IF acceptedRnd[self] >= read_msg[self].accRnd
                                  THEN /\ IF acceptedRnd[self] > read_msg[self].accRnd
                                             THEN /\ suffix' = [suffix EXCEPT ![self] = Suffix(logs[self], read_msg[self].decIdx)]
                                             ELSE /\ suffix' = [suffix EXCEPT ![self] = Suffix(logs[self], read_msg[self].logIdx)]
                                  ELSE /\ suffix' = [suffix EXCEPT ![self] = <<>>]
                            /\ out_msg_' = [out_msg_ EXCEPT ![self] = [type |-> "PROMISE", from |-> self, n |-> read_msg[self].n, accRnd |-> acceptedRnd[self], logIdx |-> Len(logs[self]), decIdx |-> decidedIdx[self], sfx |-> suffix'[self]]]
                            /\ mailbox' = [mailbox EXCEPT ![read_msg[self].from] = Append(mailbox[read_msg[self].from], out_msg_'[self])]
                       ELSE /\ TRUE
                            /\ UNCHANGED << mailbox, promisedRnd, state, 
                                            out_msg_, suffix >>
                 /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                 /\ UNCHANGED << logs, decidedIdx, last_decided, proposals, 
                                 acceptedRnd, currentRnd, promises, maxProm, 
                                 accepted, chosenIdx, buffer, read_msg, 
                                 syncidx, idx, current_rnd, current_leader, 
                                 out_msg >>

PROMISE(self) == /\ pc[self] = "PROMISE"
                 /\ (read_msg[self].type = "PROMISE")
                 /\ IF read_msg[self].n = currentRnd[self]
                       THEN /\ promises' = [promises EXCEPT ![self] = promises[self] \union {[accRnd |-> read_msg[self].accRnd, logIdx |-> read_msg[self].logIdx, from |-> read_msg[self].from, decIdx |-> read_msg[self].decIdx, sfx |-> read_msg[self].sfx]}]
                            /\ \/ /\ state[self] = <<"LEADER", "PREPARE">>
                                  /\ IF Cardinality(promises'[self]) >= MAJORITY
                                        THEN /\ maxProm' = [maxProm EXCEPT ![self] = GetMaxPromise(promises'[self])]
                                             /\ IF maxProm'[self].accRnd /= acceptedRnd[self]
                                                   THEN /\ logs' = [logs EXCEPT ![self] = Prefix(logs[self], decidedIdx[self])]
                                                   ELSE /\ TRUE
                                                        /\ logs' = logs
                                             /\ pc' = [pc EXCEPT ![self] = "P1"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                                             /\ UNCHANGED << logs, maxProm >>
                                  /\ UNCHANGED <<mailbox, out_msg_, syncidx, idx>>
                               \/ /\ state[self] = <<"LEADER", "ACCEPT">>
                                  /\ IF read_msg[self].accRnd = maxProm[self].accRnd
                                        THEN /\ syncidx' = [syncidx EXCEPT ![self] = maxProm[self].logIdx]
                                        ELSE /\ syncidx' = [syncidx EXCEPT ![self] = read_msg[self].decIdx]
                                  /\ out_msg_' = [out_msg_ EXCEPT ![self] = [type |-> "ACCEPTSYNC", from |-> self, n |-> currentRnd[self], sfx |-> Suffix(logs[self], syncidx'[self]), syncIdx |-> syncidx'[self]]]
                                  /\ mailbox' = [mailbox EXCEPT ![read_msg[self].from] = Append(mailbox[read_msg[self].from], out_msg_'[self])]
                                  /\ idx' = [idx EXCEPT ![self] = Max(chosenIdx[self], decidedIdx)]
                                  /\ IF idx'[self] > read_msg[self].decIdx
                                        THEN /\ pc' = [pc EXCEPT ![self] = "P2"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                                  /\ UNCHANGED <<logs, maxProm>>
                       ELSE /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                            /\ UNCHANGED << mailbox, logs, promises, maxProm, 
                                            out_msg_, syncidx, idx >>
                 /\ UNCHANGED << decidedIdx, last_decided, proposals, 
                                 promisedRnd, acceptedRnd, state, currentRnd, 
                                 accepted, chosenIdx, buffer, read_msg, suffix, 
                                 current_rnd, current_leader, out_msg >>

P1(self) == /\ pc[self] = "P1"
            /\ logs' = [logs EXCEPT ![self] = logs[self] \o maxProm[self].sfx \o buffer[self]]
            /\ acceptedRnd' = [acceptedRnd EXCEPT ![self] = currentRnd[self]]
            /\ accepted' = [accepted EXCEPT ![self][self] = Len(logs'[self])]
            /\ state' = [state EXCEPT ![self] = <<"LEADER", "ACCEPT">>]
            /\ buffer' = [buffer EXCEPT ![self] = <<>>]
            /\ \E p \in {[from |-> x.from, accRnd |-> x.accRnd, logIdx |-> x.logIdx, decIdx |-> x.decIdx] : x \in {y \in promises[self] : y.from /= self} }:
                 /\ IF p.accRnd = maxProm[self].accRnd
                       THEN /\ syncidx' = [syncidx EXCEPT ![self] = p.logIdx]
                       ELSE /\ syncidx' = [syncidx EXCEPT ![self] = p.decIdx]
                 /\ out_msg_' = [out_msg_ EXCEPT ![self] = [type |-> "ACCEPTSYNC", from |-> self, n |-> currentRnd[self], sfx |-> Suffix(logs'[self], syncidx'[self]), syncIdx |-> syncidx'[self]]]
                 /\ mailbox' = [mailbox EXCEPT ![p.from] = Append(mailbox[p.from], out_msg_'[self])]
            /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
            /\ UNCHANGED << decidedIdx, last_decided, proposals, promisedRnd, 
                            currentRnd, promises, maxProm, chosenIdx, read_msg, 
                            suffix, idx, current_rnd, current_leader, out_msg >>

P2(self) == /\ pc[self] = "P2"
            /\ out_msg_' = [out_msg_ EXCEPT ![self] = [type |-> "DECIDE", from |-> self, n |-> currentRnd[self], decIdx |-> idx[self]]]
            /\ mailbox' = [mailbox EXCEPT ![read_msg[self].from] = Append(mailbox[read_msg[self].from], out_msg_'[self])]
            /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
            /\ UNCHANGED << logs, decidedIdx, last_decided, proposals, 
                            promisedRnd, acceptedRnd, state, currentRnd, 
                            promises, maxProm, accepted, chosenIdx, buffer, 
                            read_msg, suffix, syncidx, idx, current_rnd, 
                            current_leader, out_msg >>

ACCEPTSYNC(self) == /\ pc[self] = "ACCEPTSYNC"
                    /\ (read_msg[self].type = "ACCEPTSYNC")
                    /\ IF read_msg[self].n = promisedRnd[self] /\ state[self] = <<"FOLLOWER", "PREPARE">>
                          THEN /\ acceptedRnd' = [acceptedRnd EXCEPT ![self] = read_msg[self].n]
                               /\ state' = [state EXCEPT ![self] = <<"FOLLOWER", "ACCEPT">>]
                               /\ logs' = [logs EXCEPT ![self] = Prefix(logs[self], read_msg[self].syncIdx)]
                               /\ pc' = [pc EXCEPT ![self] = "AS"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                               /\ UNCHANGED << logs, acceptedRnd, state >>
                    /\ UNCHANGED << mailbox, decidedIdx, last_decided, 
                                    proposals, promisedRnd, currentRnd, 
                                    promises, maxProm, accepted, chosenIdx, 
                                    buffer, read_msg, out_msg_, suffix, 
                                    syncidx, idx, current_rnd, current_leader, 
                                    out_msg >>

AS(self) == /\ pc[self] = "AS"
            /\ logs' = [logs EXCEPT ![self] = logs[self] \o read_msg[self].sfx]
            /\ out_msg_' = [out_msg_ EXCEPT ![self] = [type |-> "ACCEPTED", from |-> self, n |-> promisedRnd[self], logIdx |-> Len(logs'[self])]]
            /\ mailbox' = [mailbox EXCEPT ![read_msg[self].from] = Append(mailbox[read_msg[self].from], out_msg_'[self])]
            /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
            /\ UNCHANGED << decidedIdx, last_decided, proposals, promisedRnd, 
                            acceptedRnd, state, currentRnd, promises, maxProm, 
                            accepted, chosenIdx, buffer, read_msg, suffix, 
                            syncidx, idx, current_rnd, current_leader, out_msg >>

ACCEPT(self) == /\ pc[self] = "ACCEPT"
                /\ IF read_msg[self].n = promisedRnd[self] /\ state[self] = <<"FOLLOWER", "ACCEPT">>
                      THEN /\ logs' = [logs EXCEPT ![self] = Append(logs[self], read_msg[self].C)]
                           /\ out_msg_' = [out_msg_ EXCEPT ![self] = [type |-> "ACCEPTED", from |-> self, n |-> currentRnd[self], logIdx |-> Len(logs'[self])]]
                           /\ mailbox' = [mailbox EXCEPT ![read_msg[self].from] = Append(mailbox[read_msg[self].from], out_msg_'[self])]
                      ELSE /\ TRUE
                           /\ UNCHANGED << mailbox, logs, out_msg_ >>
                /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                /\ UNCHANGED << decidedIdx, last_decided, proposals, 
                                promisedRnd, acceptedRnd, state, currentRnd, 
                                promises, maxProm, accepted, chosenIdx, buffer, 
                                read_msg, suffix, syncidx, idx, current_rnd, 
                                current_leader, out_msg >>

ACCEPTED(self) == /\ pc[self] = "ACCEPTED"
                  /\ (read_msg[self].type = "ACCEPTED")
                  /\ IF read_msg[self].n = currentRnd[self] /\ state[self] = <<"LEADER", "ACCEPT">>
                        THEN /\ accepted' = [accepted EXCEPT ![self][read_msg[self].from] = read_msg[self].logIdx]
                             /\ IF read_msg[self].logIdx > chosenIdx[self]
                                   THEN /\ IF IsChosen(accepted'[self], read_msg[self].logIdx) = TRUE
                                              THEN /\ chosenIdx' = [chosenIdx EXCEPT ![self] = read_msg[self].logIdx]
                                                   /\ Assert((last_decided[self] = Prefix(logs[self], Len(last_decided[self]))), 
                                                             "Failure of assertion at line 43, column 9 of macro called at line 189, column 17.")
                                                   /\ decidedIdx' = [decidedIdx EXCEPT ![self] = read_msg[self].logIdx]
                                                   /\ last_decided' = [last_decided EXCEPT ![self] = Prefix(logs[self], (read_msg[self].logIdx))]
                                                   /\ out_msg_' = [out_msg_ EXCEPT ![self] = [type |-> "DECIDE", from |-> self, n |-> currentRnd[self], decIdx |-> chosenIdx'[self]]]
                                                   /\ \E p \in {x.from : x \in promises[self]} \ {self}:
                                                        mailbox' = [mailbox EXCEPT ![p] = Append(mailbox[p], out_msg_'[self])]
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED << mailbox, 
                                                                   decidedIdx, 
                                                                   last_decided, 
                                                                   chosenIdx, 
                                                                   out_msg_ >>
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << mailbox, decidedIdx, 
                                                        last_decided, 
                                                        chosenIdx, out_msg_ >>
                        ELSE /\ TRUE
                             /\ UNCHANGED << mailbox, decidedIdx, last_decided, 
                                             accepted, chosenIdx, out_msg_ >>
                  /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                  /\ UNCHANGED << logs, proposals, promisedRnd, acceptedRnd, 
                                  state, currentRnd, promises, maxProm, buffer, 
                                  read_msg, suffix, syncidx, idx, current_rnd, 
                                  current_leader, out_msg >>

DECIDE(self) == /\ pc[self] = "DECIDE"
                /\ (read_msg[self].type = "DECIDE")
                /\ IF read_msg[self].n = promisedRnd[self] /\ state[self] = <<"FOLLOWER", "ACCEPT">>
                      THEN /\ Assert((last_decided[self] = Prefix(logs[self], Len(last_decided[self]))), 
                                     "Failure of assertion at line 43, column 9 of macro called at line 192, column 17.")
                           /\ decidedIdx' = [decidedIdx EXCEPT ![self] = read_msg[self].decIdx]
                           /\ last_decided' = [last_decided EXCEPT ![self] = Prefix(logs[self], (read_msg[self].decIdx))]
                      ELSE /\ TRUE
                           /\ UNCHANGED << decidedIdx, last_decided >>
                /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                /\ UNCHANGED << mailbox, logs, proposals, promisedRnd, 
                                acceptedRnd, state, currentRnd, promises, 
                                maxProm, accepted, chosenIdx, buffer, read_msg, 
                                out_msg_, suffix, syncidx, idx, current_rnd, 
                                current_leader, out_msg >>

PROPOSE(self) == /\ pc[self] = "PROPOSE"
                 /\ (read_msg[self].type = "PROPOSE")
                 /\ \/ /\ (state[self] = <<"LEADER", "PREPARE">>)
                       /\ buffer' = [buffer EXCEPT ![self] = Append(buffer[self], (read_msg[self].C))]
                       /\ UNCHANGED <<mailbox, logs, accepted, out_msg_>>
                    \/ /\ (state[self] = <<"LEADER", "ACCEPT">>)
                       /\ logs' = [logs EXCEPT ![self] = Append(logs[self], (read_msg[self].C))]
                       /\ accepted' = [accepted EXCEPT ![self][self] = Len(logs'[self])]
                       /\ out_msg_' = [out_msg_ EXCEPT ![self] = [type |-> "ACCEPT", from |-> self, n |-> currentRnd[self], C |-> (read_msg[self].C)]]
                       /\ \E p \in {x.from : x \in { y \in promises[self] : y.from /= self} }:
                            mailbox' = [mailbox EXCEPT ![p] = Append(mailbox[p], out_msg_'[self])]
                       /\ UNCHANGED buffer
                 /\ pc' = [pc EXCEPT ![self] = "HANDLE"]
                 /\ UNCHANGED << decidedIdx, last_decided, proposals, 
                                 promisedRnd, acceptedRnd, state, currentRnd, 
                                 promises, maxProm, chosenIdx, read_msg, 
                                 suffix, syncidx, idx, current_rnd, 
                                 current_leader, out_msg >>

s(self) == HANDLE(self) \/ LEADER(self) \/ LP(self) \/ PREPARE(self)
              \/ PROMISE(self) \/ P1(self) \/ P2(self) \/ ACCEPTSYNC(self)
              \/ AS(self) \/ ACCEPT(self) \/ ACCEPTED(self) \/ DECIDE(self)
              \/ PROPOSE(self)

BLECLIENT == /\ pc[NSERVERS + 1] = "BLECLIENT"
             /\ IF proposals > 0
                   THEN /\ \/ /\ (current_rnd < MAXB)
                              /\ current_leader' = (CHOOSE x \in Servers : x /= current_leader)
                              /\ current_rnd' = current_rnd + 1
                              /\ out_msg' = [type |-> "LEADER", n |-> current_rnd', s |-> current_leader']
                              /\ \E p \in Servers:
                                   mailbox' = [mailbox EXCEPT ![p] = Append(mailbox[p], out_msg')]
                              /\ UNCHANGED proposals
                           \/ /\ (proposals > 0 /\ current_leader > 0)
                              /\ out_msg' = [type |-> "PROPOSE", C |-> proposals]
                              /\ mailbox' = [mailbox EXCEPT ![current_leader] = Append(mailbox[current_leader], out_msg')]
                              /\ proposals' = proposals - 1
                              /\ UNCHANGED <<current_rnd, current_leader>>
                        /\ pc' = [pc EXCEPT ![NSERVERS + 1] = "BLECLIENT"]
                   ELSE /\ pc' = [pc EXCEPT ![NSERVERS + 1] = "Done"]
                        /\ UNCHANGED << mailbox, proposals, current_rnd, 
                                        current_leader, out_msg >>
             /\ UNCHANGED << logs, decidedIdx, last_decided, promisedRnd, 
                             acceptedRnd, state, currentRnd, promises, maxProm, 
                             accepted, chosenIdx, buffer, read_msg, out_msg_, 
                             suffix, syncidx, idx >>

ble_client == BLECLIENT

Next == ble_client
           \/ (\E self \in Servers: s(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(s(self))
        /\ WF_vars(ble_client)

\* END TRANSLATION 

---------------------------

\* SC1. Validity: If a server decided on a log L then L only contains proposed commands.
Validity == \A pid \in Servers : decidedIdx[pid] > 0 => (\A i \in 1..Len(Prefix(logs[pid], decidedIdx[pid])) : 0 < logs[pid][i] /\ logs[pid][i] <= NPROPOSALS)

\* SC2. Uniform Agreement: For any two servers that has decided the logs L and L' respectively then one is a prefix of the other.
UniformAgreement == \A x,y \in Servers : decidedIdx[x] <= decidedIdx[y] => Prefix(logs[x], decidedIdx[x]) = Prefix(logs[y], decidedIdx[x])

\* SC3. Integrity: If a server decides on a log L and later decides on L' then L is a strict prefix of L'.
\* Is checked with asserts in the macro Decide().
==============
