# etcd's trace validation

etcd's raft library logs its state transitions and checks each log
against its TLA⁺ spec with TLC (`tla/validate.sh`): the spec follows the
trace, and `TraceMatched` fails where it cannot. `make etcd-bench` logs
a trace from each of the library's interaction tests, with Go, and checks
each, and the trace etcd ships, with manyan and with TLC as `validate.sh`
runs it. Every difference in what they print is a bug.

<!-- results -->

etcd-io/raft at 99f9ffb3d19c: the traces its interaction tests log, and `tla/example.ndjson`. Measured on arm64 Darwin 25.5.0, one run, wall-clock seconds, one worker.

29 traces: manyan prints what TLC prints for 29.

| trace | events | TLC's exit | TLC | Manyan | result |
|---|---:|---|---:|---:|---|
| single_node | 14 | exit 0 | 0.53 | 0.01 | same |
| confchange_disable_validation | 35 | exit 75 | 0.55 | 0.01 | same |
| confchange_v1_add_single | 38 | exit 12 | 0.62 | 0.02 | same |
| confchange_v2_add_single_auto | 38 | exit 12 | 0.64 | 0.02 | same |
| confchange_v2_add_double_implicit | 57 | exit 12 | 0.59 | 0.01 | same |
| campaign | 54 | exit 0 | 0.76 | 0.02 | same |
| forget_leader_read_only_lease_based | 54 | exit 0 | 0.92 | 0.04 | same |
| snapshot_succeed_via_app_resp | 59 | exit 12 | 0.85 | 0.04 | same |
| heartbeat_resp_recovers_from_probing | 72 | exit 0 | 1.13 | 0.04 | same |
| snapshot_succeed_via_app_resp_behind | 75 | exit 12 | 0.98 | 0.04 | same |
| confchange_v2_add_single_explicit | 87 | exit 12 | 0.61 | 0.02 | same |
| campaign_learner_must_vote | 108 | exit 12 | 0.71 | 0.02 | same |
| lagging_commit | 107 | exit 0 | 1.07 | 0.05 | same |
| confchange_v1_remove_leader_stepdown | 119 | exit 0 | 0.86 | 0.04 | same |
| prevote | 135 | exit 12 | 1.18 | 0.05 | same |
| prevote_checkquorum | 147 | exit 12 | 1.13 | 0.05 | same |
| forget_leader_prevote_checkquorum | 147 | exit 12 | 1.08 | 0.04 | same |
| confchange_v1_remove_leader | 143 | exit 0 | 1.13 | 0.04 | same |
| checkquorum | 150 | exit 12 | 1.14 | 0.04 | same |
| confchange_v2_add_double_auto | 174 | exit 12 | 0.60 | 0.02 | same |
| replicate_pause | 167 | exit 12 | 1.39 | 0.11 | same |
| async_storage_writes | 184 | exit 0 | 1.38 | 0.09 | same |
| slow_follower_after_compaction | 183 | exit 12 | 1.52 | 0.13 | same |
| confchange_v2_replace_leader_stepdown | 194 | exit 12 | 0.95 | 0.04 | same |
| forget_leader | 201 | exit 12 | 1.05 | 0.04 | same |
| confchange_v2_replace_leader | 209 | exit 12 | 0.96 | 0.04 | same |
| async_storage_writes_append_aba_race | 239 | exit 0 | 3.75 | 0.50 | same |
| probe_and_replicate | 960 | exit 0 | 27.42 | 2.91 | same |
| example | 4888 | exit 0 | 1493.38 | 147.67 | same |
