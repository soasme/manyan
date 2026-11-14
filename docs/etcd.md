# etcd's trace validation

etcd's raft library logs its state transitions and checks each log
against its TLA⁺ spec with TLC (`tla/validate.sh`): the spec follows the
trace, and `TraceMatched` fails where it cannot. `make etcd-bench` logs
a trace from each of the library's interaction tests, with Go, and checks
each, and the trace etcd ships, with manyan and with TLC as `validate.sh`
runs it. Every difference in what they print is a bug.

<!-- results -->
