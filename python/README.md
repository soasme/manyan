# manyan

[Manyan](https://github.com/soasme/manyan) is a fast model checker for TLA⁺,
compatible with TLC and Apalache. It is a native executable, with no JVM.

```sh
pip install manyan
manyan -workers auto examples/DieHard
```

The wheel installs the same `manyan` a
[release](https://github.com/soasme/manyan/releases) ships, so it prints and
exits as the release does, with `-workers` too. `python -m manyan` runs it
as well, and `manyan.find_manyan_bin()` gives its path.

See [the manual](https://github.com/soasme/manyan/blob/main/docs/manual.md).
