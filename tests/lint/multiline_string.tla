---- MODULE multiline_string ----
\* Regression for #37: backslash-newline inside string literal is a lexical error in SANY.
S == "hello\
world"
====
