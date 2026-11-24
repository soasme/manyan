---- MODULE IOUtils ----
\* The operators of CommunityModules' IOUtils that the tests use, with its
\* definitions: TLC replaces them by its Java, as Manyan by its own.
LOCAL INSTANCE Integers
LOCAL INSTANCE TLC
IOExec(command) == CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE
IOEnvExec(env, command) == CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE
IOEnv == CHOOSE r \in [STRING -> STRING] : TRUE
atoi(str) == CHOOSE i \in Int : ToString(i) = str
====
