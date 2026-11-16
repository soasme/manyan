"""Manyan, a fast model checker for TLA+. The wheel installs the executable
itself onto the PATH; find_manyan_bin gives where."""
import os
import sys
import sysconfig


def find_manyan_bin():
    """The path of the manyan executable this package installed."""
    name = "manyan.exe" if sys.platform == "win32" else "manyan"
    schemes = [sysconfig.get_default_scheme()] if hasattr(sysconfig, "get_default_scheme") else []
    schemes.append(os.name + "_user")
    for scheme in schemes:
        path = os.path.join(sysconfig.get_path("scripts", scheme), name)
        if os.path.isfile(path):
            return path
    raise FileNotFoundError(name)
