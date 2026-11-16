"""python -m manyan runs the executable, as manyan on the PATH does."""
import os
import subprocess
import sys

from manyan import find_manyan_bin


def main():
    manyan = find_manyan_bin()
    if sys.platform == "win32":
        sys.exit(subprocess.call([manyan, *sys.argv[1:]]))
    os.execv(manyan, [manyan, *sys.argv[1:]])


if __name__ == "__main__":
    main()
