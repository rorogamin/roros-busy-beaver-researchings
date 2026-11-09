import os, subprocess
print("tmux:", subprocess.run("which tmux", shell=True).returncode)
print("screen:", subprocess.run("which screen", shell=True).returncode)
