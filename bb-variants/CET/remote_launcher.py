import subprocess
import os

print("[Runner] Compiling colab_triple_expedition.c with -O3 -fopenmp -march=native...")
cmd_compile = "gcc -O3 -fopenmp -march=native /content/colab_triple_expedition.c -o /content/colab_triple_bin"
ret = subprocess.call(cmd_compile, shell=True)
if ret != 0:
    print("[Runner] Compilation FAILED!")
    sys.exit(1)

print("[Runner] Compilation SUCCESS! Launching 1-hour (3600s) triple search...")
cmd_run = "/content/colab_triple_bin 3600 > /content/triple_expedition.log 2>&1 &"
subprocess.Popen(cmd_run, shell=True)
print("[Runner] Process spawned in background! Logging to /content/triple_expedition.log")
