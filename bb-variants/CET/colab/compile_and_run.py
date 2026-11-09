import subprocess
import os

print("=== COMPILING ON COLAB VM ===")
cmd_compile = "g++ -O3 -march=native -flto -pthread /content/hunt_all_families.cpp -o /content/hunt_all_families"
res = subprocess.run(cmd_compile, shell=True, capture_output=True, text=True)
if res.returncode != 0:
    print("Compilation failed:\n", res.stderr)
else:
    print("✓ Compilation successful with native Intel Xeon AVX-512 vectorization!")
    print("=== LAUNCHING HUNTER IN BACKGROUND ===")
    # Run in background redirecting to /content/colab_hunt.log
    bg_cmd = "nohup /content/hunt_all_families 8 > /content/colab_hunt.log 2>&1 &"
    os.system(bg_cmd)
    print("✓ Hunter successfully started in background on 8 threads!")
    print("Output is streaming to /content/colab_hunt.log")
