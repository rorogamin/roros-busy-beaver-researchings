import subprocess
try:
    print(subprocess.check_output(['nvidia-smi']).decode())
except Exception as e:
    print("GPU check error:", e)
