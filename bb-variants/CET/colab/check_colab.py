import subprocess
import os

print("=== COLAB PROCESS STATUS ===")
os.system("ps aux | grep -v grep | grep hunt_all_families")

print("\n=== COLAB LOG TAIL ===")
if os.path.exists("/content/colab_hunt.log"):
    os.system("tail -n 35 /content/colab_hunt.log")
else:
    print("Log not found.")

print("\n=== CHAMPION FILES ===")
for f in ["cet3_all_champions.txt", "cet4_all_champions.txt", "cet23_all_champions.txt", "mcet3_hunt_champions.txt"]:
    path = f"/content/{f}"
    if os.path.exists(path):
        lines = open(path).readlines()
        print(f"{f}: {len(lines)} records (latest: {lines[-1].strip() if lines else 'empty'})")
    else:
        print(f"{f}: not created yet")
