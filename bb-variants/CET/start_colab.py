import subprocess

code = """
import os, time
os.system('tmux kill-session -t hunt 2>/dev/null; killall -9 hunt_all_families 2>/dev/null')
time.sleep(1)
os.system('tmux new-session -d -s hunt "cd /content && ./hunt_all_families 8 2>&1 | tee /content/colab_hunt.log"')
time.sleep(1)
os.system('ps aux | grep hunt_all_families')
"""

p = subprocess.run(["wsl", "bash", "-l", "-c", "colab exec -s cet-hunter"], input=code, text=True, capture_output=True)
print(p.stdout)
if p.stderr:
    print("STDERR:", p.stderr)
