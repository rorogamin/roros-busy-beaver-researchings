import subprocess
import os
import time

# Kill any previous hunt tmux session if exists
os.system("tmux kill-session -t hunt 2>/dev/null")

# Start new detached tmux session running the hunter and teeing to log
cmd = "tmux new-session -d -s hunt 'cd /content && ./hunt_all_families 8 2>&1 | tee /content/colab_hunt.log'"
subprocess.run(cmd, shell=True, check=True)

time.sleep(2)
out = subprocess.check_output("tmux capture-pane -pt hunt", shell=True, text=True)
print("=== TMUX HUNT SESSION STARTED ===")
print(out)
