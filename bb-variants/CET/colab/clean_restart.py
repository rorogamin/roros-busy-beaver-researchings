import subprocess
import os

# Kill all hunt_all_families except the one in tmux or kill all and restart cleanly
os.system("killall -9 hunt_all_families 2>/dev/null")
import time
time.sleep(1)

# Start clean single tmux session
os.system("tmux kill-session -t hunt 2>/dev/null")
os.system("tmux new-session -d -s hunt 'cd /content && ./hunt_all_families 8 2>&1 | tee -a /content/colab_hunt.log'")
time.sleep(2)
print("=== CLEAN LAUNCH STATUS ===")
os.system("ps aux | grep hunt_all_families | grep -v grep")
