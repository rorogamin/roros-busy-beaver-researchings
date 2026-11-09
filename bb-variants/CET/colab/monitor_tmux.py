import subprocess

print("=== TMUX PANE (LIVE CONSOLE) ===")
try:
    print(subprocess.check_output("tmux capture-pane -pt hunt -S -50", shell=True, text=True))
except Exception as e:
    print("Error capturing tmux:", e)

print("=== CPU UTILIZATION (TOP) ===")
try:
    print(subprocess.check_output("top -b -n 1 | head -n 18", shell=True, text=True))
except Exception as e:
    print("Error top:", e)
