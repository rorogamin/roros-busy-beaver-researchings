import subprocess
import os
import time

log_file = open("/content/colab_hunt.log", "a")
p = subprocess.Popen(
    ["/content/hunt_all_families", "8"],
    stdout=log_file,
    stderr=subprocess.STDOUT,
    cwd="/content",
    start_new_session=True
)

time.sleep(1)
print(f"✓ Started hunter daemon on Colab VM with PID {p.pid} (setsid/detached)")
