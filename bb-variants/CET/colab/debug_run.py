import subprocess

p = subprocess.run(["/content/hunt_all_families", "8"], capture_output=True, text=True, timeout=10)
print("Returncode:", p.returncode)
print("STDOUT:\n", p.stdout)
print("STDERR:\n", p.stderr)
