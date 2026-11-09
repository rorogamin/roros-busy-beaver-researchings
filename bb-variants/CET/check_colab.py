import subprocess

code = """
with open('/content/colab_hunt.log') as f:
    lines = [l for l in f if l.strip()]
print("=== COLAB HUNT LOG (LAST 10 PROGRESS LINES) ===")
for l in lines[-10:]:
    print(l.strip())
"""

p = subprocess.run(["wsl", "bash", "-l", "-c", "colab exec -s cet-hunter"], input=code, text=True, capture_output=True)
print(p.stdout)
if p.stderr:
    print("STDERR:", p.stderr)
