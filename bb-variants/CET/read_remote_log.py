import subprocess

code = """
import subprocess
try:
    out = subprocess.check_output(['tail', '-n', '25', '/content/triple_expedition.log']).decode()
    print(out)
except Exception as e:
    print('Log read error:', e)
"""
with open('/tmp/check_log.py', 'w') as f:
    f.write(code)

subprocess.call('~/.local/bin/colab exec -s triple-cet-hunt -f /tmp/check_log.py', shell=True)
